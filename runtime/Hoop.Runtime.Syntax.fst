(**
 * The syntax of a Hoop program: the AST the machines run, and the interface
 * through which handler clauses reach them.
 *
 * The runtime's architecture is that of a CEK-like abstract machine:
 *
 *   - C = Control      ... the current computation node
 *   - E = Environment  ... the evidence environment used for handler dispatch
 *   - K = Kontinuation ... a defunctionalized continuation represented
 *                          as an explicit stack of frames
 *
 * This module holds C and the frames K is built from -- `comp_tree` and
 * `frame`, which are mutually recursive and so cannot be separated. What a
 * machine *does* with them is `Hoop.Runtime.Semantics` (the specification) and
 * `Hoop.Runtime` (the implementation that ships); E belongs to the latter.
 *)
module Hoop.Runtime.Syntax

open FStar.List.Tot

(* The handler table, keyed by (eff, op). `include` rather than `open` so that a
   module opening `Hoop.Runtime.Syntax` sees `handlers`, `lookup_clause`, `keys`
   and `mk_handlers` under the names it always used them by. *)
include Hoop.Runtime.Handlers

(**
 * The `comp_tree` is the C-part of the CEK machine: the AST of the whole
 * program, the chain of `Hoop`-monadic `bind` and `pure` (`Op` and `Var`) plus
 * the effect primitives `handle`/`perform`/`resume`. It is polymorphic in the
 * type `v` of computation inputs/outputs and the type `cl` of handler clauses.
 *
 * `cl` may be understood as something like
 *   ```
 *   list v       -> (v -> comp_tree) -> comp_tree
 *   ^^^^ payloads     ^ continuation
 *  ```
 * but that function type cannot go directly in a constructor argument: doing so
 * violates the [*strictly positive rule.*](https://fstar-lang.org/tutorial/book/part2/part2_inductive_type_families.html#strictly-positive-definitions)
 *)
noeq
type comp_tree (v: Type) (cl: Type) =
  | Op:
      c:comp_tree v cl ->
      fn:(v -> comp_tree v cl) ->
      comp_tree v cl
  | Var:
      value:v ->
      comp_tree v cl
  | Perform:
      eff:string ->
      op:string ->
      payload:list v ->
      comp_tree v cl
  // **A SCOPED operation.** The same three fields as `Perform`, and that is the
  // whole of the difference: what the constructor marks is the KIND OF THE
  // OPERATION, not where its arguments live.
  //
  // A scoped operation's inner computations sit inside the opaque payload -- a
  // user-defined higher-order signature `h (Hoop inner) b`, which the runtime
  // cannot traverse without the `HFunctor` obligation this design exists to
  // remove. So the clause destructures the payload itself and applies the
  // supplied `weave` capability to whichever computation it selects; F* never
  // sees those computations, and `Hoop.Runtime.WellScopedness.apply_scoped_ok`
  // is where that is paid for. See the scoped-effects design note, Decision 3.
  //
  // *Why a constructor and not a field on `Perform`.* A field would be read at
  // 94 sites against a constructor's 22, and -- the reason that matters -- it
  // would put the scoped case inside the statement of `perform_algebraic`, which
  // does not mention it as things stand. Decision 6.
  | PerformS:
      eff:string ->
      op:string ->
      payload:list v ->
      comp_tree v cl
  | Handle:
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      body:comp_tree v cl ->
      comp_tree v cl
  // `Splice` node is machine-internal and should never be exported to the PS-world;
  // it is inserted by the machine at the head of a delimited continuation when the
  // continuation is loaded as the next instruction — the result of firing `continue k`
  // in a handler clause.
  //
  // It says: *push these frames, then run this body under them*. The frames are a
  // captured stack segment and the body is what the machine is to run once they are
  // back in place. The two parts are independent: the segment says WHERE control is
  // to resume, the body says WITH WHAT.
  //
  // Splitting them apart is what leaves room for a scoped operation, whose body is a
  // computation rather than a value; resumption, the only use today, is the special
  // case where the body is already a value. See `resumed` below.
  | Splice:
      frames: list (frame v cl) ->
      body: comp_tree v cl ->
      comp_tree v cl
  // **Running a computation under a borrowed context.** Machine-internal, like
  // `Splice`, and never exported to the PS-world: it is what applying a scoped
  // clause's `weave` capability produces, and stepping it is where the borrow is
  // either taken or refused.
  //
  // Two things distinguish it from `Splice`, and both are deliberate.
  //
  //   - **The EXECUTION-RELEVANT segment it carries is NORMALIZED**, never a raw
  //     captured one. The two sides of a monad law differ by the extra `BindF`
  //     frames of the law's redex block; `Hoop.Runtime.Semantics.prepare_captured`
  //     erases exactly that difference, so both sides build the SAME node -- same
  //     origin, same segment, same borrowability verdict, same weave function. A
  //     raw segment stored here would not, and the resume-only congruence the laws
  //     are proved under would no longer suffice. See Decision 7.
  //
  //   - **Stepping it CHECKS borrowability**, whereas splicing checks nothing.
  //     The check belongs here rather than at the dispatch of the scoped
  //     operation because a scoped clause is entitled to discard an inner
  //     computation -- `once` prunes, `catch` does not take the branch it did
  //     not choose -- and a non-borrowable prompt in a context that is never
  //     woven is no reason to refuse anything. Decision 5.
  //
  // **The node also remembers WHERE IT CAME FROM.** `origin_eff` and `origin_op`
  // name the scoped operation whose dispatch built it. Normalization is a
  // condition on the execution-relevant stack component and was never a reason
  // to discard diagnostic provenance -- and a node that may be evaluated
  // arbitrarily far from its dispatch, by a clause free to run a woven
  // computation later or not at all, is precisely the node that has to carry its
  // own origin. It is what `UnborrowableScope` reports, and it costs two fields
  // on a node that is already allocated. Nothing in the semantics reads it: the
  // borrowability verdict and the transition are functions of `prepared` alone.
  //
  // Well-scopedness of the node carries NO borrowability condition: a `Weave`
  // that is going to be rejected is still well scoped, since it fires no action
  // it lacks the capability for. That is what keeps
  // `Hoop.Runtime.WellScopedness.weave_ok` dischargeable unconditionally. The
  // origin is invisible to it too.
  | Weave:
      origin_eff: string ->
      origin_op: string ->
      prepared: list (frame v cl) ->
      body: comp_tree v cl ->
      comp_tree v cl
  // Prompt-local state. `NewP` installs a cell for the duration of `body`;
  // `ReadP` and `WriteP` reach the nearest enclosing cell of that label. The
  // label is the runtime representation of the opaque carrier the PureScript
  // surface hands out, and it names a *binder*, not a location: the cell lives
  // in the `ParamF` frame below, by value, so a captured continuation carries
  // its own copy.
  | NewP:
      label: string ->
      init: v ->
      body: comp_tree v cl ->
      comp_tree v cl
  | ReadP:
      label: string ->
      comp_tree v cl
  | WriteP:
      label: string ->
      value: v ->
      comp_tree v cl

(**
 * A `frame` is the K-part　of the CEK machine and represents a defunctionalized continuation.
 * Basically, it is the right-hand side of a monadic `>>=` chain (making it literally a continuation).
 * Once the program performs an action, control flow jumps to the corresponding handler.
 * Prompts serve as landmarks for the machine to find the appropriate handlers to process the action.
 *)
and frame (v: Type) (cl: Type) =
  | BindF:
      fn:(v -> comp_tree v cl) ->
      frame v cl
  // A prompt-local cell, held IN THE FRAME, BY VALUE. There is no mutable cell,
  // no pointer and no identity: a write rebuilds the frame, so a captured
  // continuation carries the value it was captured with. Which is what makes
  // the composition order of two handlers observable, exactly as in Koka.
  | ParamF:
      label:string ->
      value:v ->
      frame v cl
  | PromptF:
      hs:handlers cl ->
      pure:option (v -> comp_tree v cl) ->
      frame v cl

(**
 * **Resumption is the `Var` specialisation of `Splice`.** Handing a value `x` to a
 * captured continuation `fs` is splicing `fs` back on with nothing left to compute
 * but `x` itself.
 *
 * It is kept under its own name because that name is the one the metatheory argues
 * about: `Hoop.Runtime.Semantics.kont_of` builds exactly this, `apply_ok` constrains
 * exactly this, and every theorem about resumption is stated of it. Making it
 * `unfold` rather than a `val` is deliberate — `step`'s `Splice` rule then applies to
 * it *definitionally*, so the old transition survives as a tautology rather than as a
 * lemma with a proof that could rot (see `Hoop.Runtime.Metatheory.step_resumed`).
 *)
unfold
let resumed (#v #cl: Type) (fs: list (frame v cl)) (x: v) : comp_tree v cl
  = Splice fs (Var x)

// The clause-monomorphized version of `apply`. This calls a handler clause by feeding
// it the action's payload (`list v`) and the captured delimited continuation.
// Because clauses are closures passed from the PureScript world via the FFI, F* can
// guarantee nothing about the invariants enforced by the PS type system. Therefore,
// we abstract the clause away as a parameter `cl` and specify its invariant
// via `Hoop.Runtime.WellScopedness.apply_ok`.
let apply_t (v cl : Type) = cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl

(**
 * **The same, for a scoped clause**: one argument more, and it is the whole
 * point of the type.
 *
 * `weave : comp_tree v cl -> comp_tree v cl` is the capability the machine hands
 * over -- "run this inner computation under the handlers my perform site could
 * see". On the PureScript side it is rank-2 (`forall x. Hoop inner x -> Hoop r
 * (f x)`), which is what makes "you may only run an inner computation through
 * `weave`" a type error rather than a convention; here it is a plain arrow,
 * because F* has a single value type and there is nothing left of the
 * quantifier to see.
 *
 * `apply_t` is UNCHANGED and stays the interpreter of ordinary clauses. Keeping
 * the two apart is what keeps `Hoop.Runtime.WellScopedness.apply_ok` -- an
 * assumption about every program, including those that use no scoped operation
 * at all -- from being conditioned on a clause kind.
 *)
let scoped_apply_t (v cl : Type) =
  cl -> list v -> (comp_tree v cl -> comp_tree v cl) -> (v -> comp_tree v cl) -> comp_tree v cl
