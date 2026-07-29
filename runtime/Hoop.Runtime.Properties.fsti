module Hoop.Runtime.Properties

open Hoop.Runtime
open FStar.List.Tot

let find_prompt_t
    (v:Type)
    (cl:Type)
  = eff: string ->
    op: string ->
    k: stack v cl ->
    GTot (option (stack v cl & cl & stack v cl))

(**
 * **The preservation of stack**: appending the captured and the rest of stack
 * reproduces original one, i.e. `cap @ below == k`
 *
 * This lemma ensures the `find_prompt` indeed *splits* the stack;
 * no dropping, adding or moving any frame.
 *)
let find_prompt_partitions_correctness
    (#v #cl: Type)
    (find_prompt: find_prompt_t v cl)
    (eff op: string)
    (k: stack v cl)
  : prop
  = Some? (find_prompt eff op k) ==>
      (let Some (cap, _, below) = find_prompt eff op k in
          cap @ below == k
      )
val find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures find_prompt_partitions_correctness (find_prompt #v #cl) eff op k)
(**
 * **Captured segments end with the prompt inclusive**:
 * The captured segments are non-empty, and their *final* element is precisely
 * the `PromptF` frame which holds the selected operation clause.
 *
 * This serves as the foundation for **deep handler semantics**. The behavior upon resumption
 * diverges depending on whether the capture cuts *before* the prompt (shallow)
 * or *includes* the prompt itself (deep):
 *   - Under shallow semantics, the resumed continuation is no longer under that handler's scope.
 *   - Under deep semantics, the handler is re-installed upon resumption, allowing the continuation
 *     to perform the same effect again inside it.
 * Hoop adopts the deep semantics approach, and this lemma solidifies this design choice
 * on the F* side.
 *
 * At the same time, this property asserts that "the returned clause is exactly the one looked up
 * from the handler table of the trailing prompt in the captured segment"
 * (`lookup_clause hs eff op == Some c`). It formalizes the guarantee that the clause
 * does not mismatch with the prompt that re-installs it.
 *)
let find_prompt_last_correctness
    (#v #cl : Type)
    (find_prompt: find_prompt_t v cl)
    (eff op : string)
    (k : stack v cl)
  : prop
  = Some? (find_prompt eff op k) ==>
      (let Some (cap, c, _) = find_prompt eff op k in
          (Cons? cap /\
            ( match last cap with
              | PromptF hs _ -> lookup_clause hs eff op == Some c
              | BindF _ -> False
            )
          )
      )
val find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_last_correctness (find_prompt #v #cl) eff op k))
(**
 * **Innermost lemma**:
 * No frame in the captured segment before the tail (the handler's own prompt)
 * handles the given (eff, op).
 *
 * This underpins the scoping mechanics of effect handlers. A `perform` must resolve to
 * the innermost capable handler. This lemma ensures that no handling prompt is hidden
 * inside the cut segment; in other words, *no handler is ever bypassed*.
 *
 * Why this matters to the runtime:
 *   This property guarantees proper shadowing when handlers for the same effect are nested.
 *   If this invariant breaks, scope leakage occurs—for instance, an operation might bypass
 *   an inner `Reader` and incorrectly reach an outer one.
 *
 * Note that this statement applies specifically to `init cap` (the captured segment minus the tail).
 * The tail prompt itself is omitted because it is the actual handler. Its existence (`Cons? cap`)
 * is guaranteed by `find_prompt_last` (in the proof, the properties of `last` are extracted
 * before driving the induction).
 *)
let find_prompt_innermost_correctness
    (#v #cl: Type)
    (find_prompt: find_prompt_t v cl)
    (eff op: string)
    (k: stack v cl)
  : prop
  = (Some? (find_prompt eff op k)) ==>
      (let Some (cap, _, _) = find_prompt eff op k in
        (Cons? cap) /\
          forall (f: frame v cl).
            memP f (init cap) ==> not (handles eff op f)
          )
val find_prompt_innermost
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_innermost_correctness (find_prompt #v #cl) eff op k))
(**
 * **Characterization of Stuck**:
 * `find_prompt` returns `None` if and only if no frame on the stack handles the given (eff, op).
 *
 * Both directions of `<==>` are meaningful:
 *   - (==>) If the search fails, there truly was no handler available.
 *     Since `step` returns `Stuck eff op` upon receiving `None`, this guarantees
 *     "no false positives for Stuck"—meaning the runtime will never accidentally
 *     throw an unhandled exception when a valid handler actually exists.
 *   - (<==) If at least one handler exists, the search is guaranteed to return `Some`.
 *     This ensures no handler is ever missed or overlooked, preventing accidental Stuck states.
 *
 * This property provides type-theoretic backing for the claim that "Stuck never occurs
 * as long as the runtime is sound" (as noted in the comments for `Stuck` in Hoop.Runtime.fst).
 * In other words, to prove the absence of a Stuck state, the problem can be reduced
 * simply to showing that a valid handler resides on the stack.
 *)
let find_prompt_none_correctness
    (#v #cl : Type)
    (find_prompt: find_prompt_t v cl)
    (eff op : string)
    (k: stack v cl)
  : prop
  = None? (find_prompt eff op k) <==>
      (forall (f: frame v cl). memP f k ==> not (handles eff op f))
val find_prompt_none
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures
        find_prompt_none_correctness (find_prompt #v #cl) eff op k)

// -------------------------------------- //

(**
 * The soundness of `lookup_clause`:
 * If `lookup_clause hs eff op` returns `Some c`, then the triple `(eff, op, clause)`
 * should indeed be an element of the handlers table `hs`.
 * In other words, `lookup_clause` never forges the handler clause.
 *
 * Together with `find_prompt_last`, ensures that:
 * the returned clause is indeed a member of handlers installed by the prompt at the bottom of
 * the captured continuation.
 *)
let lookup_clause_soundness
    (#cl : Type)
    (hs: handlers cl)
    (eff op : string)
  : prop
  = Some? (lookup_clause hs eff op) ==>
      (let Some c = lookup_clause hs eff op
      in memP (eff, op, c) hs)

val lookup_clause_memP
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures (lookup_clause_soundness hs eff op))

(**
 * **The completeness of `lookup_clause`**:
 * if `lookup_clause` returns `None` then the handlers table never has
 * an entry identified as `(eff, op)`
 *
 * This is the frame-layer equivalent of `find_prompt_none`. It guarantees that
 * if a prompt's `handles` check returns `false`, it is because the prompt truly lacks
 * that effect, not because the search somehow missed it. Only with this completeness
 * can the innermost property (`find_prompt_innermost`) validly claim that
 * *no handler is ever bypassed*.
 *)
let lookup_clause_completeness
    (#cl : Type)
    (hs : handlers cl)
    (eff op : string)
  : prop
  = None? (lookup_clause hs eff op) ==>
      forall (c: cl). ~(memP (eff, op, c) hs)

val lookup_clause_none
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures lookup_clause_completeness hs eff op)

//------------------------//

(** The soundness of step on perform *)
val step_perform
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
          (let Some (captured, clause, below) = find_prompt eff op k in
              // 1. The next computation is the handler clause fed with the payload of the action
              // and with the delimited continuation and the machine keeps running on `below`.
              (step apply (Step (Perform eff op payload) k) ==
                  Step (apply clause payload (fun x -> Resumed captured x)) below) /\
              // 2. Stack is preserved
              captured @ below == k))

(**
 * **Characterization of Stuck at the level of `step`**:
 * the machine gets stuck on `Perform eff op payload` if and only if no frame of the stack
 * handles the given (eff, op). This carries `find_prompt_none` over from the search function
 * to the transition function itself.
 *
 * Both directions of `<==>` are meaningful:
 *   - (<==) `Stuck ==> ~(handled_in eff op k)`: if the machine returned `Stuck`, then the
 *     stack truly held no frame capable of handling that action, i.e. **there are no false
 *     positives for Stuck**. Seen from the PureScript user's side, this rules out the worst
 *     conceivable behavior—being told *Unhandled effect operation* even though the handler
 *     had been installed correctly. In practice this is the more important direction.
 *   - (==>) `~(handled_in eff op k) ==> Stuck`: if not a single frame can handle the action,
 *     the machine does get stuck, i.e. **nothing slips through**. An unhandled operation is
 *     never silently let past.
 *
 * Why this matters to the runtime:
 *   Read contrapositively, the lemma says that as soon as one capable handler sits anywhere
 *   on the stack, `step` does not return `Stuck`. That is the entry point for a future
 *   *progress* theorem, stating that a well-formed machine never wedges.
 *)
val step_perform_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply (Step (Perform eff op payload) k) == Stuck eff op)

(**
 *
 * Although this corollary is almost self-evident, it remains valuable to establish.
 * This is because, combined with the `find_prompt_last` lemma, it guarantees that
 * the prompt selected on perform is contained within the captured stack segment and
 * reinstalled on resume, which amounts to nothing less than deep handler semantics.
 *)
val step_resumed
    (#v #cl : Type)
    (apply: apply_t v cl)
    (comp : comp_tree v cl { Resumed? comp })
    (cc : stack v cl)
  : Lemma
      (step apply (Step comp cc) ==
        Step (Var (Resumed?.value comp)) ((Resumed?.frames comp) @ cc))

(**
 * When the continuation captured by `perform` is resumed on top of `below` (left by `step_perform`), 
 * the stack is perfectly restored to `k`. Because the next computation transitions to `Var x`, 
 * it becomes identical to the state where the value `x` has just been returned directly after the `perform`.
 *
 * Effectively, when paired with `step_perform`, we can state:
 *
 *   Step (Perform eff op payload) k
 *     --step-->  Step (apply clause payload (fun x -> Resumed captured x)) below
 *                (The clause triggers `continue k x`)
 *     --step-->  Step (Var x) k          (* Back to the original stack *)
 *
 * This directly establishes the formal definition of "capture and resumption canceling each other out."
 *)
val capture_resume_roundtrip
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
    (x: v)
    (apply: apply_t v cl)
  : Lemma
      (requires (handled_in eff op k))
      (ensures
          (let Some (captured, _, below) = find_prompt eff op k in
            step apply (Step (Resumed captured x) below) == Step (Var x) k))

(**
 * **The Op transition**: the left-hand side of a monadic bind is evaluated first, with
 * a `BindF` frame pushed to hold the rest. `Op c fn` is the tree shape of `c >>= fn`,
 * and the transition reads: run `c`, having set *what to do afterwards* aside on the
 * stack.
 *
 * This is defunctionalization proper. The continuation `fn` is neither applied nor kept
 * in a closure of the machine; it is parked as an explicit frame. That is exactly what
 * later allows `find_prompt` to slice the continuation apart and hand one segment of it
 * to a handler clause—an operation that would be impossible if the continuation were an
 * opaque function.
 *)
val step_op
    (#v #cl: Type)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Op c fn) k) == Step c (BindF fn :: k))

(**
 * **The Handle transition**: entering `Handle hs ret body` pushes a `PromptF hs ret`
 * frame and continues with `body`. The handler table and the return clause are carried
 * by that frame, so nothing about a handler ever lives outside the stack.
 *
 * The frame is what delimits the handler's scope: whatever the machine pushes while
 * running `body` sits *inside* the scope, and whatever was already there sits outside.
 * All later traffic in prompts keys on this one landmark—`step_perform` locates its
 * handler by scanning for it (`find_prompt`) and cuts the captured segment at it,
 * `step_var_prompt` pops it when a value reaches it, and `Resumed` puts it back on
 * resumption, which is what makes the semantics deep.
 *)
val step_handle
    (#v #cl: Type)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Handle hs ret body) k) == Step body (PromptF hs ret :: k))

(**
 * **Reaching a value with an empty stack ends the run**: there is nothing left to do
 * with the value, so the machine halts on `Done`. This is the sole way a `Done` state
 * is ever produced.
 *)
val step_var_done
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
  : Lemma (step apply (Step (Var value) ([] <: stack v cl)) == Done value)

(**
 * **A value meeting a `BindF` frame feeds the saved continuation**: the frame parked by
 * `step_op` is popped and applied to the value. This is the monad law
 * `pure v >>= f == f v`, realized as a single transition of the machine, and it is the
 * counterpart of `step_op`: what one transition sets aside, the other picks back up.
 *)
val step_var_bind
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (BindF fn :: rest)) == Step (fn value) rest)

(**
 * **A value reaching a prompt leaves the handler's scope**: the handled body ran to
 * completion without ever firing an operation this prompt is responsible for, so the
 * prompt has nothing left to do. It is discarded, and the return clause is applied to
 * the value. With no return clause the transition is the identity on the value: it
 * simply passes through, on the stack the prompt used to sit on.
 *
 * This is the counterpart of `(frame.args.pure ?? Pure)(val)` in the TypeScript runtime.
 *
 * Why this matters to the runtime:
 *   This is the *only* place in the whole of `step` where a return clause is ever
 *   applied, and the prompt carrying it is consumed by the very same transition, so it
 *   cannot be reached a second time through that frame. That is the ground on which the
 *   theorem still ahead—*the return clause runs exactly once, and last*—will rest:
 *   *once*, because the prompt is spent here; *last*, because arriving at this frame
 *   means the handled body, together with everything that had been pushed on top of the
 *   prompt, has already been reduced to a value.
 *)
val step_var_prompt
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (step apply (Step (Var value) (PromptF hs ret :: rest)) ==
        (match ret with
          | Some r -> Step (r value) rest
          | None -> Step (Var value) rest))

(**
 * **A handler without a return clause is transparent to values**: the `None` case of
 * `step_var_prompt`, singled out. The prompt is dropped and the value carries on
 * unchanged over the remaining stack.
 *
 * Read at the level of types, this says such a handler does not alter the answer type:
 * it may install operations, but it cannot reinterpret the result of the block it
 * delimits.
 *)
val step_var_prompt_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (PromptF hs None :: rest)) == Step (Var value) rest)

(**
 * **Installing a handler makes its operations handled**: once a `PromptF hs ret` frame
 * has been pushed, every (eff, op) listed in `hs` satisfies `handled_in` on the
 * resulting stack, whatever the frames underneath happen to be.
 *
 * Why this matters to the runtime:
 *   Paired with the contrapositive of `step_perform_stuck`—a stack that handles the
 *   action does not lead to `Stuck`—this yields the statement one actually wants about
 *   `Handle`: *performing, from within the body of a `Handle`, an operation its table
 *   declares can never wedge the machine.* That is the first genuine component of a
 *   *progress* theorem. What is still missing is that the prompt survives while the body
 *   runs, and that is what `handled_in_cons` supplies.
 *)
val handle_installs
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures handled_in eff op (PromptF hs ret :: k))

(**
 * **Monotonicity of `handled_in` under pushing**: a handler already present on the stack
 * is not lost when a further frame is pushed on top of it.
 *
 * Why this matters to the runtime:
 *   The two structural transitions of the machine both work by pushing—`BindF` in
 *   `step_op`, `PromptF` in `step_handle`. This lemma says neither of them can break a
 *   scope: descending into the left-hand side of a bind, or into the body of an inner
 *   `Handle`, never takes an outer handler out of reach. Together with `handle_installs`
 *   it is what carries *the handler is still in place* along a run, and that is precisely
 *   the induction step a progress theorem needs.
 *)
val handled_in_cons
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
    (k: stack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures handled_in eff op (f :: k))

//------------------------//

(**
 * **Terminal states are fixpoints**: once the machine has reached `Done` or `Stuck`,
 * running it for any further number of transitions changes nothing.
 *
 * This is the multi-step counterpart of the two absorbing branches of `step`, and it is
 * what makes `fuel` semantically inert: an answer obtained with a given amount of fuel is
 * not disturbed by feeding in more.
 *
 * Its immediate use is proof-technical. Every induction over the length of a run splits
 * on the shape of the current state, and this lemma is what discharges the terminal
 * branches—`steps_add` is proved exactly this way. Without it the two sides of an
 * interval decomposition cannot be shown to agree once the machine has already halted
 * inside the first interval.
 *)
val steps_terminal
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s)
      (ensures steps apply n s == s)

(**
 * **Additivity of multi-step execution**: running for `n` transitions and then for `m`
 * more is running for `n + m` transitions. Equivalently, a run may be cut at any point
 * and the two halves reasoned about separately.
 *
 * This is the pivotal lemma of this group: it is the glue with which a property spanning
 * several transitions is assembled out of properties of shorter stretches. Without it,
 * multi-step statements cannot even be *phrased* compositionally—one would be forced to
 * unfold a fixed number of transitions by hand, which is impossible as soon as the length
 * of a stretch is not known in advance.
 *
 * Why this matters to the runtime:
 *   `step_perform` and `capture_resume_roundtrip` currently sit side by side as two
 *   isolated single-transition facts. To fuse them into the single proposition one
 *   actually wants—*performing an operation and coming back into the continuation takes
 *   N transitions, and lands on the original stack*—one has to account for what happens
 *   in between, namely the execution of the clause body returned by `apply`. That body is
 *   an arbitrary computation of unknown length. The run therefore has to be split into
 *   *one transition (the perform) + j transitions (the clause body) + one transition (the
 *   resume)*, and it is this lemma that welds the three intervals back together.
 *
 * The same shape is needed for the theorems still ahead: that a handler's return clause
 * is applied exactly once and at the very end; that a `Handle` node's prompt survives
 * from its installation until its removal; and, eventually, an adequacy theorem relating
 * the machine to a denotational semantics, whose proof is an induction that repeatedly
 * concatenates sub-runs.
 *)
val steps_add
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (ensures steps apply (n + m) s == steps apply m (steps apply n s))

(**
 * **Stability of the answer**: once a run has produced a `Done`, adding fuel never
 * changes it. A corollary of `steps_add` and `steps_terminal`.
 *
 * The point is that the result of the machine does not depend on how much fuel it was
 * given, as long as it was given enough. This is what justifies the habit—in the tests
 * and in specifications alike—of passing a comfortably large constant and reading off the
 * result: the value observed is the value the machine converges to, not an artifact of
 * the bound. It also means a specification may quantify existentially over the fuel
 * (*there is some n for which the machine is `Done`*) without the choice of witness
 * mattering.
 *)
val steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply n s))
      (ensures steps apply (n + m) s == steps apply n s)

// ------------------------------------------------------------------ //
//  Well-scopedness: the defining equations                            //
// ------------------------------------------------------------------ //

(**
 * `Hoop.Runtime.ws` is defined by recursion on a step index rather than on the
 * computation tree, for the reason spelled out where it is defined: the return
 * clause of `Handle` is an `option (v -> comp_tree v cl)`, and F* has no subterm
 * axiom reaching under it, so the structural definition one would like to write
 * cannot be shown to terminate.
 *
 * The eight lemmas of this section are what makes that a matter of bookkeeping
 * rather than of substance. Each is an `<==>`, and together they are exactly the
 * clauses of the structural definition: `ws` at a `Var` holds, `ws` at a
 * `Perform` is availability of the action, `ws` at an `Op` is `ws` of both parts,
 * and so on. Nothing in the development below ever unfolds `ws_n`; it works
 * through these equations alone. In that sense `ws` *is* the naive definition,
 * and the step index never appears in a statement anyone reads.
 *
 * They are also the reason `ws` may be treated as abstract: this interface
 * mentions neither `ws_n` nor `wf_stack_n`, so a client reasons about `ws` only
 * through the equations, the congruence lemmas, and the theorems below.
 *)

(** **A value is well scoped anywhere**: it fires nothing. *)
val ws_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (x: v)
  : Lemma (ws cok a (Var x <: comp_tree v cl))

(**
 * **A `Perform` is well scoped exactly when its action is available**. This is
 * the only clause of `ws` that can fail, and hence the entire content of the
 * predicate: everything else merely propagates it through the tree.
 *)
val ws_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (eff op: string)
    (payload: list v)
  : Lemma (ws cok a (Perform eff op payload <: comp_tree v cl) <==> a eff op == true)

(**
 * **`Op` distributes**: `c >>= fn` is well scoped exactly when `c` is and every
 * branch of `fn` is. The environment does not change across a bind — a bind
 * installs no handler.
 *)
val ws_op
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
  : Lemma (ws cok a (Op c fn) <==> (ws cok a c /\ (forall (x: v). ws cok a (fn x))))

(**
 * **`Handle` extends the environment for its body only**: the body may use
 * whatever the table declares, on top of what was already in scope, whereas the
 * clauses and the return clause run *outside* the prompt they belong to and so
 * see only `a`.
 *
 * That asymmetry is not an accident of the definition, it is the scoping rule of
 * the language. A clause is invoked after `step` has cut the stack at its own
 * prompt and thrown that prompt away for the duration; a return clause is
 * invoked by `step_var_prompt`, which pops the prompt first. Neither can rely on
 * its own handler being installed, and `ws` says so.
 *)
val ws_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
  : Lemma
      (ws cok a (Handle hs ret body) <==>
        (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret))

(**
 * **A `Resumed` node is well scoped exactly when the continuation it carries is
 * well formed**. The node holds no computation of its own; it is the machine's
 * way of splicing a captured stack segment back on, so its obligation is that of
 * a stack.
 *)
val ws_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (x: v)
  : Lemma (ws cok a (Resumed frames x) <==> wf_stack cok a frames)

(** **The empty stack is well formed**: it suspends nothing. *)
val wf_stack_nil
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
  : Lemma (wf_stack cok a ([] <: stack v cl))

(**
 * **A `BindF` frame contributes nothing to the environment**: the suspended
 * continuation is judged in the environment of the frames below it, unchanged.
 *)
val wf_stack_bind
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (BindF fn :: rest) <==>
        ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest))

(**
 * **A `PromptF` frame owes for its table and its return clause**, both judged
 * *below* the prompt — the same rule as `ws_handle`, which is what makes the two
 * agree when `step_handle` turns one into the other.
 *)
val wf_stack_prompt
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (PromptF hs ret :: rest) <==>
        (handler_ok cok (can_in_with rest a) hs /\
         ret_ws cok (can_in_with rest a) ret /\
         wf_stack cok a rest))

// ------------------------------------------------------------------ //
//  Congruence in the environment                                      //
// ------------------------------------------------------------------ //

(**
 * **Well-scopedness only sees which actions an environment offers**, not how the
 * environment was built.
 *
 * Availability environments are functions, so the ones the machine computes are
 * equal pointwise but almost never syntactically: pushing a `BindF` frame yields
 * `can_in (BindF fn :: k)`, a different closure from `can_in k` although it offers
 * exactly the same actions. Every preservation proof below therefore ends with a
 * congruence step, and these lemmas are it. The hypothesis `clause_ok_congr cok` is
 * inherited by `handler_ok` and propagated through the whole predicate.
 *)
val clauses_ok_cong
    (#cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (hs: handlers cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures handler_ok cok a1 hs <==> handler_ok cok a2 hs)

val ws_cong
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures ws cok a1 c <==> ws cok a2 c)

val wf_stack_cong
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures wf_stack cok a1 k <==> wf_stack cok a2 k)

// ------------------------------------------------------------------ //
//  How the environment reacts to the stack surgery `step` performs    //
// ------------------------------------------------------------------ //

(** **Pushing a `BindF` frame changes nothing**: a bind installs no handler.
    This is the environment-level reading of `step_op`. *)
val av_bind
    (#v #cl: Type)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (BindF fn :: k) a) (can_in_with k a))

(** **Pushing a `PromptF` frame extends the environment by its table**, which is
    the environment-level reading of `step_handle`, and matches to the letter the
    extension `ws_handle` grants the body of the corresponding `Handle`. That the
    two agree is what carries well-scopedness across that transition. *)
val av_prompt
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (PromptF hs ret :: k) a) (extend hs (can_in_with k a)))

(** **Concatenation of stacks composes environments**: running on `k1` stacked on
    `k2` offers what `k1` offers on top of what `k2` does. Needed for the
    `Resumed` transition, which splices a captured segment back on. *)
val av_append
    (#v #cl: Type)
    (k1 k2: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (k1 @ k2) a) (can_in_with k1 (can_in_with k2 a)))

// ------------------------------------------------------------------ //
//  Splitting and joining a well-formed stack                          //
// ------------------------------------------------------------------ //

(**
 * **Well-formedness is compositional along `@`**: a concatenated stack is well
 * formed exactly when the lower part is, and the upper part is well formed in
 * the environment the lower part offers.
 *
 * This is the workhorse of the two transitions that take a stack apart or put
 * one back together — `Perform`, which cuts at a prompt, and `Resumed`, which
 * splices the cut segment back on. Read left to right it justifies the cut; read
 * right to left, the splice.
 *)
val wf_stack_append
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (k1 k2: stack v cl)
    (a: can_perform)
  : Lemma
      (requires clause_ok_congr cok)
      (ensures wf_stack cok a (k1 @ k2) <==> (wf_stack cok (can_in_with k2 a) k1 /\ wf_stack cok a k2))

(**
 * **The clause table of a prompt buried in a well-formed stack is well scoped
 * below that prompt**. Combined with `find_prompt_last` — which says the prompt
 * `step` selects really does hold the clause it hands to `apply` — this is what
 * supplies the `cok (can_in below) clause` premise that `apply_ok` demands.
 *)
val wf_stack_split_prompt
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (k1: stack v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k2: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_stack cok a (k1 @ (PromptF hs ret :: k2)))
      (ensures handler_ok cok (can_in_with k2 a) hs)

// ------------------------------------------------------------------ //
//  Preservation of the machine invariant, one transition at a time    //
// ------------------------------------------------------------------ //

(**
 * The five lemmas that follow are the five branches of `step`, each shown to
 * take a well-formed state to a well-formed state. They are stated separately
 * rather than inlined into `step_preserves_wf` because they are of very
 * different weights — `pres_var` is immediate, `pres_perform` is the whole
 * argument — and keeping them apart keeps each SMT query small.
 *)

(** **Op**: descending into the left of a bind, with the rest parked on the
    stack. The pushed frame changes no environment, so both halves of `ws_op`
    land where they must. *)
val pres_op
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (inner: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Op inner fn) k))
      (ensures wf_state cok (step apply (Step (Op inner fn) k)))

(** **Handle**: the extension `ws_handle` grants the body is exactly the one
    `av_prompt` says the pushed frame provides. *)
val pres_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Handle hs ret body) k))
      (ensures wf_state cok (step apply (Step (Handle hs ret body) k)))

(** **Var**: a value meets the top frame. Whichever frame it is, its obligation
    was recorded against the environment of the frames below, which is precisely
    the environment the machine now runs in. *)
val pres_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires wf_state cok (Step (Var value <: comp_tree v cl) k))
      (ensures wf_state cok (step apply (Step (Var value <: comp_tree v cl) k)))

(** **Resumed**: the captured segment is spliced back on. Well-formedness of the
    join follows from `wf_stack_append`, the environments matching by `av_append`. *)
val pres_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (captured: stack v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Resumed captured value) k))
      (ensures wf_state cok (step apply (Step (Resumed captured value) k)))

(**
 * **Perform**: the interesting one, and the only branch that could get stuck.
 *
 * Well-scopedness of the `Perform` says the action is available on `k`, which by
 * definition of `can_in` means `find_prompt` succeeds — so the `Stuck` branch is
 * already out. What remains is that the state the machine moves to is well
 * formed, and that is assembled from three facts proved elsewhere: the stack
 * splits as `captured @ below` (`find_prompt_partitions`); the prompt owning the
 * clause is the last frame of `captured` (`find_prompt_last`), whence
 * `wf_stack_split_prompt` gives `cok (can_in below) clause`; and the captured segment,
 * being well formed over `below`, makes `fun x -> Resumed captured x` a well
 * scoped continuation there (`ws_resumed`). `apply_ok` then delivers the clause
 * body, well scoped in `can_in below`, which is where the machine continues.
 *)
val pres_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\
                wf_state cok (Step (Perform eff op payload) k))
      (ensures wf_state cok (step apply (Step (Perform eff op payload) k)))

(**
 * **Preservation**: one transition of a well-formed machine leaves it well
 * formed. The five branches above, assembled.
 *)
val step_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures wf_state cok (step apply s))

(**
 * **Progress, one step**: a well-formed machine does not wedge. This is
 * preservation read against the `Stuck` clause of `wf_state`, which is `False`.
 *
 * Compare `step_perform_stuck`, which reduces the absence of `Stuck` to *some
 * frame on the stack handles the action*. That reduction left open the question
 * of why a handler should be there at all; well-scopedness is the answer, and
 * this lemma is where the two meet.
 *)
val step_progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures ~(Stuck? (step apply s)))

// ------------------------------------------------------------------ //
//  Progress                                                           //
// ------------------------------------------------------------------ //

(** **Preservation along a whole run**: the invariant is an invariant of `steps`,
    not merely of `step`. Induction on the fuel. *)
val steps_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures wf_state cok (steps apply n s))

(**
 * **Progress**: a well-formed machine never gets stuck, however long it runs.
 *
 * This is the theorem the `Stuck` constructor was always waiting for. Its
 * comment in `Hoop.Runtime` says the state *should never occur as long as the
 * runtime is sound*; here that hope is discharged, against a precise reading of
 * *sound* — the program is well scoped, and the FFI's `apply` respects
 * well-scopedness.
 *)
val progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures ~(Stuck? (steps apply n s)))

(** **Loading a well-scoped program yields a well-formed state**: the empty stack
    is well formed and offers exactly the empty environment. *)
val load_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ ws cok (can_nothing ()) c)
      (ensures wf_state cok (load c))

(**
 * **From the invariant to the precondition of `run`**: `Hoop.Runtime.run`
 * demands `never_stuck`, and this is what produces it.
 *
 * `run` cannot be given `wf_state cok s` directly as its precondition, because
 * `run` lives in `Hoop.Runtime` and would then need `step_preserves_wf`, which
 * lives here — modules do not go round in circles. Phrasing `run`'s
 * precondition as *this run never reaches `Stuck`* breaks the knot: that
 * property is closed under `step` by inspection, so `Hoop.Runtime` stays
 * self-contained, while the substance of the argument is supplied from here by
 * these two lemmas.
 *)
val wf_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
      (ensures never_stuck apply s)

(**
 * **The entry point**: a well-scoped program may be handed to `run`, and comes
 * back `Done`.
 *
 * Read together with the type of `run`, this is the end-to-end statement of the
 * development: if the PureScript side only ever builds programs whose `perform`s
 * sit inside a matching `with`-block, and its clause interpreter respects
 * `apply_ok`, then the machine either diverges or returns a value — it never
 * reports an unhandled operation.
 *)
val load_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ ws cok (can_nothing ()) c)
      (ensures never_stuck apply (load c))
