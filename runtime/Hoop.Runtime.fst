(**
 * **The runtime that ships**: the evidence-passing machine `<C, E, K>`, with
 * tail-resumptive ("fast") handler clauses, linked to the reference machine by a
 * WEAK SIMULATION rather than by per-transition state equality.
 *
 * C and K are `Hoop.Runtime.Syntax`; the reference reading of the transitions is
 * `Hoop.Runtime.Semantics`. This module supplies E, and E does two jobs.
 *
 *   - It is an *evidence environment*, mapping each handled operation to the
 *     prompt that handles it and to the environment outside that prompt.
 *     `Hoop.Runtime.Semantics.step` searches the stack at every `perform`; here
 *     that search is one `Env.lookup`.
 *
 *   - It is the *classical* E, mapping a name to a value. In a conventional CEK
 *     machine that is all E does; in Hoop the lexical bindings are already held
 *     by PureScript/JavaScript closures, so for a long time this role had no
 *     occupant and E was a handler context wearing the letter. Prompt-local
 *     cells are the one genuinely `label -> value` binding the language has, and
 *     they live here: a `NewP` extends E by a level exactly as a `Handle` does,
 *     a `ReadP` is one `Env.lookup`, and leaving either frame pops one level.
 *
 * The two sorts of name cannot collide, because `Hoop.Runtime.Handlers.key` has
 * a constructor for each and no handler table can build the cell one -- see the
 * header there, and `pd` below on why the second role belongs in E and not in a
 * store.
 *
 * Three layers, and the middle one is the machine:
 *
 *   1. `Hoop.Runtime.Semantics`, untouched, instantiated at the clause type
 *      `clause cl`. It knows nothing about `fast`: the reference reading of a
 *      fast clause is *constructed here*, by `desugar`, as the ordinary ctl
 *      clause `fun args k -> Op (apply_fast c args) k`. No new frame
 *      constructor, no mask, no change to `handled_in` or `find_prompt`.
 *
 *   2. The machine. `mstate` carries the evidence environment in its
 *      configuration and has an `MEnvF` frame that exists only on this side. A
 *      fast clause body runs *in place* -- nothing is captured, the stack is not
 *      cut -- under the handler's own environment, with the perform site's
 *      environment saved in the frame.
 *
 *   3. The link. `erase_st` maps a machine configuration to a reference
 *      state, and `msim` says one machine transition is one *or two* reference
 *      transitions. Never zero, so there is no stuttering to rank.
 *
 * `execute` is the extracted entry point -- what `runtime/ml/melange/hoop_ffi.ml` calls,
 * and the only thing in the development that touches the FFI boundary. Its
 * postcondition is stated about `Hoop.Runtime.Semantics.steps` through
 * `erase_st`, so `Hoop.Runtime.Metatheory` and `Hoop.Runtime.Laws` continue to
 * speak about the reference machine without a line being restated: specification
 * and implementation, in that order.
 *
 * *Why a weak simulation and not state equality.* An earlier machine kept the
 * environment beside a reference `state` and proved the two agree transition by
 * transition. That is unavailable here by construction: a fast clause body runs
 * without the capture the reference performs, so the two stacks stop having the
 * same length -- an `MEnvF` stands for a whole segment of the reference stack.
 * `erase_st` is what relates them, and `msim` is the equality that survives.
 *
 * *Why no height is tracked.* Locating a prompt by the height it was installed
 * at is an index into the *reference* stack, which `MEnvF` makes unavailable.
 * `msplit` below therefore walks -- and walks only the captured part, which is
 * the property evidence passing exists to buy, and the one a height was only
 * ever a means to. The module consequently keeps its own `env_of_stack`, at a
 * payload that is a prompt frame and nothing else.
 *)
module Hoop.Runtime

open FStar.List.Tot
open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics

module E = Hoop.Runtime.Env
module MT = Hoop.Runtime.Metatheory

(* ------------------------------------------------------------------ *)
(*  1.  Clauses: the fast/full distinction, visible to F*              *)
(* ------------------------------------------------------------------ *)

(**
 * **A clause, tagged.** The FFI hands over an opaque handle `cl` together with
 * *two* interpreters (`full_t`, `fast_t`); which one applies is decided by this
 * tag, which F* can see. The equivalence `fast f == ctl (\args k -> bind (f
 * args) k)` is therefore a definition -- `desugar` -- rather than an assumption
 * at the boundary.
 *)
noeq
type clause (cl: Type u#a) : Type u#a =
  | Full : c:cl -> clause cl
  | Fast : c:cl -> clause cl

let ct (v: Type) (cl: Type) = comp_tree v (clause cl)
let rframe (v cl: Type) = frame v (clause cl)
let rstack (v cl: Type) = stack v (clause cl)
let rstate (v cl: Type) = state v (clause cl)

(** **The two FFI interpreters.** A full clause is handed the delimited
    continuation; a fast clause is not, and cannot be. *)
let full_t (v cl: Type) = cl -> list v -> (v -> ct v cl) -> ct v cl
let fast_t (v cl: Type) = cl -> list v -> ct v cl

(**
 * **The desugaring**, i.e. the reference reading of a tagged clause. This is the
 * `apply` the reference machine is run with. A `Fast c` clause reads as the ctl
 * clause that binds the body to the continuation and resumes exactly once --
 * built here, in F*, not trusted from outside.
 *
 * `noextract`: the machine never dispatches through this. It calls
 * `af` and `afast` directly, which is what makes the tag free at run time.
 *)
noextract
let desugar (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
  : apply_t v (clause cl)
  = fun c payload k ->
      match c with
      | Full c0 -> af c0 payload k
      | Fast c0 -> Op (afast c0 payload) k

(* ------------------------------------------------------------------ *)
(*  2.  The machine                                          *)
(* ------------------------------------------------------------------ *)

(**
 * **What a level of the evidence environment carries here**: the frame that
 * installed it, which is a prompt or a cell and never a bind. No height, no
 * prompt count -- the machine never needs to locate a prompt by arithmetic,
 * because it never cuts its stack at one except through `msplit`, which walks.
 *
 * *Why a cell is a level too.* In a classical CEK machine E maps variables to
 * values. Ours mapped effect names to handler evidence and nothing else -- a
 * *handler context*, not an environment; the classical E was absent because the
 * language is closed and PureScript's own closures hold the lexical bindings.
 * A prompt-local cell is the one thing in this language that genuinely is a
 * `label -> value` binding, so putting it here is what makes E take on the
 * second role, and it is the role the letter was named for. The payload is
 * consequently a `ParamF` or a `PromptF`, and the two lookups -- an operation's
 * evidence and a cell's value -- are one operation on one structure, kept apart
 * by the two constructors of `Hoop.Runtime.Handlers.key`.
 *
 * *And a cell belongs in E rather than in a store.* A CESK store is global and
 * persistent, which is precisely the cached-pointer machine this design was
 * chosen over: there both strands of a resumption share one cell and
 * `choice(state)` comes out `[(False,1),(True,2)]`. An environment is captured
 * and restored with the continuation, so each resumption gets the cell as it
 * was captured -- which is where `choice(state) = [(False,1),(True,1)]` comes
 * from. **The per-branch semantics is a consequence of cells living in E.**
 * `Hoop.Runtime.Test` fixtures 26-29 are the two figures that measure it.
 *)
let pd (v cl: Type) = f: rframe v cl { PromptF? f \/ ParamF? f }
let menv (v cl: Type) = E.env (pd v cl)

(**
 * **The environment a *reference* stack offers.** One level per prompt and one
 * per cell, innermost first. The machine's environment is compared against this,
 * up to `E.equiv`, in `config_ok`.
 *
 * `noextract`: it states an invariant, and no transition computes it -- the
 * machine carries its environment rather than rebuilding it.
 *)
noextract
let rec env_of_stack (#v #cl: Type) (k: rstack v cl)
  : Tot (menv v cl) (decreases k)
  = match k with
    | [] -> E.empty
    | BindF _ :: r -> env_of_stack r
    | ParamF l x :: r ->
        E.extend (env_of_stack r) (var_keyset l) (ParamF l x <: pd v cl)
    | PromptF hs ret :: r ->
        E.extend (env_of_stack r) (keys hs) (PromptF hs ret <: pd v cl)

(**
 * **The machine frames.** `MEnvF` is the one that has no counterpart in the
 * reference machine: it marks a tail-resumptive clause body running in place. It
 * carries the operation whose clause is running -- which is how its own prompt
 * is re-found -- and the environment in force at the perform site, which is
 * restored when the body completes. No height, no count.
 *)
noeq
type mframe (v cl: Type) =
  | MBindF : fn:(v -> ct v cl) -> mframe v cl
  // The machine's parameter frame, erasing POINTWISE and TOTALLY to `ParamF`.
  // Unlike `MEnvF` it stands for exactly one reference frame, so it costs the
  // erasure no definedness condition and `stack_ok` nothing.
  | MParamF : label:string -> value:v -> mframe v cl
  | MPromptF : hs:handlers (clause cl) -> ret:option (v -> ct v cl) -> mframe v cl
  | MEnvF : eff:string -> op:string -> saved:menv v cl -> mframe v cl

let mstack (v cl: Type) = list (mframe v cl)

(** **The machine state.** `MStep` carries the environment; the
    reference `state` does not, and does not need to. *)
noeq
type mstate (v cl: Type) =
  | MDone : value:v -> mstate v cl
  | MStep : c:ct v cl -> w:menv v cl -> k:mstack v cl -> mstate v cl
  | MStuck : eff:string -> op:string -> mstate v cl

(* ------------------------------------------------------------------ *)
(*  3.  The erasure                                                    *)
(* ------------------------------------------------------------------ *)

(**
 * **The erasure of a machine stack to a reference stack.**
 *
 * `MBindF` and `MPromptF` map across unchanged. An `MEnvF` erases to the frame
 * the reference machine really has at that point: the desugared fast clause
 * pushed `BindF (kont_of captured)` -- the continuation of the ctl clause it
 * desugars to -- and the frames from the `MEnvF` down to and including its own
 * prompt are exactly that captured segment, so they are *absorbed*.
 *
 * The erasure is therefore partial: it is defined only when the `MEnvF`'s prompt
 * really is below it. That is the definedness condition of `erase_k`, and
 * `stack_ok` is the invariant which supplies it. It lives on this side only; the
 * reference machine never hears of it.
 *
 * The continuation is written `Hoop.Runtime.Semantics.kont_of captured`, which
 * is how `Hoop.Runtime.Semantics.step` writes it too, so the two are the same
 * term rather than two anonymous closures that happen to elaborate alike.
 *)
let rec erase_k (#v #cl: Type) (kk: mstack v cl)
  : GTot (option (rstack v cl)) (decreases kk)
  = match kk with
    | [] -> Some []
    | MParamF l x :: r ->
        (match erase_k r with None -> None | Some k -> Some (ParamF l x :: k))
    | MBindF fn :: r ->
        (match erase_k r with None -> None | Some k -> Some (BindF fn :: k))
    | MPromptF hs ret :: r ->
        (match erase_k r with None -> None | Some k -> Some (PromptF hs ret :: k))
    | MEnvF eff op _ :: r ->
        (match erase_k r with
          | None -> None
          | Some k ->
            (match find_prompt eff op k with
              | None -> None
              | Some (captured, clause, below) ->
                  Some (BindF (kont_of captured) :: below)))

let erase_st (#v #cl: Type) (q: mstate v cl) : GTot (option (rstate v cl)) =
  match q with
  | MDone x -> Some (Done x)
  | MStuck e o -> Some (Stuck e o)
  | MStep c w kk -> (match erase_k kk with None -> None | Some k -> Some (Step c k))

(* ------------------------------------------------------------------ *)
(*  4.  The invariant                                                  *)
(* ------------------------------------------------------------------ *)

(**
 * **The machine stack is well formed.** Two things, at every `MEnvF`:
 *
 *   - its prompt is below it and *inside the same erased stack*
 *     (`handled_in`), which is what makes `erase_k` total here;
 *   - the environment it saved is the environment the frames below it offer,
 *     which is what makes restoring it on completion correct.
 *
 * Confined to this module. Nothing in `Hoop.Runtime.Semantics` mentions it.
 *)
let rec stack_ok (#v #cl: Type) (kk: mstack v cl) : GTot prop (decreases kk) =
  match kk with
  | [] -> True
  | MParamF _ _ :: r -> stack_ok r
  | MBindF _ :: r -> stack_ok r
  | MPromptF _ _ :: r -> stack_ok r
  | MEnvF eff op saved :: r ->
      stack_ok r /\
      (match erase_k r with
        | None -> False
        | Some k -> handled_in eff op k /\ saved `E.equiv` env_of_stack k)

(** **The machine invariant.** The stack is well formed and the environment is
    the one the *erased* stack offers -- which, when an `MEnvF` is in flight, is
    the fast clause's own `below`, since the erasure absorbed the frames down to
    its prompt. *)
let config_ok (#v #cl: Type) (q: mstate v cl) : GTot prop =
  match q with
  | MDone _ -> True
  | MStuck _ _ -> True
  | MStep _ w kk ->
      stack_ok kk /\
      (match erase_k kk with
        | None -> False
        | Some k -> w `E.equiv` env_of_stack k)

(* ------------------------------------------------------------------ *)
(*  5.  The machine transition                                       *)
(* ------------------------------------------------------------------ *)

(**
 * **Splitting the machine stack at the prompt handling `(eff, op)`**, in one
 * pass: it returns *both* the segment the clause is to be handed -- already in
 * reference frames, which is the form a delimited continuation travels in -- and
 * the machine stack the machine runs on below the prompt.
 *
 * The erasure is fused into the walk rather than run before it. Only the
 * captured part is visited; the frames below the handling prompt are handed back
 * untouched. This is what evidence passing exists to make possible.
 *
 * The one place where an `MEnvF` needs care: while a fast clause body is in
 * flight, the prompts between the `MEnvF` and its own prompt are *masked* --
 * they are not in the environment, and the erasure absorbs them -- so the search
 * must jump over them wholesale. It does so by re-running itself on the
 * `MEnvF`'s own key. The segment that jump skips is exactly what the erasure
 * absorbs into a single `BindF (kont_of ...)`, and that frame is what goes into
 * the captured segment here, so the two agree by construction rather than by a
 * later argument -- see `msplit_agrees`.
 *
 * The refinement makes the remaining stack a strict suffix, which is what
 * discharges termination of the two-phase `MEnvF` branch.
 *
 * *This is the specification.* What the machine runs is `msplit_fast` below,
 * which computes the same answer without a recursion as deep as the segment is
 * long; see there.
 *)
noextract
let rec msplit (#v #cl: Type) (eff op: string) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl)
          { match o with None -> True | Some (_, b) -> length b < length kk })
        (decreases (length kk))
  = match kk with
    | [] -> None
    | MParamF l x :: r ->
        (match msplit eff op r with
          | None -> None
          | Some (cap, b) -> Some (ParamF l x :: cap, b))
    | MBindF fn :: r ->
        (match msplit eff op r with
          | None -> None
          | Some (cap, b) -> Some (BindF fn :: cap, b))
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> Some ([PromptF hs ret], r)
          | None ->
            (match msplit eff op r with
              | None -> None
              | Some (cap, b) -> Some (PromptF hs ret :: cap, b)))
    | MEnvF e' o' _ :: r ->
        (match msplit e' o' r with
          | None -> None
          | Some (cap', mrest) ->
            (match msplit eff op mrest with
              | None -> None
              | Some (cap, b) -> Some (BindF (kont_of cap') :: cap, b)))

(** **Leaving a prompt**: pop one level. The guard is unreachable under
    `config_ok` and is written out so that `mstep` is a total function. *)
let pop_env (#v #cl: Type) (w: menv v cl) : Tot (menv v cl) =
  if E.is_empty w then w else E.outer w

(**
 * **Splicing a captured segment back on.** A captured segment is made of
 * *reference* frames -- it travels inside a `Resumed` node of the shared AST --
 * so resuming injects them back as machine frames. No `MEnvF` can appear in
 * one: the erasure turned every `MEnvF` into a `BindF` when the segment was
 * captured.
 *
 * The specification; `inj_append` below is what runs.
 *)
noextract
let rec inj_k (#v #cl: Type) (k: rstack v cl) : Tot (mstack v cl) (decreases k) =
  match k with
  | [] -> []
  | ParamF l x :: r -> MParamF l x :: inj_k r
  | BindF fn :: r -> MBindF fn :: inj_k r
  | PromptF hs ret :: r -> MPromptF hs ret :: inj_k r

(**
 * **Re-deriving the environment of a spliced segment**, against the environment
 * in force *now*: a segment may be resumed under a stack other than the one it
 * was captured on, so nothing captured with it may be reused.
 *
 * The specification; `mreinstall_fast` below is what runs.
 *)
noextract
let rec mreinstall (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Tot (menv v cl) (decreases k)
  = match k with
    | [] -> w
    | BindF _ :: r -> mreinstall w r
    | ParamF l x :: r ->
        E.extend (mreinstall w r) (var_keyset l) (ParamF l x <: pd v cl)
    | PromptF hs ret :: r ->
        E.extend (mreinstall w r) (keys hs) (PromptF hs ret <: pd v cl)

(* ------------------------------------------------------------------ *)
(*  5a.  The three walks, as loops                                     *)
(*                                                                     *)
(*  `inj_k`, `mreinstall` and `msplit` are all structurally recursive   *)
(*  over a captured segment, and the extracted runtime maps that depth  *)
(*  onto the host's call stack -- a few tens of thousands of frames     *)
(*  that are the user's to spend, not the machine's. Each is therefore  *)
(*  paired with an accumulating loop, proved equal to it, and the       *)
(*  equality lives in the loop's type so that every statement about the *)
(*  specification is a statement about what runs.                       *)
(* ------------------------------------------------------------------ *)

(* Injection, as a fold from the bottom of the segment. *)
let rec inj_onto (#v #cl: Type) (rk: rstack v cl) (acc: mstack v cl)
  : Tot (mstack v cl) (decreases rk)
  = match rk with
    | [] -> acc
    | ParamF l x :: r -> inj_onto r (MParamF l x :: acc)
    | BindF fn :: r -> inj_onto r (MBindF fn :: acc)
    | PromptF hs ret :: r -> inj_onto r (MPromptF hs ret :: acc)

private
let rec inj_onto_append (#v #cl: Type) (l1 l2: rstack v cl) (acc: mstack v cl)
  : Lemma (ensures inj_onto (l1 @ l2) acc == inj_onto l2 (inj_onto l1 acc)) (decreases l1)
  = match l1 with
    | [] -> ()
    | ParamF l x :: r -> inj_onto_append r l2 (MParamF l x :: acc)
    | BindF fn :: r -> inj_onto_append r l2 (MBindF fn :: acc)
    | PromptF hs ret :: r -> inj_onto_append r l2 (MPromptF hs ret :: acc)

private
let rec inj_onto_rev (#v #cl: Type) (k: rstack v cl) (acc: mstack v cl)
  : Lemma (ensures inj_onto (rev k) acc == inj_k k @ acc) (decreases k)
  = match k with
    | [] -> ()
    | f :: r ->
        inj_onto_rev r acc;
        rev_rev' k;
        rev_rev' r;
        inj_onto_append (rev r) [f] acc

(** **Splicing, without recursing over the segment.** *)
let inj_append (#v #cl: Type) (k: rstack v cl) (kk: mstack v cl)
  : Tot (o: mstack v cl { o == inj_k k @ kk })
  = inj_onto_rev k kk;
    inj_onto (rev k) kk

(* Re-derivation, as a fold from the bottom of the segment. *)
let rec mreinstall_loop (#v #cl: Type) (w: menv v cl) (rk: rstack v cl)
  : Tot (menv v cl) (decreases rk)
  = match rk with
    | [] -> w
    | BindF _ :: r -> mreinstall_loop w r
    | ParamF l x :: r ->
        mreinstall_loop (E.extend w (var_keyset l) (ParamF l x <: pd v cl)) r
    | PromptF hs ret :: r ->
        mreinstall_loop (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) r

private
let rec mreinstall_loop_append (#v #cl: Type) (w: menv v cl) (l1 l2: rstack v cl)
  : Lemma
      (ensures mreinstall_loop w (l1 @ l2) == mreinstall_loop (mreinstall_loop w l1) l2)
      (decreases l1)
  = match l1 with
    | [] -> ()
    | BindF _ :: r -> mreinstall_loop_append w r l2
    | ParamF l x :: r ->
        mreinstall_loop_append (E.extend w (var_keyset l) (ParamF l x <: pd v cl)) r l2
    | PromptF hs ret :: r ->
        mreinstall_loop_append (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) r l2

private
let rec mreinstall_loop_rev (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Lemma (ensures mreinstall_loop w (rev k) == mreinstall w k) (decreases k)
  = match k with
    | [] -> ()
    | f :: r ->
        mreinstall_loop_rev w r;
        rev_rev' k;
        rev_rev' r;
        mreinstall_loop_append w (rev r) [f]

(** **Re-deriving, without recursing over the segment.** *)
let mreinstall_fast (#v #cl: Type) (w: menv v cl) (k: rstack v cl)
  : Tot (w': menv v cl { w' == mreinstall w k })
  = mreinstall_loop_rev w k;
    mreinstall_loop w (rev k)

(**
 * **The split, without recursing over the captured segment.** `acc` holds the
 * frames captured so far, innermost last, so the answer is `rev acc` -- the same
 * reversal trick the two loops above use, and `rev` is itself a loop in
 * `runtime/ml/shim/FStar_List_Tot_Base.ml`.
 *
 * The nested call in the `MEnvF` branch is genuinely nested and not a tail call.
 * It cannot be otherwise: jumping over a masked region means finding its far end
 * first. Its depth is the number of *nested fast clause bodies* in flight inside
 * the captured segment, not the number of frames -- and a fast clause body that
 * performs another fast operation is the only way to nest one.
 *)
let rec msplit_acc (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl)
          { match o with None -> True | Some (_, b) -> length b < length kk })
        (decreases (length kk))
  = match kk with
    | [] -> None
    | MParamF l x :: r -> msplit_acc eff op (ParamF l x :: acc) r
    | MBindF fn :: r -> msplit_acc eff op (BindF fn :: acc) r
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> Some (rev (PromptF hs ret :: acc), r)
          | None -> msplit_acc eff op (PromptF hs ret :: acc) r)
    | MEnvF e' o' _ :: r ->
        (match msplit_acc e' o' [] r with
          | None -> None
          | Some (cap', mrest) -> msplit_acc eff op (BindF (kont_of cap') :: acc) mrest)

(* What the accumulating walk computes, in terms of the specification: the same
   answer, with whatever was already accumulated in front of the captured
   segment. Named so that no `match` appears in the statement of a lemma. *)
private
let msplit_acc_ok
    (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : GTot prop
  = match msplit_acc eff op acc kk, msplit eff op kk with
    | None, None -> True
    | Some (cap1, b1), Some (cap2, b2) -> cap1 == rev acc @ cap2 /\ b1 == b2
    | _ -> False

(* Pushing one frame onto the accumulator prepends it to the captured segment.
   The only arithmetic of `rev` the proof needs, and it is stated here so that
   the induction below cites it rather than re-derives it three times. *)
private
let rev_cons_append (#a: Type) (x: a) (acc l: list a)
  : Lemma (rev (x :: acc) @ l == rev acc @ (x :: l))
  = rev_rev' (x :: acc);
    rev_rev' acc;
    append_assoc (rev acc) [x] l

private
let rec msplit_acc_agrees
    (#v #cl: Type) (eff op: string) (acc: rstack v cl) (kk: mstack v cl)
  : Lemma (ensures msplit_acc_ok eff op acc kk) (decreases (length kk))
  = match kk with
    | [] -> ()
    | MParamF l x :: r ->
        msplit_acc_agrees eff op (ParamF l x :: acc) r;
        (match msplit eff op r with
          | None -> ()
          | Some (cap, _) -> rev_cons_append (ParamF l x <: rframe v cl) acc cap)
    | MBindF fn :: r ->
        msplit_acc_agrees eff op (BindF fn :: acc) r;
        (match msplit eff op r with
          | None -> ()
          | Some (cap, _) -> rev_cons_append (BindF fn <: rframe v cl) acc cap)
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ ->
              rev_cons_append (PromptF hs ret <: rframe v cl) acc [];
              append_l_nil (rev (PromptF hs ret :: acc));
              append_l_nil (rev acc)
          | None ->
              msplit_acc_agrees eff op (PromptF hs ret :: acc) r;
              (match msplit eff op r with
                | None -> ()
                | Some (cap, _) -> rev_cons_append (PromptF hs ret <: rframe v cl) acc cap))
    | MEnvF e' o' _ :: r ->
        msplit_acc_agrees e' o' [] r;
        (match msplit e' o' r with
          | None -> ()
          | Some (cap', mrest) ->
            msplit_acc_agrees eff op (BindF (kont_of cap') :: acc) mrest;
            (match msplit eff op mrest with
              | None -> ()
              | Some (cap, _) -> rev_cons_append (BindF (kont_of cap') <: rframe v cl) acc cap))

(** **The split the machine runs.** Its answer is the specification's, and the
    equality is in the type, so `msplit_agrees` below speaks about both at once. *)
let msplit_fast (#v #cl: Type) (eff op: string) (kk: mstack v cl)
  : Tot (o: option (rstack v cl & mstack v cl) { o == msplit eff op kk })
  = msplit_acc_agrees eff op [] kk;
    msplit_acc eff op [] kk

(* ------------------------------------------------------------------ *)
(*  5b.  Prompt-local state, on the machine                            *)
(*                                                                     *)
(*  The one place where a cell costs this machine more than it costs   *)
(*  the reference: while a tail-resumptive body is in flight, the      *)
(*  frames an `MEnvF` masks are ABSENT FROM THE ERASED STACK -- the    *)
(*  erasure absorbs them into the `BindF (kont_of ...)` the reference  *)
(*  machine really has there -- so a cell inside a masked region is    *)
(*  invisible to the reference machine and must be invisible here too. *)
(*  Both walks therefore jump over a masked region exactly as `msplit` *)
(*  does, by re-running the split on the `MEnvF`'s own key.            *)
(*                                                                     *)
(*  THE READ IS NOT HERE. It is one `E.lookup` in `mstep`, because a   *)
(*  cell is a level of the evidence environment; `mfind_param` below   *)
(*  survives only as the statement that the walk and the lookup agree, *)
(*  which is `mfind_param_agrees` together with `lookup_param_find`.   *)
(*                                                                     *)
(*  THE WRITE CARRIES AN ENVIRONMENT. A cell's value is a level's      *)
(*  payload, so changing it changes `E.levels`, and the machine's `w`  *)
(*  must be rebuilt rather than carried across a `WriteP` as it was    *)
(*  when a level held only a prompt. Both walks below therefore thread *)
(*  the environment of the stack they are rebuilding: they descend     *)
(*  popping one level per prompt and per cell crossed, and ascend      *)
(*  pushing one back for each. The environment of the rebuilt stack is *)
(*  produced by the same recursion that produces the rebuilt stack, so *)
(*  it costs the walk no second pass -- and it is the ONLY way to get  *)
(*  the saved environment of an `MEnvF` right: a write that reaches    *)
(*  below a tail-resumptive body's own prompt changes a cell the       *)
(*  PERFORM SITE can see, so the environment that frame restores on    *)
(*  completion is stale unless it is rebuilt too. `Hoop.Runtime.Test`  *)
(*  fixture 30 is exactly that program.                                *)
(* ------------------------------------------------------------------ *)

(**
 * **Reading a cell, by walking.** The nearest `MParamF` with this label that is
 * not inside a masked region.
 *
 * `noextract`: nothing runs it. The machine reads a cell out of its environment
 * in one `E.lookup`, and this is kept as the other side of the equation --
 * `mfind_param_agrees` says the walk finds what the reference machine finds and
 * `lookup_param_find` says the lookup does, so the two answers are the same
 * answer. Were the environment ever to be realised differently, this is the
 * specification it would be measured against.
 *)
noextract
let rec mfind_param (#v #cl: Type) (l: string) (kk: mstack v cl)
  : Tot (option v) (decreases (length kk))
  = match kk with
    | [] -> None
    | MParamF l' x :: r -> if l' = l then Some x else mfind_param l r
    | MBindF _ :: r -> mfind_param l r
    | MPromptF _ _ :: r -> mfind_param l r
    | MEnvF e o _ :: r ->
        (match msplit_fast e o r with
          | None -> None
          | Some (_, b) -> mfind_param l b)

(**
 * **Replacing what lies below a split point.** `mrepl eff op w kk wb' b'`
 * rebuilds `kk` with the machine stack below the prompt handling `(eff, op)`
 * replaced by `b'` -- the frames above it copied, the masked regions carried
 * along intact -- and rebuilds the environment alongside it: `w` is the
 * environment `kk` offers, `wb'` the one `b'` offers, and the answer's first
 * component is the one the rebuilt stack offers.
 *
 * It exists for one caller: a write whose cell sits below an `MEnvF` has to
 * come back up through the region that `MEnvF` masks, and the region is
 * delimited by a search rather than by a count, so it cannot simply be
 * consed back on. `mrepl_agrees` is what says the rebuild leaves the erasure
 * of the region -- the captured segment -- exactly where it was, and leaves the
 * environment the one that segment on the new tail offers.
 *
 * *The `MEnvF` branch is where the environment earns its passage.* Its saved
 * environment is the perform site's, which is the one the frames below the
 * frame offer -- and those frames have just been rebuilt around a changed cell.
 * The recursive call that puts the region back therefore hands back the new
 * saved environment, and it is that value, not the old `sv`, that goes into the
 * frame. Nothing else could supply it: `sv` describes `cap @ below`, the
 * write touched `below`, and the length of `cap` is known only to this walk.
 *
 * *This is the specification.* What the machine runs is `mrepl_fast` in 5c
 * below, which computes the same answer without a recursion as deep as the
 * stack; see there.
 *)
noextract
let rec mrepl (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl)
    (wb': menv v cl) (b': mstack v cl)
  : Tot (option (menv v cl & mstack v cl)) (decreases (length kk))
  = match kk with
    | [] -> None
    | MBindF fn :: r ->
        (match mrepl eff op w r wb' b' with
          | None -> None
          | Some (w', r') -> Some (w', MBindF fn :: r'))
    | MParamF l y :: r ->
        (match mrepl eff op (pop_env w) r wb' b' with
          | None -> None
          | Some (w', r') ->
              Some (E.extend w' (var_keyset l) (ParamF l y <: pd v cl), MParamF l y :: r'))
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ ->
              Some (E.extend wb' (keys hs) (PromptF hs ret <: pd v cl), MPromptF hs ret :: b')
          | None ->
            (match mrepl eff op (pop_env w) r wb' b' with
              | None -> None
              | Some (w', r') ->
                  Some (E.extend w' (keys hs) (PromptF hs ret <: pd v cl), MPromptF hs ret :: r')))
    | MEnvF e' o' sv :: r ->
        (match msplit_fast e' o' r with
          | None -> None
          | Some (_, mrest) ->
            (match mrepl eff op w mrest wb' b' with
              | None -> None
              | Some (wm', mrest') ->
                (match mrepl e' o' sv r wm' mrest' with
                  | None -> None
                  | Some (sv', r') -> Some (wm', MEnvF e' o' sv' :: r'))))

(**
 * **Writing a cell.** The frames above the cell are rebuilt and the frames
 * below are shared, exactly as `Hoop.Runtime.Semantics.set_param` does on the
 * reference stack -- with the masked regions jumped over on the way down and
 * spliced back by `mrepl` on the way up -- and the environment is rebuilt with
 * them, since the cell's value is a level's payload.
 *
 * `w` is the environment the stack offers and the answer's first component is
 * the environment the rebuilt stack offers. That the two are related by exactly
 * one level's payload is true but not said here: saying it would need an
 * `Hoop.Runtime.Env` operation that replaces a payload in place, and the walk
 * has to rebuild the levels above the cell in any case, because it is rebuilding
 * the frames above the cell in any case.
 *
 * *This is the specification.* What the machine runs is `mset_param_fast` in 5c
 * below.
 *)
noextract
let rec mset_param (#v #cl: Type) (l: string) (x: v) (w: menv v cl) (kk: mstack v cl)
  : Tot (option (menv v cl & mstack v cl)) (decreases (length kk))
  = match kk with
    | [] -> None
    | MParamF l' y :: r ->
        if l' = l
        then Some (E.extend (pop_env w) (var_keyset l) (ParamF l x <: pd v cl), MParamF l x :: r)
        else
          (match mset_param l x (pop_env w) r with
            | None -> None
            | Some (w', r') ->
                Some (E.extend w' (var_keyset l') (ParamF l' y <: pd v cl), MParamF l' y :: r'))
    | MBindF fn :: r ->
        (match mset_param l x w r with
          | None -> None
          | Some (w', r') -> Some (w', MBindF fn :: r'))
    | MPromptF hs ret :: r ->
        (match mset_param l x (pop_env w) r with
          | None -> None
          | Some (w', r') ->
              Some (E.extend w' (keys hs) (PromptF hs ret <: pd v cl), MPromptF hs ret :: r'))
    | MEnvF e o sv :: r ->
        (match msplit_fast e o r with
          | None -> None
          | Some (_, b) ->
            (match mset_param l x w b with
              | None -> None
              | Some (wb', b') ->
                (match mrepl e o sv r wb' b' with
                  | None -> None
                  | Some (sv', r') -> Some (wb', MEnvF e o sv' :: r'))))

(* ------------------------------------------------------------------ *)
(*  5c.  The two walks of the write, as loops                          *)
(*                                                                     *)
(*  `mrepl` and `mset_param` recurse over the machine stack and build  *)
(*  their answer on the way back out, so the extracted runtime maps    *)
(*  the whole depth of the stack onto the host's call stack -- the     *)
(*  same few tens of thousands of frames that `inj_onto`,              *)
(*  `mreinstall_loop` and `msplit_acc` in 5a exist to keep off it.     *)
(*  Each is therefore paired with an accumulating loop, proved equal   *)
(*  to it, WITH THE EQUALITY IN THE LOOP'S TYPE, so that every         *)
(*  statement about the specification -- `mrepl_agrees`,               *)
(*  `mset_param_agrees`, and `msim` through them -- is a statement     *)
(*  about what runs.                                                   *)
(*                                                                     *)
(*  Unlike the three in 5a these walks rebuild as they return, and     *)
(*  they now rebuild an environment as well as a stack, so the         *)
(*  accumulator is unwound rather than reversed: `unwind` replays the  *)
(*  frames passed on the way down, innermost first, pushing one level  *)
(*  back for each prompt and each cell.                                *)
(*                                                                     *)
(*  The nested call in each `MEnvF` branch stays nested, exactly as it *)
(*  does in `msplit_acc`, and for the same reason: jumping over a      *)
(*  masked region means finding its far end first, and putting the     *)
(*  region back means walking it. Its depth is the number of NESTED    *)
(*  FAST CLAUSE BODIES in flight, not the number of frames. What this  *)
(*  section removes is the recursion proportional to the stack.        *)
(* ------------------------------------------------------------------ *)

(**
 * **Replaying the frames the descent passed**, innermost first, rebuilding the
 * environment with them.
 *
 * The accumulator is a machine stack because that is what its entries are;
 * neither loop below ever pushes an `MEnvF` onto it -- an `MEnvF` is not passed
 * over, it is jumped over and then rebuilt by a nested walk -- so that branch is
 * unreachable. It is written as the identity on the frame rather than left out
 * because `unwind` is a total function, and because the specification equation
 * proved below quantifies over every accumulator: both sides read an unreachable
 * entry the same way, so nothing has to establish that it does not occur.
 *)
let rec unwind (#v #cl: Type) (acc: mstack v cl) (w: menv v cl) (kk: mstack v cl)
  : Tot (menv v cl & mstack v cl) (decreases acc)
  = match acc with
    | [] -> (w, kk)
    | MBindF fn :: a -> unwind a w (MBindF fn :: kk)
    | MParamF l y :: a ->
        unwind a (E.extend w (var_keyset l) (ParamF l y <: pd v cl)) (MParamF l y :: kk)
    | MPromptF hs ret :: a ->
        unwind a (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) (MPromptF hs ret :: kk)
    | MEnvF e o sv :: a -> unwind a w (MEnvF e o sv :: kk)

(* Unwinding an answer that may not exist. Named so that no `match` appears in
   the statement of the two lemmas below. *)
noextract
let unwind_opt (#v #cl: Type) (acc: mstack v cl) (o: option (menv v cl & mstack v cl))
  : GTot (option (menv v cl & mstack v cl))
  = match o with
    | None -> None
    | Some (w, kk) -> Some (unwind acc w kk)

(** **The replacement, as a descent and an unwind.** *)
let rec mrepl_acc (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl)
    (wb': menv v cl) (b': mstack v cl)
    (acc: mstack v cl)
  : Tot (option (menv v cl & mstack v cl)) (decreases (length kk))
  = match kk with
    | [] -> None
    | MBindF fn :: r -> mrepl_acc eff op w r wb' b' (MBindF fn :: acc)
    | MParamF l y :: r -> mrepl_acc eff op (pop_env w) r wb' b' (MParamF l y :: acc)
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ ->
              Some (unwind acc
                      (E.extend wb' (keys hs) (PromptF hs ret <: pd v cl))
                      (MPromptF hs ret :: b'))
          | None -> mrepl_acc eff op (pop_env w) r wb' b' (MPromptF hs ret :: acc))
    | MEnvF e' o' sv :: r ->
        (match msplit_fast e' o' r with
          | None -> None
          | Some (_, mrest) ->
            (match mrepl_acc eff op w mrest wb' b' [] with
              | None -> None
              | Some (wm', mrest') ->
                (match mrepl_acc e' o' sv r wm' mrest' [] with
                  | None -> None
                  | Some (sv', r') -> Some (unwind acc wm' (MEnvF e' o' sv' :: r')))))

private
let rec mrepl_acc_agrees (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl)
    (wb': menv v cl) (b': mstack v cl)
    (acc: mstack v cl)
  : Lemma
      (ensures
        mrepl_acc eff op w kk wb' b' acc == unwind_opt acc (mrepl eff op w kk wb' b'))
      (decreases (length kk))
  = match kk with
    | [] -> ()
    | MBindF fn :: r -> mrepl_acc_agrees eff op w r wb' b' (MBindF fn :: acc)
    | MParamF l y :: r -> mrepl_acc_agrees eff op (pop_env w) r wb' b' (MParamF l y :: acc)
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> ()
          | None -> mrepl_acc_agrees eff op (pop_env w) r wb' b' (MPromptF hs ret :: acc))
    | MEnvF e' o' sv :: r ->
        (match msplit_fast e' o' r with
          | None -> ()
          | Some (_, mrest) ->
            mrepl_acc_agrees eff op w mrest wb' b' [];
            (match mrepl eff op w mrest wb' b' with
              | None -> ()
              | Some (wm', mrest') -> mrepl_acc_agrees e' o' sv r wm' mrest' []))

(** **The replacement the machine runs.** Its answer is the specification's, and
    the equality is in the type, so `mrepl_agrees` speaks about both at once. *)
let mrepl_fast (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl)
    (wb': menv v cl) (b': mstack v cl)
  : Tot (o: option (menv v cl & mstack v cl) { o == mrepl eff op w kk wb' b' })
  = mrepl_acc_agrees eff op w kk wb' b' [];
    mrepl_acc eff op w kk wb' b' []

(** **The write, as a descent and an unwind.** *)
let rec mset_acc (#v #cl: Type) (l: string) (x: v)
    (w: menv v cl) (kk: mstack v cl) (acc: mstack v cl)
  : Tot (option (menv v cl & mstack v cl)) (decreases (length kk))
  = match kk with
    | [] -> None
    | MParamF l' y :: r ->
        if l' = l
        then
          Some (unwind acc
                  (E.extend (pop_env w) (var_keyset l) (ParamF l x <: pd v cl))
                  (MParamF l x :: r))
        else mset_acc l x (pop_env w) r (MParamF l' y :: acc)
    | MBindF fn :: r -> mset_acc l x w r (MBindF fn :: acc)
    | MPromptF hs ret :: r -> mset_acc l x (pop_env w) r (MPromptF hs ret :: acc)
    | MEnvF e o sv :: r ->
        (match msplit_fast e o r with
          | None -> None
          | Some (_, b) ->
            (match mset_acc l x w b [] with
              | None -> None
              | Some (wb', b') ->
                (match mrepl_fast e o sv r wb' b' with
                  | None -> None
                  | Some (sv', r') -> Some (unwind acc wb' (MEnvF e o sv' :: r')))))

private
let rec mset_acc_agrees (#v #cl: Type) (l: string) (x: v)
    (w: menv v cl) (kk: mstack v cl) (acc: mstack v cl)
  : Lemma
      (ensures mset_acc l x w kk acc == unwind_opt acc (mset_param l x w kk))
      (decreases (length kk))
  = match kk with
    | [] -> ()
    | MParamF l' y :: r ->
        if l' = l then () else mset_acc_agrees l x (pop_env w) r (MParamF l' y :: acc)
    | MBindF fn :: r -> mset_acc_agrees l x w r (MBindF fn :: acc)
    | MPromptF hs ret :: r -> mset_acc_agrees l x (pop_env w) r (MPromptF hs ret :: acc)
    | MEnvF e o sv :: r ->
        (match msplit_fast e o r with
          | None -> ()
          | Some (_, b) -> mset_acc_agrees l x w b [])

(** **The write the machine runs.** Its answer is the specification's, and the
    equality is in the type, so `mset_param_agrees` -- and `msim` through it --
    speaks about both at once. *)
let mset_param_fast (#v #cl: Type) (l: string) (x: v) (w: menv v cl) (kk: mstack v cl)
  : Tot (o: option (menv v cl & mstack v cl) { o == mset_param l x w kk })
  = mset_acc_agrees l x w kk [];
    mset_acc l x w kk []

(**
 * **One transition of the machine.**
 *
 *   - `Op`, `Handle`, `Var`  behave as in `Hoop.Runtime`.
 *   - `Var` over an `MEnvF`  is the *return* from a tail-resumptive body: the
 *                            perform site's environment comes back and the value
 *                            flows on as the operation's result. Nothing is
 *                            spliced -- the frames are still on the stack.
 *   - `Perform` / `Fast`     runs the body in place, under the handler's own
 *                            environment (`ev.below`), with an `MEnvF` marking
 *                            the boundary. The continuation is NOT captured and
 *                            the stack is NOT cut.
 *   - `Perform` / `Full`     the existing path: capture, hand the segment to the
 *                            clause, run on below the prompt.
 *   - `Resumed`              splice and re-derive.
 *   - `NewP` / `ReadP`       a cell is a level of the environment: install one,
 *                            and read one back out. The read is the transition
 *                            this design was taken for -- one `Env.lookup`,
 *                            against a walk of the machine stack that had to run
 *                            a `msplit` at every `MEnvF` it crossed.
 *   - `WriteP`               rebuilds the stack, because the erasure reads cell
 *                            values off frames, AND the environment, because a
 *                            cell's value is a level's payload. Twice O(depth),
 *                            and the price of the read above.
 *
 * *What a capture does to an `MEnvF`.* A delimited continuation travels inside a
 * `Resumed` node of the *shared* AST, so it is made of reference frames; the
 * captured segment handed to a full clause is therefore the *erasure* of the
 * machine segment, with each `MEnvF` in it replaced by the `BindF` the
 * reference machine has there. Resuming splices reference frames back
 * (`inj_append`), so no `MEnvF` is ever reinstalled: the tail-resumptive
 * optimisation lapses for a body that has been captured, and the machine behaves
 * exactly as the reference from that point. This is deliberate. It keeps a
 * single AST, avoids an FFI naturality assumption, and makes multi-shot
 * resumption automatically safe.
 *
 * *The `Full` branch does what a shipping implementation would do.* It calls the
 * split once, which walks the captured part of the stack and no further, and it
 * invokes the FFI's full interpreter `af` directly -- there is no dispatch
 * through `desugar` to be optimised away later.
 *)
let mstep
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (q: mstate v cl)
  : Tot (mstate v cl)
  = match q with
    | MDone _ -> q
    | MStuck _ _ -> q
    | MStep c w kk ->
      match c with
      | Op comp fn -> MStep comp w (MBindF fn :: kk)
      | Handle hs ret body ->
          MStep body (E.extend w (keys hs) (PromptF hs ret <: pd v cl)) (MPromptF hs ret :: kk)
      | Var value ->
          (match kk with
            | [] -> MDone value
            // A cell is a level, so leaving its frame leaves its level, exactly
            // as leaving a prompt does.
            | MParamF _ _ :: r -> MStep (Var value) (pop_env w) r
            | MBindF fn :: r -> MStep (fn value) w r
            | MPromptF hs ret :: r ->
                let w' = pop_env w in
                (match ret with
                  | Some fn -> MStep (fn value) w' r
                  | None -> MStep (Var value) w' r)
            | MEnvF _ _ saved :: r -> MStep (Var value) saved r)
      | Perform eff op payload ->
          (match E.lookup w (OpKey eff op) with
            | None -> MStuck eff op
            // The evidence of an `OpKey` is a prompt: a cell's level binds a
            // `VarKey` and nothing else, so the second branch is unreachable --
            // `lookup_find` is what says so. It is written out because `mstep`
            // is a total function and `pd` now admits both frames.
            | Some ev ->
              (match ev.E.prompt with
                | ParamF _ _ -> MStuck eff op
                | PromptF hs _ ->
                  (match lookup_clause hs eff op with
                    | None -> MStuck eff op
                    | Some (Fast c0) ->
                        MStep (afast c0 payload) ev.E.below (MEnvF eff op w :: kk)
                    | Some (Full c0) ->
                      (match msplit_fast eff op kk with
                        | None -> MStuck eff op
                        | Some (captured, b) ->
                            MStep (af c0 payload (kont_of captured)) ev.E.below b))))
      | Resumed kont value ->
          MStep (Var value) (mreinstall_fast w kont) (inj_append kont kk)
      // A cell binds a name to a value, so it extends the environment -- one
      // level, exactly as a `Handle` does, and popped again by the `Var` rule
      // above when its frame is left.
      | NewP l init body ->
          MStep body (E.extend w (var_keyset l) (ParamF l init <: pd v cl)) (MParamF l init :: kk)
      // The read: ONE lookup, no walk. This is what moving cells into E buys,
      // and it is the whole of the transition. The `PromptF` branch is
      // unreachable for the same reason the `ParamF` branch above is.
      | ReadP l ->
          (match E.lookup w (VarKey l) with
            | None -> MStuck var_eff l
            | Some ev ->
              (match ev.E.prompt with
                | PromptF _ _ -> MStuck var_eff l
                | ParamF _ y -> MStep (Var y) w kk))
      | WriteP l y ->
          (match mset_param_fast l y w kk with
            | None -> MStuck var_eff l
            | Some (w', kk') -> MStep (Var y) w' kk')

(* ------------------------------------------------------------------ *)
(*  6.  Reference-side facts about `find_prompt`                        *)
(*                                                                     *)
(*  `find_prompt` recurses structurally, so its two equations -- skip a *)
(*  frame that does not handle, stop at a matching `PromptF` -- hold by  *)
(*  unfolding, captured segment included. That is what the fused         *)
(*  `msplit` needs: it builds the captured segment as it walks, so       *)
(*  agreeing with `find_prompt` means agreeing on all three components.  *)
(* ------------------------------------------------------------------ *)

let fp_same (#v #cl: Type) (o1 o2: option (stack v cl & cl & stack v cl)) : prop =
  match o1, o2 with
  | None, None -> True
  | Some (_, c1, b1), Some (_, c2, b2) -> c1 == c2 /\ b1 == b2
  | _ -> False

(** **A bind frame is transparent to the search.** *)
let fp_bind (#v #cl: Type) (eff op: string) (fn: v -> comp_tree v cl) (k: stack v cl)
  : Lemma (fp_same (find_prompt eff op (BindF fn :: k)) (find_prompt eff op k))
  = ()

(** **A parameter frame is transparent to the search too.** *)
let fp_param (#v #cl: Type) (eff op: string) (l: string) (x: v) (k: stack v cl)
  : Lemma (fp_same (find_prompt eff op (ParamF l x :: k)) (find_prompt eff op k))
  = ()

(** **A prompt that handles the action stops the search there.** *)
let fp_prompt_hit
    (#v #cl: Type) (eff op: string)
    (hs: handlers cl) (ret: option (v -> comp_tree v cl)) (k: stack v cl)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures
        find_prompt eff op (PromptF hs ret :: k)
          == Some ([PromptF hs ret], Some?.v (lookup_clause hs eff op), k))
  = ()

(**
 * **A captured segment finds its own prompt, on whatever is stacked below it.**
 * `find_prompt` reads only the frames down to the prompt it stops at, so
 * replacing everything below that prompt leaves the search's first two
 * components alone and hands back the replacement as the third. This is what
 * makes `mrepl` -- which does exactly that replacement, on the machine side --
 * erase to the stack the reference machine has.
 *)
let rec fp_cap_append (#v #cl: Type) (eff op: string) (k: stack v cl) (x: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures
        (let Some (cap, c, _) = find_prompt eff op k in
         find_prompt eff op (cap @ x) == Some (cap, c, x)))
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs ret :: rest ->
        (match lookup_clause hs eff op with
          | Some _ -> ()
          | None -> fp_cap_append eff op rest x)
    | _ :: rest -> fp_cap_append eff op rest x

(** **A prompt that does not is transparent too.** *)
let fp_prompt_miss
    (#v #cl: Type) (eff op: string)
    (hs: handlers cl) (ret: option (v -> comp_tree v cl)) (k: stack v cl)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures fp_same (find_prompt eff op (PromptF hs ret :: k)) (find_prompt eff op k))
  = ()

(* ------------------------------------------------------------------ *)
(*  7.  Environment / stack correspondence                             *)
(* ------------------------------------------------------------------ *)

(** **Extending respects `equiv`.** *)
let extend_equiv (#v #cl: Type) (w1 w2: menv v cl) (ks: keyset) (x: pd v cl)
  : Lemma (requires w1 `E.equiv` w2) (ensures E.extend w1 ks x `E.equiv` E.extend w2 ks x)
  = ()

(** **Popping a prompt pops exactly one level.** *)
let pop_env_agrees
    (#v #cl: Type) (w: menv v cl)
    (hs: handlers (clause cl)) (ret: option (v -> ct v cl)) (k: rstack v cl)
  : Lemma
      (requires w `E.equiv` env_of_stack (PromptF hs ret :: k))
      (ensures pop_env w `E.equiv` env_of_stack k)
  = let lvl : E.level (pd v cl) =
      { E.keys = keyset_view (keys hs); E.payload = (PromptF hs ret <: pd v cl) } in
    assert (env_of_stack (PromptF hs ret :: k)
            == E.extend (env_of_stack k) (keys hs) (PromptF hs ret <: pd v cl));
    assert (E.levels (env_of_stack (PromptF hs ret :: k))
            == lvl :: E.levels (env_of_stack k));
    assert (E.levels w == lvl :: E.levels (env_of_stack k));
    assert (E.depth w == length (E.levels w));
    assert (E.depth w > 0)

(** **Popping a cell pops exactly one level too.** The counterpart of the above
    for the frame that carries a `label -> value` binding rather than a handler
    table, and the reason the `Var` rule pops at an `MParamF`: a cell is a level
    now, so leaving its frame must leave its level or the environment would
    outlive the binder. *)
let pop_env_agrees_param
    (#v #cl: Type) (w: menv v cl) (l: string) (y: v) (k: rstack v cl)
  : Lemma
      (requires w `E.equiv` env_of_stack (ParamF l y :: k))
      (ensures pop_env w `E.equiv` env_of_stack k)
  = let lvl : E.level (pd v cl) =
      { E.keys = keyset_view (var_keyset l); E.payload = (ParamF l y <: pd v cl) } in
    assert (env_of_stack (ParamF l y :: k)
            == E.extend (env_of_stack k) (var_keyset l) (ParamF l y <: pd v cl));
    assert (E.levels (env_of_stack (ParamF l y :: k))
            == lvl :: E.levels (env_of_stack k));
    assert (E.levels w == lvl :: E.levels (env_of_stack k));
    assert (E.depth w == length (E.levels w));
    assert (E.depth w > 0)

(** **Splicing a segment on and re-deriving from the bottom agree.** *)
let rec mreinstall_agrees (#v #cl: Type) (k1 k2: rstack v cl)
  : Lemma (ensures env_of_stack (k1 @ k2) == mreinstall (env_of_stack k2) k1) (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> mreinstall_agrees r k2

(** **Two stacks offering the same environment go on doing so under a common
    prefix.** `env_of_stack` reads the prefix and the environment of the tail,
    and nothing else about the tail. *)
let env_of_stack_append_congr (#v #cl: Type) (pre x y: rstack v cl)
  : Lemma (requires env_of_stack x == env_of_stack y)
          (ensures env_of_stack (pre @ x) == env_of_stack (pre @ y))
  = mreinstall_agrees pre x;
    mreinstall_agrees pre y

(**
 * **A write moves no prompt** -- but it does move a cell, and a cell is now a
 * level, so the environment a `WriteP` leaves behind is NOT the one it found.
 *
 * This is the hazard the whole of section 5b is built around: `E.equiv` compares
 * `E.levels`, a level carries its payload, and a cell's payload is its value, so
 * changing a cell changes `levels` at that level and `config_ok` has to be
 * re-established rather than carried. What survives of the old reading is the
 * statement below -- the *shape* of the environment is untouched, level for
 * level and key for key, and only the payload of the one cell moves -- which is
 * why nothing about dispatch has to be reproved.
 *
 * *What replaced it.* Nothing states the relation between the two
 * environments, because nothing needs it: `mset_param` produces the new one by
 * the same recursion that produces the new stack, and `mset_param_agrees` says
 * it is the environment the new stack offers -- which is the only thing
 * `config_ok` ever asks. A lemma relating it to the old one would be a lemma
 * about a value no transition holds.
 *)

(** **Re-deriving respects `equiv`**, so the machine may reinstall onto its own
    environment rather than onto one rebuilt from the stack. *)
let rec mreinstall_equiv (#v #cl: Type) (w1 w2: menv v cl) (k: rstack v cl)
  : Lemma (requires w1 `E.equiv` w2)
          (ensures mreinstall w1 k `E.equiv` mreinstall w2 k)
          (decreases k)
  = match k with
    | [] -> ()
    | _ :: r -> mreinstall_equiv w1 w2 r

(* ------------------------------------------------------------------ *)
(*  8.  The erasure and splicing                                       *)
(* ------------------------------------------------------------------ *)

(** **Injected reference frames erase back to themselves**, and the erasure
    distributes over the splice. *)
let rec erase_inj_append (#v #cl: Type) (k1: rstack v cl) (kk: mstack v cl)
  : Lemma
      (ensures
        (match erase_k kk with
          | None -> erase_k (inj_k k1 @ kk) == None
          | Some k -> erase_k (inj_k k1 @ kk) == Some (k1 @ k)))
      (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> erase_inj_append r kk

(** **Splicing preserves the invariant**: injected frames are never `MEnvF`, so
    they carry no obligation of their own, and the frames below are untouched. *)
let rec stack_ok_inj_append (#v #cl: Type) (k1: rstack v cl) (kk: mstack v cl)
  : Lemma (requires stack_ok kk) (ensures stack_ok (inj_k k1 @ kk)) (decreases k1)
  = match k1 with
    | [] -> ()
    | _ :: r -> stack_ok_inj_append r kk

(* ------------------------------------------------------------------ *)
(*  9.  Dispatch: evidence answers what the stack walk answers          *)
(* ------------------------------------------------------------------ *)

(** **What a lookup in `env_of_stack k` must agree with**: the clause and the
    context `find_prompt` finds on `k`. Named so that no `match` appears in the
    statement of a lemma. *)
let lookup_find_ok (#v #cl: Type) (eff op: string) (k: rstack v cl) : GTot prop =
  match E.lookup (env_of_stack k) (OpKey eff op), find_prompt eff op k with
  | None, None -> True
  | Some ev, Some (cap, c, below) ->
      PromptF? ev.E.prompt /\
      lookup_clause (PromptF?.hs ev.E.prompt) eff op == Some c /\
      ev.E.below `E.equiv` env_of_stack below
  | _ -> False

let rec lookup_find (#v #cl: Type) (eff op: string) (k: rstack v cl)
  : Lemma (ensures lookup_find_ok eff op k) (decreases k)
  = match k with
    | [] -> E.lookup_empty #(pd v cl) (OpKey eff op)
    | ParamF l x :: r ->
        // A cell binds one `VarKey`, so it is transparent to a dispatch --
        // which is what the two constructors of `key` were introduced for, and
        // is why this branch is a `miss` and not a case analysis.
        E.lookup_extend_miss (env_of_stack r) (var_keyset l) (ParamF l x <: pd v cl)
          (OpKey eff op);
        lookup_find eff op r;
        fp_param eff op l x r
    | BindF fn :: r ->
        lookup_find eff op r;
        fp_bind eff op fn r
    | PromptF hs ret :: r ->
        let w = env_of_stack r in
        keys_correct hs eff op;
        (match lookup_clause hs eff op with
          | Some _ ->
              E.lookup_extend_hit w (keys hs) (PromptF hs ret <: pd v cl) (OpKey eff op);
              fp_prompt_hit eff op hs ret r
          | None ->
              E.lookup_extend_miss w (keys hs) (PromptF hs ret <: pd v cl) (OpKey eff op);
              lookup_find eff op r;
              fp_prompt_miss eff op hs ret r)

(**
 * **What a cell lookup in `env_of_stack k` must agree with**: the value
 * `find_param` reads off the stack, and the payload really is the cell's frame.
 * Named so that no `match` appears in the statement of a lemma.
 *)
let lookup_param_ok (#v #cl: Type) (l: string) (k: rstack v cl) : GTot prop =
  match E.lookup (env_of_stack k) (VarKey l), find_param l k with
  | None, None -> True
  | Some ev, Some y -> ev.E.prompt == (ParamF l y <: pd v cl)
  | _ -> False

(**
 * **The environment answers the cell read.** The counterpart of `lookup_find`
 * for E's other role, and the whole justification of `mstep`'s `ReadP`: the
 * innermost level binding `VarKey l` carries the frame `find_param` would have
 * walked to.
 *
 * Every frame that is not that cell is transparent, and for three different
 * reasons: a `BindF` installs no level at all; a `ParamF` with another label
 * binds another `VarKey`; and a `PromptF` binds no `VarKey` whatever its table
 * says, which is `keys_no_var` and is the fact the sorted key type exists to
 * supply. Without it a handler declaring an operation under the reserved effect
 * name would shadow a cell here, and this lemma -- which is quantified over
 * every stack, `Hoop.Runtime.WellScopedness` not being in scope -- would be
 * false.
 *)
let rec lookup_param_find (#v #cl: Type) (l: string) (k: rstack v cl)
  : Lemma (ensures lookup_param_ok l k) (decreases k)
  = match k with
    | [] -> E.lookup_empty #(pd v cl) (VarKey l)
    | BindF fn :: r -> lookup_param_find l r
    | ParamF l' y :: r ->
        let w = env_of_stack r in
        if l' = l
        then E.lookup_extend_hit w (var_keyset l') (ParamF l' y <: pd v cl) (VarKey l)
        else
          (E.lookup_extend_miss w (var_keyset l') (ParamF l' y <: pd v cl) (VarKey l);
           lookup_param_find l r)
    | PromptF hs ret :: r ->
        keys_no_var hs l;
        E.lookup_extend_miss (env_of_stack r) (keys hs) (PromptF hs ret <: pd v cl) (VarKey l);
        lookup_param_find l r

(* ------------------------------------------------------------------ *)
(*  10.  The machine split is the reference split                     *)
(* ------------------------------------------------------------------ *)

(**
 * **What the fused split must agree with**: all three components of
 * `find_prompt` on the erased stack. The captured segment is part of the claim
 * -- `msplit` produces it rather than reading it off an erasure -- and it is
 * claimed to be *equal*, not merely pointwise equal, so the clause this
 * machine invokes and the clause the reference machine invokes are literally the
 * same term.
 *)
let msplit_ok (#v #cl: Type) (eff op: string) (kk: mstack v cl) (k: rstack v cl) : GTot prop =
  match msplit eff op kk, find_prompt eff op k with
  | None, None -> True
  | Some (cap, b), Some (cap', _, below) ->
      cap == cap' /\ stack_ok b /\ erase_k b == Some below
  | _ -> False

(**
 * **The central structural lemma.** Walking the machine stack -- jumping over
 * the region an `MEnvF` masks -- captures the erasure of what `find_prompt`
 * captures and lands on the erasure of what it lands on. This is where the
 * invariant "the `MEnvF`'s prompt sits below it inside the same segment" is
 * spent: without it `erase_k r` would be `None` and the masked region would have
 * no boundary to jump to.
 *)
let rec msplit_agrees (#v #cl: Type) (eff op: string) (kk: mstack v cl) (k: rstack v cl)
  : Lemma
      (requires stack_ok kk /\ erase_k kk == Some k)
      (ensures msplit_ok eff op kk k)
      (decreases (length kk))
  = match kk with
    | [] -> ()
    | MParamF l x :: r ->
        let Some kr = erase_k r in
        msplit_agrees eff op r kr
    | MBindF fn :: r ->
        let Some kr = erase_k r in
        msplit_agrees eff op r kr
    | MPromptF hs ret :: r ->
        let Some kr = erase_k r in
        (match lookup_clause hs eff op with
          | Some _ -> fp_prompt_hit eff op hs ret kr
          | None -> msplit_agrees eff op r kr)
    | MEnvF e' o' sv :: r ->
        let Some kr = erase_k r in
        msplit_agrees e' o' r kr;
        (match msplit e' o' r with
          | None -> ()
          | Some (cap', mrest) ->
            let Some (cap'', _, mrest_r) = find_prompt e' o' kr in
            assert (cap' == cap'');
            assert (erase_k mrest == Some mrest_r);
            assert (k == BindF (kont_of cap') :: mrest_r);
            msplit_agrees eff op mrest mrest_r)

(* ------------------------------------------------------------------ *)
(*  10a.  The machine's cell operations are the reference's            *)
(*                                                                     *)
(*  Three lemmas, and the third is the one with content: it must show  *)
(*  that rebuilding the machine stack around a masked region erases to *)
(*  `set_param` on the reference stack -- which needs the region's own  *)
(*  erasure to come back unchanged, and that is `mrepl_agrees`.         *)
(* ------------------------------------------------------------------ *)

(** **A read finds what the reference machine finds.** The `MEnvF` branch is
    where the masking is spent: `msplit` lands on the erasure of what
    `find_prompt` lands on, and the reference stack there has the captured
    segment replaced by a single `BindF`, which holds no cell. *)
let rec mfind_param_agrees (#v #cl: Type) (l: string) (kk: mstack v cl) (k: rstack v cl)
  : Lemma
      (requires stack_ok kk /\ erase_k kk == Some k)
      (ensures mfind_param l kk == find_param l k)
      (decreases (length kk))
  = match kk with
    | [] -> ()
    | MParamF l' x :: r ->
        if l' = l then ()
        else (let Some kr = erase_k r in mfind_param_agrees l r kr)
    | MBindF fn :: r -> let Some kr = erase_k r in mfind_param_agrees l r kr
    | MPromptF hs ret :: r -> let Some kr = erase_k r in mfind_param_agrees l r kr
    | MEnvF e o sv :: r ->
        let Some kr = erase_k r in
        msplit_agrees e o r kr;
        (match msplit e o r with
          | None -> ()
          | Some (_, b) ->
            let Some kb = erase_k b in
            mfind_param_agrees l b kb)

(** **What replacing below a split point must produce**: the captured segment,
    unchanged, on top of the erasure of the replacement -- and the environment
    that stack offers. Named so that no `match` appears in the statement of a
    lemma. *)
let mrepl_ok
    (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl)
    (wb': menv v cl) (b': mstack v cl) (kb': rstack v cl)
  : GTot prop
  = match msplit eff op kk with
    | None -> True
    | Some (cap, _) ->
      (match mrepl eff op w kk wb' b' with
        | None -> False
        | Some (w', kk') ->
            stack_ok kk' /\ erase_k kk' == Some (cap @ kb') /\
            w' `E.equiv` env_of_stack (cap @ kb'))

(**
 * **Putting an `MEnvF` back on a rebuilt tail.** Both walks below rebuild the
 * frames under an `MEnvF` and then have to re-establish two things about the
 * frame itself: that its prompt is still below it -- which it is, because the
 * rebuild kept the captured segment and only replaced what lay under it -- and
 * that the environment it saved is the environment the frames below it offer.
 *
 * The second used to be discharged by observing that a write moves no level, so
 * the old `sv` still did. It does not: a cell IS a level. So the frame is
 * rebuilt with the environment the recursive call handed back, and this lemma
 * simply takes that as a hypothesis -- which is why it no longer needs
 * `find_prompt_partitions` or `env_of_stack_append_congr`. The obligation moved
 * from here to the caller, where the value that discharges it is in hand.
 *)
let envf_rebuild
    (#v #cl: Type) (e o: string) (sv': menv v cl)
    (r': mstack v cl) (kr: rstack v cl)
    (cap below x: rstack v cl) (c: clause cl)
  : Lemma
      (requires
        find_prompt e o kr == Some (cap, c, below) /\
        stack_ok r' /\ erase_k r' == Some (cap @ x) /\
        sv' `E.equiv` env_of_stack (cap @ x))
      (ensures
        stack_ok (MEnvF e o sv' :: r') /\
        erase_k (MEnvF e o sv' :: r') == Some (BindF (kont_of cap) :: x))
  = fp_cap_append e o kr x

(**
 * **The rebuild is invisible to the erasure**, above the split point, and
 * produces the environment the rebuilt stack offers. Shaped like
 * `msplit_agrees`: it walks the machine stack, spends the `MEnvF` invariant to
 * give the masked region a boundary, and recurses twice there -- once past the
 * region to reach the replacement, once back over the region to put it on the
 * new tail.
 *)
let rec mrepl_agrees
    (#v #cl: Type) (eff op: string)
    (w: menv v cl) (kk: mstack v cl) (k: rstack v cl)
    (wb': menv v cl) (b': mstack v cl) (kb': rstack v cl)
  : Lemma
      (requires
        stack_ok kk /\ erase_k kk == Some k /\ w `E.equiv` env_of_stack k /\
        stack_ok b' /\ erase_k b' == Some kb' /\ wb' `E.equiv` env_of_stack kb')
      (ensures mrepl_ok eff op w kk wb' b' kb')
      (decreases %[length kk; 1])
  = match kk with
    | [] -> ()
    | MBindF fn :: r ->
        let Some kr = erase_k r in
        mrepl_agrees eff op w r kr wb' b' kb'
    | MParamF l y :: r ->
        let Some kr = erase_k r in
        pop_env_agrees_param w l y kr;
        mrepl_agrees eff op (pop_env w) r kr wb' b' kb'
    | MPromptF hs ret :: r ->
        (match lookup_clause hs eff op with
          | Some _ -> ()
          | None ->
            let Some kr = erase_k r in
            pop_env_agrees w hs ret kr;
            mrepl_agrees eff op (pop_env w) r kr wb' b' kb')
    | MEnvF e' o' sv :: r -> mrepl_agrees_envf eff op w e' o' sv r k wb' b' kb'

(** The `MEnvF` branch, split off so that it is a query of its own: it is the
    only branch that recurses twice, and the only one that has to re-establish
    the frame's own invariant afterwards. *)
and mrepl_agrees_envf
    (#v #cl: Type) (eff op: string) (w: menv v cl)
    (e' o': string) (sv: menv v cl)
    (r: mstack v cl) (k: rstack v cl)
    (wb': menv v cl) (b': mstack v cl) (kb': rstack v cl)
  : Lemma
      (requires
        stack_ok (MEnvF e' o' sv :: r) /\ erase_k (MEnvF e' o' sv :: r) == Some k /\
        w `E.equiv` env_of_stack k /\
        stack_ok b' /\ erase_k b' == Some kb' /\ wb' `E.equiv` env_of_stack kb')
      (ensures mrepl_ok eff op w (MEnvF e' o' sv :: r) wb' b' kb')
      (decreases %[length (MEnvF e' o' sv :: r); 0])
  = let Some kr = erase_k r in
    msplit_agrees e' o' r kr;
    let Some (cap1, mrest) = msplit e' o' r in
    let Some (_, c1, below1) = find_prompt e' o' kr in
    match msplit eff op mrest with
    | None -> ()
    | Some (cap2, b) ->
      msplit_agrees eff op mrest below1;
      // `k` is `BindF (kont_of cap1) :: below1`, and a bind installs no level,
      // so the environment the frame offers is the one `mrest` offers.
      mrepl_agrees eff op w mrest below1 wb' b' kb';
      let Some (wm', mrest') = mrepl eff op w mrest wb' b' in
      // Back over the masked region, on the rebuilt tail. The `MEnvF`'s own
      // saved environment comes out of this call, which is the only place it
      // can: it describes `cap1 @ below1`, and only this walk knows `cap1`.
      mrepl_agrees e' o' sv r kr wm' mrest' (cap2 @ kb');
      let Some (sv', r') = mrepl e' o' sv r wm' mrest' in
      envf_rebuild e' o' sv' r' kr cap1 below1 (cap2 @ kb') c1

(** **What a write must produce**: the erasure of the rebuilt machine stack is
    the reference machine's rebuilt stack, the invariant survives, and the
    environment handed back is the one that stack offers. *)
let mset_param_ok
    (#v #cl: Type) (l: string) (x: v)
    (w: menv v cl) (kk: mstack v cl) (k: rstack v cl)
  : GTot prop
  = match mset_param l x w kk, set_param l x k with
    | None, None -> True
    | Some (w', kk'), Some k' ->
        stack_ok kk' /\ erase_k kk' == Some k' /\ w' `E.equiv` env_of_stack k'
    | _ -> False

(**
 * **A write does on the machine what it does on the reference machine.**
 *
 * Split into a mutually recursive pair for the same reason `mrepl_agrees` is:
 * the `MEnvF` branch carries a context nothing else in the walk needs -- a
 * split, a rebuild over the masked region and the frame's own invariant -- and
 * asking the solver for it together with the four easy branches is one query
 * large enough to be worth an option. Ordering the two by `%[length kk; 1]` and
 * `%[length kk; 0]` makes the branch a query of its own without one.
 *)
let rec mset_param_agrees
    (#v #cl: Type) (l: string) (x: v)
    (w: menv v cl) (kk: mstack v cl) (k: rstack v cl)
  : Lemma
      (requires stack_ok kk /\ erase_k kk == Some k /\ w `E.equiv` env_of_stack k)
      (ensures mset_param_ok l x w kk k)
      (decreases %[length kk; 1])
  = match kk with
    | [] -> ()
    | MParamF l' y :: r ->
        let Some kr = erase_k r in
        pop_env_agrees_param w l' y kr;
        if l' = l then () else mset_param_agrees l x (pop_env w) r kr
    | MBindF fn :: r ->
        let Some kr = erase_k r in
        mset_param_agrees l x w r kr
    | MPromptF hs ret :: r ->
        let Some kr = erase_k r in
        pop_env_agrees w hs ret kr;
        mset_param_agrees l x (pop_env w) r kr
    | MEnvF e o sv :: r -> mset_param_agrees_envf l x w e o sv r k

(** The `MEnvF` branch of the write, as its own query: the cell is below the
    masked region, so the walk lands beneath the region's prompt, writes there,
    and comes back up through the region -- which is the one place a write has
    to rebuild an `MEnvF`, saved environment included. *)
and mset_param_agrees_envf
    (#v #cl: Type) (l: string) (x: v) (w: menv v cl)
    (e o: string) (sv: menv v cl) (r: mstack v cl) (k: rstack v cl)
  : Lemma
      (requires
        stack_ok (MEnvF e o sv :: r) /\ erase_k (MEnvF e o sv :: r) == Some k /\
        w `E.equiv` env_of_stack k)
      (ensures mset_param_ok l x w (MEnvF e o sv :: r) k)
      (decreases %[length (MEnvF e o sv :: r); 0])
  = let Some kr = erase_k r in
    msplit_agrees e o r kr;
    let Some (cap1, b) = msplit e o r in
    let Some (_, c1, below1) = find_prompt e o kr in
    mset_param_agrees l x w b below1;
    match mset_param l x w b with
    | None -> ()
    | Some (wb', b') ->
      let Some below1' = set_param l x below1 in
      mrepl_agrees e o sv r kr wb' b' below1';
      let Some (sv', r') = mrepl e o sv r wb' b' in
      envf_rebuild e o sv' r' kr cap1 below1 below1' c1

(* ------------------------------------------------------------------ *)
(*  11.  What the reference machine does in two steps                   *)
(*                                                                     *)
(*  The two places where one machine transition is two reference      *)
(*  transitions. Both are consequences of the desugaring: a fast        *)
(*  clause reads as `Op (body args) k`, so the reference has to build    *)
(*  the `Op` node and then push its bind frame; and it returns through   *)
(*  that bind frame by splicing the segment the machine never  *)
(*  removed.                                                            *)
(* ------------------------------------------------------------------ *)

(**
 * **The `Perform` rule, restated with the clause exposed.** Only a restatement
 * of `Hoop.Runtime.Metatheory.step_perform`, but the *shape* is what matters:
 * the continuation is written the way `Hoop.Runtime.Semantics.step` writes it,
 * so F* gives the two the same SMT symbol.
 *)
let ref_perform_shape
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            step (desugar af afast) (Step (Perform eff op payload) k)
              == Step (desugar af afast clause payload (kont_of captured)) below))
  = MT.step_perform eff op payload k (desugar af afast)

(** **A full clause runs in one reference step**, with the desugaring resolved
    here rather than at the call site. *)
let ref_full_one
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            steps (desugar af afast) 1 (Step (Perform eff op payload) k)
              == Step (desugar af afast clause payload (kont_of captured)) below))
  = match find_prompt eff op k with
    | None -> ()
    | Some (captured, clause, below) ->
      assert (handled_in eff op k);
      assert (steps (desugar af afast) 1 (Step (Perform eff op payload) k)
              == step (desugar af afast) (Step (Perform eff op payload) k));
      MT.step_perform eff op payload k (desugar af afast)

(** **Entering a fast clause body.** `Perform` then `Op`. *)
let ref_fast_two
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (k: rstack v cl)
  : Lemma
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            (match clause with
              | Full _ -> True
              | Fast c0 ->
                steps (desugar af afast) 2 (Step (Perform eff op payload) k)
                  == Step (afast c0 payload) (BindF (kont_of captured) :: below))))
  = match find_prompt eff op k with
    | None -> ()
    | Some (captured, clause, below) ->
      assert (handled_in eff op k);
      ref_perform_shape af afast eff op payload k

(** **Leaving a fast clause body.** The reference applies the ctl clause's
    continuation, which is a `Resumed` node, and then splices the segment back on
    -- landing on exactly the stack the machine never took apart. *)
let ref_envf_two
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (value: v) (k: rstack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
        (match find_prompt eff op k with
          | None -> True
          | Some (captured, clause, below) ->
            steps (desugar af afast) 2
              (Step (Var value) (BindF (kont_of captured) :: below))
              == Step (Var value) k))
  = MT.find_prompt_partitions eff op k

(* ------------------------------------------------------------------ *)
(*  12.  The simulation                                                *)
(* ------------------------------------------------------------------ *)

(**
 * **What one machine transition must be**: one *or two* reference
 * transitions, and again a configuration satisfying the invariant.
 *
 * *Never zero.* The machine is a contraction of the reference, not an
 * expansion of it. The two transitions it collapses are exactly the two the
 * desugaring of a fast clause introduces -- `Perform` builds the `Op` node, `Op`
 * pushes its bind frame -- and the two the return through that bind frame costs
 * -- apply the ctl continuation, splice the segment back on. There is therefore
 * no stuttering to rank and no measure to exhibit.
 *
 * *No lambda is written out here, deliberately.* Both sides mention the
 * continuation only through `erase_st` and `steps`, each of which builds it
 * under a `match` on `find_prompt eff op k`. Naming it in the statement would
 * close it over a fresh local binder instead, making it an unrelated SMT symbol.
 *)
let sim_ok (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) : GTot prop =
  Some? (erase_st q) /\
  config_ok (mstep af afast q) /\
  (exists (n: nat).
    (n == 1 \/ n == 2) /\
    erase_st (mstep af afast q)
      == Some (steps (desugar af afast) n (Some?.v (erase_st q))))

(**
 * **The simulation at a `Perform`**, split out so that each of the three
 * dispatch outcomes is proved in a context holding nothing but this transition.
 *
 *   - unhandled: the environment misses exactly when `find_prompt` misses, so
 *     both machines stop. One reference step.
 *   - `Fast`: the body starts running in place under the handler's own
 *     environment, with an `MEnvF` recording the perform site's. Nothing is
 *     captured and the stack is not cut. The reference needs two steps to reach
 *     the same configuration, and the new machine stack erases to exactly what
 *     the reference then has -- which is the point of the whole design.
 *   - `Full`: the existing path, one reference step, exact agreement.
 *)
let msim_perform
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (eff op: string) (payload: list v) (w: menv v cl) (kk: mstack v cl)
  : Lemma
      (requires config_ok (MStep (Perform eff op payload) w kk))
      (ensures sim_ok af afast (MStep (Perform eff op payload) w kk))
  = let apply = desugar af afast in
    let q : mstate v cl = MStep (Perform eff op payload) w kk in
    let Some k = erase_k kk in
    lookup_find eff op k;
    E.lookup_equiv w (env_of_stack k) (OpKey eff op);
    match E.lookup w (OpKey eff op) with
    | None ->
        MT.step_perform_stuck eff op payload k apply;
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | Some ev ->
      assert (handled_in eff op k);
      // `lookup_find` says the payload is a prompt -- a cell binds a `VarKey`
      // and this is an `OpKey` -- so `mstep`'s `ParamF` branch is dead.
      assert (PromptF? ev.E.prompt);
      (match lookup_clause (PromptF?.hs ev.E.prompt) eff op with
        | None -> ()
        | Some (Fast c0) ->
            ref_fast_two af afast eff op payload k;
            introduce exists (n: nat).
              (n == 1 \/ n == 2) /\
              erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
            with 2 and ()
        | Some (Full c0) ->
            ref_full_one af afast eff op payload k;
            msplit_agrees eff op kk k;
            introduce exists (n: nat).
              (n == 1 \/ n == 2) /\
              erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
            with 1 and ())

(** **The simulation, one transition.** The main theorem. *)
let msim (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl)
  : Lemma (requires config_ok q) (ensures sim_ok af afast q)
  = let apply = desugar af afast in
    match q with
    | MDone x ->
        MT.steps_terminal apply 1 (Done x <: rstate v cl);
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | MStuck e o ->
        MT.steps_terminal apply 1 (Stuck e o <: rstate v cl);
        introduce exists (n: nat).
          (n == 1 \/ n == 2) /\
          erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
        with 1 and ()
    | MStep c w kk ->
      let Some k = erase_k kk in
      let s : rstate v cl = Step c k in
      assert (steps apply 1 s == step apply s);
      match c with
      | Perform eff op payload -> msim_perform af afast eff op payload w kk
      | Op comp fn ->
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Handle hs ret body ->
          extend_equiv w (env_of_stack k) (keys hs) (PromptF hs ret <: pd v cl);
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Resumed kont value ->
          erase_inj_append kont kk;
          stack_ok_inj_append kont kk;
          mreinstall_agrees kont k;
          mreinstall_equiv w (env_of_stack k) kont;
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | NewP l init body ->
          extend_equiv w (env_of_stack k) (var_keyset l) (ParamF l init <: pd v cl);
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | ReadP l ->
          lookup_param_find l k;
          E.lookup_equiv w (env_of_stack k) (VarKey l);
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | WriteP l y ->
          mset_param_agrees l y w kk k;
          introduce exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with 1 and ()
      | Var value ->
          (match kk with
            | [] ->
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MBindF fn :: r ->
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MParamF l x :: r ->
                let Some kr = erase_k r in
                pop_env_agrees_param w l x kr;
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MPromptF hs ret :: r ->
                let Some kr = erase_k r in
                pop_env_agrees w hs ret kr;
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 1 and ()
            | MEnvF eff op sv :: r ->
                let Some kr = erase_k r in
                ref_envf_two af afast eff op value kr;
                introduce exists (n: nat).
                  (n == 1 \/ n == 2) /\
                  erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
                with 2 and ())

(* ------------------------------------------------------------------ *)
(*  13.  Whole runs                                                     *)
(* ------------------------------------------------------------------ *)

(**
 * **The `Full` branch of `mstep` really is a direct call to the FFI's full
 * interpreter**: `mstep` writes `af c0 payload (kont_of captured)`, so no
 * dispatch survives extraction. The reference machine goes through `desugar`,
 * and this is the equation that makes the two readings agree.
 *)
let full_branch_is_af
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (c0: cl) (payload: list v) (kf: v -> ct v cl)
  : Lemma (desugar af afast (Full c0) payload kf == af c0 payload kf)
  = ()

(** **Loading a program.** The empty environment is the environment of the empty
    stack, so the invariant holds at the start, and the erasure is the reference
    machine's own initial state. *)
let mload (#v #cl: Type) (p: ct v cl)
  : Tot (q: mstate v cl { config_ok q /\ erase_st q == Some (load p) })
  = MStep p E.empty []

(**
 * **The fuel-bounded iteration of `mstep`**, the counterpart of
 * `Hoop.Runtime.Semantics.steps`. `Tot` rather than `GTot` so that the
 * normaliser can run it -- `Hoop.Runtime.Test` does, to check that the two
 * machines really do agree on a program and not merely that they are proved to;
 * `noextract` because the runtime iterates through `mrun`, which needs no fuel.
 *)
noextract
let rec msteps
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (fuel: nat)
    (q: mstate v cl)
  : Tot (mstate v cl) (decreases fuel)
  = if fuel = 0
    then q
    else
      match q with
      | MDone _ -> q
      | MStuck _ _ -> q
      | MStep _ _ _ -> msteps af afast (fuel - 1) (mstep af afast q)

(** **Convergence of the reference machine**, restated here because
    `Hoop.Runtime.Laws` deliberately has an empty interface. Identical to
    `Hoop.Runtime.Laws.converges`. *)
let rconverges (#v #cl: Type) (apply: apply_t v cl) (s: state v cl) (x: v) : GTot prop =
  exists (n: nat). steps apply n s == Done x

(** **Convergence of the machine.** *)
let mconverges
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) (x: v)
  : GTot prop
  = exists (n: nat). msteps af afast n q == MDone x

(** **The invariant is preserved by any number of transitions**, and the erased
    run is a run of the reference machine. *)
let rec msteps_agrees
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (fuel: nat) (q: mstate v cl)
  : Lemma
      (requires config_ok q)
      (ensures
        config_ok (msteps af afast fuel q) /\
        Some? (erase_st q) /\
        (exists (n: nat).
          erase_st (msteps af afast fuel q)
            == Some (steps (desugar af afast) n (Some?.v (erase_st q)))))
      (decreases fuel)
  = let apply = desugar af afast in
    if fuel = 0
    then
      introduce exists (n: nat).
        erase_st q == Some (steps apply n (Some?.v (erase_st q)))
      with 0 and ()
    else
      match q with
      | MDone _ | MStuck _ _ ->
          introduce exists (n: nat).
            erase_st q == Some (steps apply n (Some?.v (erase_st q)))
          with 0 and ()
      | MStep _ _ _ ->
          msim af afast q;
          msteps_agrees af afast (fuel - 1) (mstep af afast q);
          eliminate exists (n: nat).
            (n == 1 \/ n == 2) /\
            erase_st (mstep af afast q) == Some (steps apply n (Some?.v (erase_st q)))
          with
            eliminate exists (m: nat).
              erase_st (msteps af afast (fuel - 1) (mstep af afast q))
                == Some (steps apply m (Some?.v (erase_st (mstep af afast q))))
            with
              (MT.steps_add apply n m (Some?.v (erase_st q));
               introduce exists (j: nat).
                 erase_st (msteps af afast fuel q)
                   == Some (steps apply j (Some?.v (erase_st q)))
               with (n + m) and ())

(* ------------------------------------------------------------------ *)
(*  14.  The theorem                                                    *)
(* ------------------------------------------------------------------ *)

(** **Soundness**: whatever the machine returns, the reference machine
    returns. *)
let converges_transfer
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl) (x: v)
  : Lemma
      (requires config_ok q /\ mconverges af afast q x)
      (ensures rconverges (desugar af afast) (Some?.v (erase_st q)) x)
  = let apply = desugar af afast in
    eliminate exists (n: nat). msteps af afast n q == MDone x
    with
      (msteps_agrees af afast n q;
       eliminate exists (m: nat).
         erase_st (msteps af afast n q) == Some (steps apply m (Some?.v (erase_st q)))
       with
         (introduce exists (j: nat). steps apply j (Some?.v (erase_st q)) == Done x
          with m and ()))

(**
 * **Completeness, and the absence of infinite stuttering**: whatever the
 * reference machine returns, the machine returns.
 *
 * *The measure* is the reference machine's remaining fuel. `msim` says every
 * machine transition is at least one reference transition, so the fuel
 * strictly decreases at every machine step and the recursion terminates. That
 * is the whole ranking argument; no auxiliary measure on machine
 * configurations is needed, because the machine never stutters.
 *)
let rec converges_reflect
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (fuel: nat) (q: mstate v cl) (x: v)
  : Lemma
      (requires
        config_ok q /\
        steps (desugar af afast) fuel (Some?.v (erase_st q)) == Done x)
      (ensures mconverges af afast q x)
      (decreases fuel)
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    match q with
    | MDone y ->
        MT.steps_terminal apply fuel s;
        introduce exists (n: nat). msteps af afast n q == MDone x with 0 and ()
    | MStuck e o -> MT.steps_terminal apply fuel s
    | MStep _ _ _ ->
        msim af afast q;
        eliminate exists (n: nat).
          (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
        with
          (if fuel <= n
           then
             (MT.steps_stable apply fuel (n - fuel) s;
              introduce exists (j: nat). msteps af afast j q == MDone x with 1 and ())
           else
             (MT.steps_add apply n (fuel - n) s;
              converges_reflect af afast (fuel - n) (mstep af afast q) x;
              eliminate exists (m: nat). msteps af afast m (mstep af afast q) == MDone x
              with
                (introduce exists (j: nat). msteps af afast j q == MDone x
                 with (m + 1) and ())))

(** **The theorem**: the machine and the reference machine agree on
    every program, in both directions. *)
let execute_agrees
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (p: ct v cl) (x: v)
  : Lemma
      (mconverges af afast (mload p) x <==> rconverges (desugar af afast) (load p) x)
  = introduce mconverges af afast (mload p) x ==> rconverges (desugar af afast) (load p) x
    with converges_transfer af afast (mload p) x;
    introduce rconverges (desugar af afast) (load p) x ==> mconverges af afast (mload p) x
    with
      (eliminate exists (n: nat). steps (desugar af afast) n (load p) == Done x
       with converges_reflect af afast n (mload p) x)

(* ------------------------------------------------------------------ *)
(*  15.  Progress                                                       *)
(* ------------------------------------------------------------------ *)

(** **Stuck-freedom survives any number of reference transitions.** *)
let never_stuck_steps (#v #cl: Type) (apply: apply_t v cl) (n: nat) (s: state v cl)
  : Lemma (requires never_stuck apply s) (ensures never_stuck apply (steps apply n s))
  = introduce forall (m: nat). ~(Stuck? (steps apply m (steps apply n s)))
    with MT.steps_add apply n m s

(**
 * **Progress transports**: a machine configuration whose erasure the
 * reference machine never gets stuck from does not get stuck either, and neither
 * does its successor. This is what carries
 * `Hoop.Runtime.Metatheory.progress` -- and with it the whole well-scopedness
 * development -- across to the machine unchanged.
 *)
let mprogress
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl) (q: mstate v cl)
  : Lemma
      (requires config_ok q /\ never_stuck (desugar af afast) (Some?.v (erase_st q)))
      (ensures
        ~(MStuck? q) /\
        ~(MStuck? (mstep af afast q)) /\
        config_ok (mstep af afast q) /\
        Some? (erase_st (mstep af afast q)) /\
        never_stuck (desugar af afast)
          (Some?.v (erase_st (mstep af afast q))))
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    never_stuck_now apply s;
    msim af afast q;
    eliminate exists (n: nat).
      (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
    with
      (never_stuck_steps apply n s;
       assert (~(Stuck? (steps apply n s))))

(* ------------------------------------------------------------------ *)
(*  16.  The entry point                                                *)
(* ------------------------------------------------------------------ *)

(* One machine transition is one or two reference transitions, so a run that
   starts after one is a run that starts before it. The counterpart of
   `Hoop.Runtime.Semantics.one_more_step`, with the erasure interposed; kept out
   of the `Div` body below so that the driver reads as the loop it is. *)
private
let one_more_mstep
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (q: mstate v cl) (r: mstate v cl)
  : Lemma
      (requires
        config_ok q /\
        Some? (erase_st (mstep af afast q)) /\
        (exists (m: nat).
          erase_st r
            == Some (steps (desugar af afast) m (Some?.v (erase_st (mstep af afast q))))))
      (ensures
        exists (j: nat).
          erase_st r == Some (steps (desugar af afast) j (Some?.v (erase_st q))))
  = let apply = desugar af afast in
    let s = Some?.v (erase_st q) in
    msim af afast q;
    eliminate exists (n: nat).
      (n == 1 \/ n == 2) /\ erase_st (mstep af afast q) == Some (steps apply n s)
    with
      eliminate exists (m: nat).
        erase_st r == Some (steps apply m (Some?.v (erase_st (mstep af afast q))))
      with
        (MT.steps_add apply n m s;
         introduce exists (j: nat). erase_st r == Some (steps apply j s)
         with (n + m) and ())

(**
 * **The transitive closure**, evidence-driven and tail-resumptive. The only
 * non-ghost iteration of a transition in this module, and the only thing that
 * actually loops at run time.
 *
 * The postcondition is in two parts, and they rest on different assumptions.
 *
 *   - The *simulation* -- `exists n. erase_st r == Some (steps ... n ...)` --
 *     holds of any configuration satisfying the invariant, with no
 *     well-scopedness hypothesis whatever. It is `msim` closed over the loop:
 *     whatever state the machine stops in, the reference machine reaches that
 *     same state on the same input. Stopping in `MStuck` is covered by it, and
 *     says that the reference machine gets stuck there too -- so a stuck run is
 *     a genuinely unhandled operation and not a defect of this machine.
 *
 *   - *Termination in a value* -- `MDone? r` -- is what actually needs
 *     `never_stuck`, and appears guarded by it. `mprogress` is what carries it
 *     from one iteration to the next, and it is invoked only under the guard.
 *
 * Keeping the two apart is what lets `mrun` be called on a configuration
 * nothing is known about and still say something true about the answer. Under
 * `never_stuck` the guard discharges and the conjunction is exactly the older,
 * unconditional-`MDone?` reading.
 *
 * No branch names `MStuck`: it is folded into the catch-all, which is also
 * where `MDone` is returned. `runtime/ml/melange/hoop_ffi.ml` sits outside the type
 * system and hands in a state whose well-scopedness it cannot establish; the
 * catch-all returns whatever it stops at to the FFI -- which reports the
 * unhandled operation -- where an incomplete match would raise `Match_failure`.
 *)
let rec mrun
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (q: mstate v cl { config_ok q })
  : Div
      (mstate v cl)
      (requires True)
      (ensures fun r ->
        (exists (n: nat).
          erase_st r == Some (steps (desugar af afast) n (Some?.v (erase_st q)))) /\
        (never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? r))
  = match q with
    | MStep _ _ _ ->
        msim af afast q;
        let r = mrun af afast (mstep af afast q) in
        one_more_mstep af afast q r;
        introduce
          never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? r
        with mprogress af afast q;
        r
    | _ ->
        introduce exists (n: nat).
          erase_st q == Some (steps (desugar af afast) n (Some?.v (erase_st q)))
        with 0 and ();
        introduce
          never_stuck (desugar af afast) (Some?.v (erase_st q)) ==> MDone? q
        with never_stuck_now (desugar af afast) (Some?.v (erase_st q));
        q

(**
 * **The entry point the FFI calls**: the machine, loaded and iterated to a
 * value. `runtime/ml/melange/hoop_ffi.ml` calls this and nothing else; it is the whole
 * of the runtime's module boundary.
 *
 * The specification is `Hoop.Runtime.Semantics.steps`, the fuel-bounded
 * iteration of the stack-walking transition, at the desugared reading of the
 * clause table.
 *
 * **There is no precondition.** `execute` runs on any program at all, and the
 * simulation conjunct -- `exists n. erase_st r == Some (steps (desugar af
 * afast) n (load p))` -- holds of every one of them: the erasure of the result
 * is a state the reference machine reaches on that same program, pinned down
 * exactly and not merely as to its shape. This is what covers the branch the
 * FFI actually has to handle. `runtime/ml/melange/hoop_ffi.ml` supplies `p` through
 * `magic`, so it could never have discharged a precondition; with none to
 * discharge, its `MStuck` result is now within the theorem rather than outside
 * it, and the theorem says the reference machine is stuck on that program too.
 * The error it raises therefore reports a real unhandled operation.
 *
 * `MDone? r` is what genuinely needs well-scopedness, and it appears guarded by
 * it: given `never_stuck (desugar af afast) (load p)`, the guard discharges and
 * the result is a value. The standing assumption has moved from "the answer is
 * correct only if PureScript's row types guarantee well-scopedness" to "the
 * answer always agrees with the reference semantics, and PureScript's types are
 * what make `MStuck` unreachable".
 *
 * The two FFI interpreters are the only trusted inputs. `af` is a fully
 * controllable clause, handed the delimited continuation; `afast` is a
 * tail-resumptive one, which is not handed it and cannot be. Which of the two
 * applies is decided by the `clause` tag on the *table entry*, which
 * `handlers_of_js` sets once per `Handle` -- so nothing is assumed of the
 * boundary that F* cannot see.
 *)
let execute
    (#v #cl: Type)
    (af: full_t v cl)
    (afast: fast_t v cl)
    (p: ct v cl)
  : Div
      (mstate v cl)
      (requires True)
      (ensures fun r ->
        (exists (n: nat). erase_st r == Some (steps (desugar af afast) n (load p))) /\
        (never_stuck (desugar af afast) (load p) ==> MDone? r))
  = mrun af afast (mload p)

(* ------------------------------------------------------------------ *)
(*  17.  Non-vacuity: the three scenarios really occur                  *)
(*                                                                     *)
(*  `msim` quantifies over every configuration satisfying `config_ok`,  *)
(*  so it covers the three scenarios of the design -- provided such     *)
(*  configurations exist. This exhibits them, and by the machine's own  *)
(*  transition rather than by hand.                                     *)
(* ------------------------------------------------------------------ *)

(**
 * Two nested handlers: `hsf` (inner) has a *fast* clause for `(ef, opf)`, and
 * `hsg` (outer) has a *full* clause for `(eg, opg)`, which `hsf` does not
 * handle. Performing `(ef, opf)` therefore runs a fast clause body whose effects
 * belong outside its own prompt.
 *
 *   - the fast transition really fires, and really pushes an `MEnvF`
 *     (scenarios 1 and 2 -- a pure body simply returns through it, an effectful
 *     one performs from underneath it);
 *   - the resulting configuration really satisfies `config_ok`, so the `MEnvF`
 *     cases of `msim` are not vacuous;
 *   - performing `(eg, opg)` from inside that body captures the *whole* stack,
 *     the `MEnvF` included (scenario 3): the split leaves nothing behind, so the
 *     `MEnvF` is inside the captured segment and its erasure is what the
 *     reference machine receives -- exhibited here *already erased* into the
 *     `BindF (kont_of ...)` frame it becomes.
 *)
let scenarios_reachable
    (#v #cl: Type) (af: full_t v cl) (afast: fast_t v cl)
    (hsf hsg: handlers (clause cl))
    (retf retg: option (v -> ct v cl))
    (ef opf eg opg: string) (payload: list v) (cf cg: cl)
  : Lemma
      (requires
        lookup_clause hsf ef opf == Some (Fast cf) /\
        lookup_clause hsf eg opg == None /\
        lookup_clause hsg eg opg == Some (Full cg))
      (ensures
        (let k0 : rstack v cl = [PromptF hsf retf; PromptF hsg retg] in
         let kk0 : mstack v cl = [MPromptF hsf retf; MPromptF hsg retg] in
         let q0 : mstate v cl = MStep (Perform ef opf payload) (env_of_stack k0) kk0 in
         config_ok q0 /\
         (let q1 = mstep af afast q0 in
          MStep? q1 /\
          Cons? (MStep?.k q1) /\ MEnvF? (hd (MStep?.k q1)) /\
          config_ok q1 /\
          (let q2 : mstate v cl =
             MStep (Perform eg opg payload) (MStep?.w q1) (MStep?.k q1) in
           config_ok q2 /\
           msplit eg opg (MStep?.k q2)
             == Some ([BindF (kont_of [PromptF hsf retf]); PromptF hsg retg], [])))))
  = let k0 : rstack v cl = [PromptF hsf retf; PromptF hsg retg] in
    let kk0 : mstack v cl = [MPromptF hsf retf; MPromptF hsg retg] in
    let q0 : mstate v cl = MStep (Perform ef opf payload) (env_of_stack k0) kk0 in
    assert (erase_k kk0 == Some k0);
    lookup_find ef opf k0;
    fp_prompt_hit ef opf hsf retf [PromptF hsg retg];
    assert (config_ok q0);
    msim af afast q0
