module Hoop.Runtime.Metatheory

open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics
open Hoop.Runtime.WellScopedness
open FStar.List.Tot

// Preservation of the stack: `cap @ below == k`, i.e. `find_prompt`
// really splits the stack -- dropping, adding and moving no frames.
let find_prompt_partitions_correctness
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : GTot prop
  = handled_in eff op k ==>
      // handled_in guarantees find_prompt returns Some
      (let Some (cap, _, below) = find_prompt eff op k in
          cap @ below == k
      )

val find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma (find_prompt_partitions_correctness eff op k)

(**
 * **The last frame of the captured continuation**: the captured segment is
 * non-empty and its final element is precisely the `PromptF` frame holding the
 * selected clause. This is the foundation of *deep handler semantics* — the
 * handler is re-installed on resumption, so the continuation may perform the
 * same effect again inside it.
 *)
let find_prompt_last_correctness
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : GTot prop
  = handled_in eff op k ==>
      (let Some (cap, c, _) = find_prompt eff op k in
          // captured continuation must not be empty
          Cons? cap /\
          // captured continuation has the prompt as the last element
          PromptF? (last cap) /\
          // and that prompt is for the same handler clause -- clause AND kind,
          // since the search carries both and they came from this one table.
          lookup_handler (PromptF?.hs (last cap)) eff op == Some c
      )

val find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
    (find_prompt_last_correctness eff op k)

(**
 * **The innermost lemma**: of the prompts able to handle the action, `find_prompt`
 * selects the one closest to the top of the stack. This is the correctness of
 * handler shadowing — with nested handler scopes for the same action, `perform`
 * always reaches the innermost.
 *)
let find_prompt_innermost_correctness
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : GTot prop
  = handled_in eff op k ==>
      (let Some (cap, _, _) = find_prompt eff op k in
          // The captured continuation stack is non-empty.
          (Cons? cap) /\
          // The selected prompt is the unique innermost handler for this action.
          ~(handled_in eff op (init cap))
      )

val find_prompt_innermost
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (find_prompt_innermost_correctness eff op k)

// -------------------------------------- //

(**
 * **Soundness of `lookup_clause`**: a returned clause really is an entry of the
 * table -- of its view `table hs`, the table itself being abstract. In other
 * words, `lookup_clause` never forges a clause.
 *
 * Together with `find_prompt_last`, this says the clause handed to `apply`
 * belongs to the prompt at the bottom of the captured continuation.
 *)
let lookup_clause_soundness
    (#cl : Type)
    (hs: handlers cl)
    (eff op : string)
  : GTot prop
  = match lookup_clause hs eff op with
    | None -> False
    | Some c -> memP (eff, op, c) (table hs)

val lookup_clause_memP
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures (lookup_clause_soundness hs eff op))

(**
 * **Completeness of `lookup_clause`**: a `None` means the table really has no
 * entry for `(eff, op)`. The frame-layer counterpart of `find_prompt`'s
 * refinement: a `handles` check fails because the prompt truly lacks the operation,
 * not because the search missed it. Only with this can `find_prompt_innermost`
 * validly claim that no handler is ever bypassed.
 *)
let lookup_clause_completeness
    (#cl : Type)
    (hs : handlers cl)
    (eff op : string)
  : GTot prop
  = None? (lookup_clause hs eff op) ==>
      forall (c: cl). ~(memP (eff, op, c) (table hs))

val lookup_clause_none
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures lookup_clause_completeness hs eff op)

//------------------------//

(**
 * **Perform progress**: performing `(eff, op)` inside a context that handles it
 * makes the next computation the clause fed with the payload and the captured
 * continuation, and the stack whatever remains below the target prompt.
 *
 * **Unless the entry it reaches holds a SCOPED clause**, in which case the
 * dispatch is refused. That case is not a hypothesis of this lemma but an arm of
 * its conclusion: the statement says strictly more than it did, and no caller
 * has anything new to discharge -- what a caller must do is decide the arm, and
 * every caller was going to look at the clause anyway.
 *
 * **The stored kind is the sole authority.** Not the constructor the clause
 * happens to carry: `Hoop.Runtime.Handlers.mk_handlers` takes an arbitrary
 * classifier, so nothing in F* forces the two to agree, and
 * `Hoop.Runtime.Machine.msim` is stated of EVERY configuration with no hypothesis about
 * how tables were built. Were the reference to decide on the stored kind and the
 * machine on the constructor, a table pairing `Full c` with `KScoped` would send
 * the two down different transitions and the simulation would be false. So both
 * machines read this field, and only this field.
 *)
 val step_perform
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
          (let Some (captured, found, below) = find_prompt eff op k in
              (match found.kind with
                | KScoped ->
                    step apply apply_s (Step (Perform eff op payload) k) ==
                      Rejected (ClauseKindMismatch eff op KOrdinaryOperation KScoped)
                | _ ->
                    step apply apply_s (Step (Perform eff op payload) k) ==
                      Step (apply found.body payload (kont_of captured)) below) /\
              // The stack is preserved -- a consequence of `find_prompt_partitions`.
              captured @ below == k))

(**
 * **Scoped perform progress**, the same statement read on the other node: the
 * clause is fed the payload, a WEAVE CAPABILITY and the continuation, and an
 * entry that is not scoped is refused.
 *
 * The weave carries `prepare_captured_fast captured` -- the intermediates
 * borrowed, the owner entire -- together with the ORIGIN of this very dispatch,
 * and it carries both as the partial application of a named function, so that
 * two dispatches of the same operation building the same segment build the same
 * weave and not merely two closures that agree. Nothing here asks whether that
 * segment may in fact be borrowed: see `step_weave_ok` / `step_weave_rejected`.
 *)
val step_performS
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures
          (let Some (captured, found, below) = find_prompt eff op k in
              (match found.kind with
                | KScoped ->
                    step apply apply_s (Step (PerformS eff op payload) k) ==
                      Step (apply_s found.body payload
                              (weave_of eff op (prepare_captured_fast captured))
                              (kont_of captured))
                           below
                | KFull ->
                    step apply apply_s (Step (PerformS eff op payload) k) ==
                      Rejected (ClauseKindMismatch eff op KScopedOperation KFull)
                | KFast ->
                    step apply apply_s (Step (PerformS eff op payload) k) ==
                      Rejected (ClauseKindMismatch eff op KScopedOperation KFast)) /\
              captured @ below == k))

(**
 * **Perform termination**: a `perform` gets stuck exactly when it runs outside
 * any context able to handle the action. The foundation of the later progress
 * and soundness proofs.
 *)
val step_perform_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply apply_s (Step (Perform eff op payload) k) == Stuck eff op)

(** **The same, for a scoped perform.** The `<==>` survives the new rejection
    arm: a refused dispatch is `Rejected` and not `Stuck`, so it does not make
    the right-hand side true, which is precisely the separation the two outcomes
    exist for. *)
val step_performS_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply apply_s (Step (PerformS eff op payload) k) == Stuck eff op)

(**
 * **Progress of `Splice`**: the carried frames are appended back onto the stack
 * and the body runs under them. Nearly trivial on its own, but combined with
 * `find_prompt_last` it yields deep handler semantics: the prompt travels inside
 * the captured segment, so it is re-installed on every `continue`.
 *
 * Stated of the constructor directly rather than through a recognizer, so that
 * both this and `step_resumed` below are *definitional equalities* — each proved
 * by `()`, and each therefore a regression test that fails the moment the rule
 * is defined as anything other than `fs @ k`.
 *)
let step_splice
    (#v #cl : Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (fs : stack v cl)
    (body : comp_tree v cl)
    (cc : stack v cl)
  : Lemma (step apply apply_s (Step (Splice fs body) cc) == Step body (fs @ cc))
  = ()

(**
 * **Progress of `Weave`**: `Splice`'s rule, behind one guard.
 *
 * Stated as the two definitional equalities rather than as one match, so that
 * each half is a regression test of its own: the success branch fails the moment
 * the prepared segment stops being installed exactly as a splice installs a
 * captured one, and the rejection branch fails the moment the check moves.
 *
 * **The check is here and nowhere else.** Not at the dispatch of the scoped
 * operation: a clause that discards an inner computation never builds one of
 * these, and never runs the check -- which is what makes "a non-borrowable
 * prompt in a context that is never woven is no reason to reject anything" a
 * property of the transition system rather than a remark. Decision 5.
 *
 * **The guard and the success branch do not read the origin**; the rejection
 * does, and reports it verbatim. That split is the whole of what the two extra
 * fields buy: the transition stays a function of the normalized segment, and the
 * refusal can still name the scope it refused.
 *)
let step_weave_ok
    (#v #cl : Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (oeff oop : string)
    (prepared : stack v cl)
    (body : comp_tree v cl)
    (cc : stack v cl)
  : Lemma (requires scope_blockers prepared == [])
          (ensures step apply apply_s (Step (Weave oeff oop prepared body) cc)
                     == Step body (prepared @ cc))
  = ()

let step_weave_rejected
    (#v #cl : Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (oeff oop : string)
    (prepared : stack v cl)
    (body : comp_tree v cl)
    (cc : stack v cl)
  : Lemma (requires Cons? (scope_blockers prepared))
          (ensures step apply apply_s (Step (Weave oeff oop prepared body) cc)
                     == Rejected (UnborrowableScope oeff oop (scope_blockers prepared)))
  = ()

(**
 * **Progress of a resumption**, the `Var` specialisation: the term becomes
 * `Var x`, the value passed to `continue`, and the captured continuation is
 * appended back onto the stack. This is the transition the machine actually
 * takes today; it survives `Splice` unchanged, and by `()`.
 *)
let step_resumed
    (#v #cl : Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (fs : stack v cl)
    (x : v)
    (cc : stack v cl)
  : Lemma (step apply apply_s (Step (resumed fs x) cc) == Step (Var x) (fs @ cc))
  = ()

(**
 * **And what the continuation handed to a clause is.** `kont_of` is the only
 * thing `step` ever builds a `Splice` with, so pinning its meaning pins the
 * whole of what a clause can do with a continuation: resume it, at a value.
 * A tautology as written, and deliberately -- it is what would break first if
 * `kont_of` were ever redirected to a `Splice` with a non-`Var` body.
 *)
let kont_of_resumed
    (#v #cl : Type)
    (cap : stack v cl)
    (x : v)
  : Lemma (kont_of cap x == resumed cap x)
  = ()

// The remaining transition rules -- the operational semantics of the machine.

let step_op
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply apply_s (Step (Op c fn) k) == Step c (BindF fn :: k))
  = ()

let step_handle
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply apply_s (Step (Handle hs ret body) k) == Step body (PromptF hs ret :: k))
  = ()

let step_var_done
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (value: v)
  : Lemma (step apply apply_s (Step (Var value) ([] <: stack v cl)) == Done value)
  = ()

let step_var_bind
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (value: v)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma (step apply apply_s (Step (Var value) (BindF fn :: rest)) == Step (fn value) rest)
  = ()

let step_var_prompt
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (step apply apply_s (Step (Var value) (PromptF hs ret :: rest)) ==
        (match ret with
          | Some r -> Step (r value) rest
          | None -> Step (Var value) rest))
  = ()

let step_var_prompt_identity
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (rest: stack v cl)
  : Lemma (step apply apply_s (Step (Var value) (PromptF hs None :: rest)) == Step (Var value) rest)
  = ()

let handle_installs
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures handled_in eff op (PromptF hs ret :: k))
  = ()

let stack_weakening
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
    (k: stack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures handled_in eff op (f :: k))
  = ()

//------------------------//

(** A terminal state is a fixed point of `steps`. There are three of them:
    `Done`, `Stuck` and `Rejected`. The last is terminal for the same reason the
    other two are -- `steps` has nothing to do from it -- and for a DIFFERENT
    reason than it is unreachable; see `Hoop.Runtime.Semantics.rejection`. *)
val steps_terminal
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s \/ Rejected? s)
      (ensures steps apply apply_s n s == s)

(** Step additivity. *)
val steps_add
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (ensures steps apply apply_s (n + m) s == steps apply apply_s m (steps apply apply_s n s))

(** Corollary: once a run is `Done`, extra fuel changes nothing. *)
val steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply apply_s n s))
      (ensures steps apply apply_s (n + m) s == steps apply apply_s n s)

// ------------------------------------------------------------------ //
//  Well-scopedness: the defining equations                            //
// ------------------------------------------------------------------ //

(**
 * `Hoop.Runtime.WellScopedness.ws` is defined by recursion on a step index
 * rather than on the computation tree, for the reason spelled out where it is
 * defined.
 *
 * The eight lemmas of this section make that a matter of bookkeeping rather
 * than of substance: each is an `<==>`, and together they are exactly the
 * clauses of the structural definition. Nothing below ever unfolds `ws_n`, and
 * this interface mentions neither it nor `wf_stack_n`, so a client reasons
 * about `ws` only through these equations, the congruence lemmas and the
 * theorems below.
 *)

(** **A value is well scoped anywhere**: it fires nothing. *)
val ws_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (x: v)
  : Lemma (ws cok a (Var x <: comp_tree v cl))

(** **A `Perform` is well scoped exactly when its action is available.** The
    only clause of `ws` that can fail, hence the entire content of the
    predicate; everything else merely propagates it through the tree.

    The `eff =!= var_eff` conjunct is the key-namespace partition of
    `Hoop.Runtime.WellScopedness`: the reserved effect name belongs to
    prompt-local cells, and a capability held by virtue of a *cell* must not
    make a `Perform` well scoped, since `find_prompt` would then find nothing
    and `progress` would fail. *)
val ws_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (eff op: string)
    (payload: list v)
  : Lemma (ws cok a (Perform eff op payload <: comp_tree v cl) <==>
           (eff =!= var_eff /\ a eff op))

(** **A scoped `Perform` asks exactly what an ordinary one asks.** What a scoped
    operation additionally owes concerns its inner computations, which live in
    the opaque payload where no clause of `ws` can reach them; that obligation is
    `Hoop.Runtime.WellScopedness.apply_scoped_ok`, at the boundary. *)
val ws_performS
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (eff op: string)
    (payload: list v)
  : Lemma (ws cok a (PerformS eff op payload <: comp_tree v cl) <==>
           (eff =!= var_eff /\ a eff op))

(** **`Op` distributes**: `c >>= fn` is well scoped exactly when `c` is and
    every branch of `fn` is. A bind installs no handler, so the environment does
    not change across it. *)
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
 * The asymmetry is the scoping rule of the language, not an accident of the
 * definition: a clause is invoked after `step` has cut the stack at its own
 * prompt and thrown that prompt away for the duration, and a return clause is
 * invoked by `step_var_prompt`, which pops the prompt first. Neither can rely
 * on its own handler being installed.
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
 * **A `Splice` node is well scoped exactly when its two parts are**: the frames
 * form a well-formed stack, and the body is well scoped in the environment
 * *those frames offer*, which is where `step_splice` puts it.
 *
 * The asymmetry with `ws_handle` is worth noticing: a `Handle` extends the
 * environment by its own table only, because its clauses run outside their
 * prompt. A `Splice` extends it by everything in the segment, because the body
 * genuinely runs with the whole segment installed beneath it -- the prompts in
 * it included. That is the environment-level statement of deep-handler
 * resumption, and `av_append` is what makes it agree with the stack the machine
 * actually builds.
 *)
val ws_splice
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (body: comp_tree v cl)
  : Lemma (ws cok a (Splice frames body) <==>
            (wf_stack cok a frames /\ ws cok (can_in_with frames a) body))

(**
 * **A `Weave` node is well scoped exactly when its two parts are** -- the same
 * equation as `ws_splice`, at the prepared segment, and **with no borrowability
 * condition on either side of the `<==>`**.
 *
 * That absence is the load-bearing part. It says a `Weave` that is going to be
 * rejected is still well scoped, which is what makes `weave_ok` -- and with it
 * the third premise of `apply_scoped_ok` -- dischargeable by the machine
 * unconditionally, with nothing known about what kind of clause any crossed
 * table holds. Fold borrowability in here and the dispatch of a scoped operation
 * would stop being provable well scoped, and `progress` would acquire a
 * hypothesis about clause kinds. Decision 5 and Decision 7.
 *
 * The origin does not appear on the right-hand side at all: it is diagnostic
 * provenance, and well-scopedness is a judgement about what actions may be
 * fired.
 *)
val ws_weave
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (oeff oop: string)
    (prepared: stack v cl)
    (body: comp_tree v cl)
  : Lemma (ws cok a (Weave oeff oop prepared body) <==>
            (wf_stack cok a prepared /\ ws cok (can_in_with prepared a) body))

(** **A resumption is well scoped exactly when the continuation it carries is
    well formed.** The `Var` specialisation of `ws_splice`: a resumption holds no
    computation of its own -- it splices a captured stack segment back on and
    hands it a value -- so the body conjunct collapses to `True` by `ws_var` and
    its obligation is that of a stack, exactly as it always was. *)
val ws_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (x: v)
  : Lemma (ws cok a (resumed frames x) <==> wf_stack cok a frames)

(** **The empty stack is well formed**: it suspends nothing. *)
val wf_stack_nil
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
  : Lemma (wf_stack cok a ([] <: stack v cl))

(** **A `BindF` frame contributes nothing to the environment**: the suspended
    continuation is judged in the environment of the frames below it. *)
val wf_stack_bind
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (BindF fn :: rest) <==>
        ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest))

(** **A `PromptF` frame owes for its table and its return clause**, both judged
    *below* the prompt — the same rule as `ws_handle`, which is what makes the
    two agree when `step_handle` turns one into the other. *)
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
 * **Well-scopedness only sees which actions an environment offers**, not how it
 * was built.
 *
 * Availability environments are functions, so the ones the machine computes are
 * equal pointwise but almost never syntactically: pushing a `BindF` frame
 * yields `can_in (BindF fn :: k)`, a different closure from `can_in k` although
 * it offers exactly the same actions. Every preservation proof below therefore
 * ends with a congruence step, and these lemmas are it.
 *
 * The third member of the family, `handler_ok_congr`, is
 * `Hoop.Runtime.WellScopedness`'s: the step-indexed congruence there needs it,
 * and this module is downstream, so it cannot be proved here and used there.
 *)
val ws_congr
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a1 a2: can_perform)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can a1 a2)
      (ensures ws cok a1 c <==> ws cok a2 c)

val wf_stack_congr
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

(** **Pushing a `PromptF` frame extends the environment by its table**: the
    environment-level reading of `step_handle`. It matches to the letter the
    extension `ws_handle` grants the body of the corresponding `Handle`, which
    is what carries well-scopedness across that transition. *)
val av_prompt
    (#v #cl: Type)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (PromptF hs ret :: k) a) (extend hs (can_in_with k a)))

(** **Concatenation of stacks composes environments**: running on `k1` stacked on
    `k2` offers what `k1` offers on top of what `k2` does. Needed for the
    `Splice` transition, which splices a carried segment back on -- and needed
    twice there, once for the resulting stack and once for the environment the
    spliced body is judged in. *)
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
 * the environment the lower part offers. The workhorse of the two transitions
 * that take a stack apart or put one back together — read left to right it
 * justifies `Perform`'s cut, right to left `Splice`'s splice.
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
//  The segment a scope runs under                                     //
//                                                                     //
//  `Hoop.Runtime.Semantics.prepare_scope` rewrites the captured        //
//  segment into the context a scoped operation's inner computation is  //
//  to run in. The two lemmas below are what `pres_performS` rests on:  //
//  the rewritten segment OFFERS THE SAME THINGS, and it is STILL WELL  //
//  FORMED -- which are, in that order, the two conjuncts of `ws_weave` //
//  and hence the whole of `weave_ok`. The transition reaches them      //
//  through `prepare_captured_is_prepare_scope`, which reads the ONE    //
//  segment a dispatch holds as the two parts these are stated of.      //
//                                                                     //
//  They sit here, with `av_append` and `wf_stack_append`, because that //
//  is what they are made of: both are the corresponding statement      //
//  about `borrow` alone, transported across the `@ [owner]` by those   //
//  two.                                                                //
//                                                                     //
//  Neither mentions borrowABILITY -- whether the prompts in question   //
//  are ones a scope is allowed to borrow. That is a separate question, //
//  answered at the transition, and keeping it out of these statements  //
//  is what makes them say something about the transformation itself.   //
// ------------------------------------------------------------------ //

(**
 * **Borrowing changes no capability**: a borrowed segment offers exactly the
 * operations and exactly the cells the original one did.
 *
 * The three clauses of `borrow` are each a reason this holds. Dropping `BindF`
 * is safe because a bind frame contributes nothing to `can_in_with` -- it
 * neither installs a table nor holds a cell. Clearing a `PromptF`'s return
 * clause is safe because `ret` does not enter `can_in_with` either; only `hs`
 * does, and that is kept.
 *
 * **The third is not free, and it is why the cells travel at all.** A `ParamF`
 * frame IS a capability -- `can_in_with` reads `param_in` under the reserved
 * effect name exactly as it reads `find_prompt` under an ordinary one -- so had
 * `borrow` dropped the cells, or kept the labels while discarding the values,
 * this lemma and `prepare_scope_can` below would simply be FALSE. Keeping
 * `ParamF l x` entire is what makes the statement true, not a convenience laid
 * on top of one that was already true.
 *
 * **This is the form in which "at every suffix" is read off.** It is stated of
 * an arbitrary stack, and a suffix of a segment is a stack, so every suffix is
 * an instance -- which is what `prepare_scope_wf` needs, since the environments
 * have to agree at each borrowed prompt's own position and not merely at the top
 * of the segment. The proof is the induction over the segment whose hypothesis
 * those instances are; `prepare_scope_can` is its corollary, not the other way
 * round.
 *)
val borrow_can
    (#v #cl: Type)
    (k: stack v cl)
    (a: can_perform)
  : Lemma (equiv_can (can_in_with (borrow k) a) (can_in_with k a))

(** **The prepared segment offers exactly what the captured one did.**
    `borrow_can` composed with `av_append` on either side of the owner, which is
    common to both stacks and so cancels. Stated of an arbitrary
    `intermediates`, hence -- again -- at every suffix of the segment. *)
val prepare_scope_can
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
    (can: can_perform)
  : Lemma
      (equiv_can (can_in_with (prepare_scope intermediates owner) can)
                 (can_in_with (intermediates @ [owner]) can))

(**
 * **Well-formedness survives borrowing**, and this is the induction that
 * `prepare_scope_wf` is assembled from.
 *
 * **It introduces no new semantic premise.** Every obligation the borrowed
 * segment carries is one the original already carried:
 *
 *   - a `BindF` frame's obligation is discharged by the frame being dropped --
 *     the suspended continuation is gone, so nothing is owed for it;
 *   - a borrowed prompt's return clause is gone too, so its `ret_ws` obligation
 *     becomes `True` and is discarded rather than transported;
 *   - what IS transported is each borrowed prompt's `handler_ok`, through
 *     `borrow_can` at that prompt's suffix and `handler_ok_congr`.
 *
 * **The transport is nevertheless a real induction, not a rewriting.** Dropping
 * the `BindF` frames changes what lies below every prompt that had one above it,
 * so a borrowed table is judged against a tail that is not the tail it was
 * judged against before. `clause_ok_congr` is required for exactly that reason
 * and for no other: it is the hypothesis that lets a clause's well-scopedness be
 * read in an equivalent environment.
 *)
val borrow_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_stack cok a k)
      (ensures wf_stack cok a (borrow k))

(**
 * **Well-formedness transports to the prepared segment.**
 *
 * `borrow_wf` at the environment the owner offers, split off and joined back on
 * by `wf_stack_append`. What that split buys is the owner: **its tail is the
 * SAME in both stacks** -- `[]` relative to the segment, whatever lies below it
 * in the ambient `can` -- so `wf_stack cok can [owner]` is literally the same
 * proposition on both sides, and the owner's `handler_ok` and `ret_ws`
 * obligations are reused unchanged, with no congruence step and nothing to
 * prove. That is the payoff of not borrowing the owner, and it is why keeping
 * its `ret` is cheaper than dropping it would have been.
 *
 * So no new premise: see `borrow_wf` for the accounting of the intermediates,
 * and note that neither this lemma nor that one asks anything about what KIND of
 * clause any table holds.
 *)
val prepare_scope_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
    (can: can_perform)
  : Lemma
      (requires clause_ok_congr cok /\ wf_stack cok can (intermediates @ [owner]))
      (ensures wf_stack cok can (prepare_scope intermediates owner))

// ------------------------------------------------------------------ //
//  Preservation of the machine invariant, one transition at a time    //
// ------------------------------------------------------------------ //

(**
 * The lemmas that follow are the branches of `step`, each shown to take a
 * well-formed state to a well-formed state. They are kept apart rather than
 * inlined into `step_preserves_wf` -- they are of very different weights,
 * `pres_var` being immediate and `pres_perform` the whole argument -- so that
 * each SMT query stays small.
 *
 * One of them, `pres_resumed`, is not a branch: it is `pres_splice` read at a
 * `Var` body. It is stated because that is the shape the machine actually
 * builds, and having it under its own name is what lets a reader check that the
 * general rule really does say the old thing about resumption.
 *)

(** **Op**: descending into the left of a bind, with the rest parked on the
    stack. The pushed frame changes no environment, so both halves of `ws_op`
    land where they must. *)
val pres_op
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (inner: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Op inner fn) k))
      (ensures wf_state cok (step apply apply_s (Step (Op inner fn) k)))

(** **Handle**: the extension `ws_handle` grants the body is exactly the one
    `av_prompt` says the pushed frame provides. *)
val pres_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Handle hs ret body) k))
      (ensures wf_state cok (step apply apply_s (Step (Handle hs ret body) k)))

(** **Var**: a value meets the top frame. Whichever frame it is, its obligation
    was recorded against the environment of the frames below, which is precisely
    the environment the machine now runs in. *)
val pres_var
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires wf_state cok (Step (Var value <: comp_tree v cl) k))
      (ensures wf_state cok (step apply apply_s (Step (Var value <: comp_tree v cl) k)))

(** **Splice**: the carried segment is spliced back on and the body runs under
    it. Well-formedness of the join follows from `wf_stack_append`, and the body
    lands in the environment `ws_splice` recorded it against -- the two agree by
    `av_append`, which is the whole content of the case. *)
val pres_splice
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (frames: stack v cl)
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Splice frames body) k))
      (ensures wf_state cok (step apply apply_s (Step (Splice frames body) k)))

(** **Resumed**: the `Var` specialisation, the transition the machine takes on
    `continue`. The body obligation is vacuous, so what remains is the splice of
    the captured segment, exactly as before. *)
val pres_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (captured: stack v cl)
    (value: v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (resumed captured value) k))
      (ensures wf_state cok (step apply apply_s (Step (resumed captured value) k)))

(**
 * **Perform**: the interesting one, and the only branch that could get stuck.
 *
 * Well-scopedness of the `Perform` says the action is available on `k`, hence
 * `find_prompt` succeeds and the `Stuck` branch is out. That the resulting state
 * is well formed is assembled from three facts proved elsewhere: the stack
 * splits as `captured @ below` (`find_prompt_partitions`); the prompt owning the
 * clause is the last frame of `captured` (`find_prompt_last`), whence
 * `wf_stack_split_prompt` gives `cok (can_in below) clause`; and the captured
 * segment, well formed over `below`, makes `kont_of captured` a well
 * scoped continuation there (`ws_resumed`). `apply_ok` then delivers the clause
 * body, well scoped in `can_in below`, which is where the machine continues.
 *)
val pres_perform
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\
                wf_state cok (Step (Perform eff op payload) k))
      (ensures wf_state cok (step apply apply_s (Step (Perform eff op payload) k)))

(**
 * **PerformS**: the scoped counterpart of `pres_perform`, and the one place the
 * machine's half of the scoped bargain is paid.
 *
 * Two of the three premises `apply_scoped_ok` demands are `pres_perform`'s
 * verbatim -- the clause is well scoped below its prompt
 * (`wf_stack_split_prompt` at the prompt `find_prompt_last` locates), and every
 * branch of the continuation is well scoped there (`ws_resumed` on the captured
 * segment). The third, `weave_ok`, is PROVED HERE and assumed nowhere:
 *
 *   - `find_prompt_partitions` and `find_prompt_last` split the captured segment
 *     as `intermediates @ [owner]` with `PromptF? owner`, which is what
 *     `prepare_captured_is_prepare_scope` needs to read the transition's segment
 *     as `prepare_scope`;
 *   - `prepare_scope_wf` carries `wf_stack` from the captured segment to the
 *     prepared one, which is the first conjunct of `ws_weave`;
 *   - `prepare_scope_can` says the two offer the same capabilities, so a
 *     computation well scoped at the perform site is well scoped under the
 *     prepared segment -- the second conjunct, through `ws_congr`.
 *
 * None of the three mentions borrowability, and none could: this is a theorem
 * about a `Weave` node that may well go on to be rejected.
 *
 * A dispatch that is refused lands in `Rejected`, where `wf_state` is `True`, so
 * that arm is unconditional.
 *)
val pres_performS
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_scoped_ok apply_s cok /\
                wf_state cok (Step (PerformS eff op payload) k))
      (ensures wf_state cok (step apply apply_s (Step (PerformS eff op payload) k)))

(** **Weave**: `pres_splice` at the prepared segment on the success branch, and
    `wf_state (Rejected _) = True` on the other. Unconditional on both, which is
    what the absence of a borrowability clause in `ws_weave` buys. *)
val pres_weave
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (oeff oop: string)
    (prepared: stack v cl)
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (Weave oeff oop prepared body) k))
      (ensures wf_state cok (step apply apply_s (Step (Weave oeff oop prepared body) k)))

(* ------------------------------------------------------------------ *)
(*  Preservation for prompt-local state                                *)
(* ------------------------------------------------------------------ *)

(** **A `ParamF` frame is transparent to `wf_stack`**: it suspends no
    computation and installs no handler, so it owes nothing. *)
val wf_stack_param
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (l: string)
    (x: v)
    (rest: stack v cl)
  : Lemma (wf_stack cok can (ParamF l x :: rest) <==> wf_stack cok can rest)

(** **A write moves no prompt.** *)
val set_param_handled
    (#v #cl: Type)
    (l: string)
    (x: v)
    (k k': stack v cl)
    (eff op: string)
  : Lemma
      (requires set_param l x k == Some k')
      (ensures Some? (find_prompt eff op k') <==> Some? (find_prompt eff op k))

(** **A write creates and destroys no cell.** Stated through `find_param`
    rather than `param_in`, because the latter is an existential over `memP`
    while the induction is structural; the refinement on `find_param`
    converts. *)
val set_param_param_in
    (#v #cl: Type)
    (l: string)
    (x: v)
    (k k': stack v cl)
    (l2: string)
  : Lemma
      (requires set_param l x k == Some k')
      (ensures Some? (find_param l2 k') <==> Some? (find_param l2 k))

(** **Hence a write leaves the capability environment alone**: the two facts
    above are exactly the two disjuncts of `can_in_with`. *)
val set_param_equiv_can
    (#v #cl: Type)
    (l: string)
    (x: v)
    (k k': stack v cl)
    (can: can_perform)
  : Lemma
      (requires set_param l x k == Some k')
      (ensures equiv_can (can_in_with k' can) (can_in_with k can))

(** **And leaves the stack well formed.** *)
val set_param_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (l: string)
    (x: v)
    (k k': stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ set_param l x k == Some k' /\ wf_stack cok can k)
      (ensures wf_stack cok can k')

(** **NewP**: installing a cell extends the environment by exactly that cell,
    which is what `extend_param` says and what `ParamF` contributes to
    `can_in`. *)
val pres_newp
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (l: string)
    (init: v)
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ wf_state cok (Step (NewP l init body) k))
      (ensures wf_state cok (step apply apply_s (Step (NewP l init body) k)))

(** **ReadP**: well-scopedness says the cell is available on `k`, hence
    `find_param` succeeds and the `Stuck` branch is out. *)
val pres_readp
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (l: string)
    (k: stack v cl)
  : Lemma
      (requires wf_state cok (Step (ReadP l <: comp_tree v cl) k))
      (ensures wf_state cok (step apply apply_s (Step (ReadP l <: comp_tree v cl) k)))

(** **WriteP**: likewise, and the rebuilt stack is well formed by
    `set_param_wf`, in an environment `set_param_equiv_can` says has not
    moved. *)
val pres_writep
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (l: string)
    (x: v)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\
                wf_state cok (Step (WriteP l x <: comp_tree v cl) k))
      (ensures wf_state cok (step apply apply_s (Step (WriteP l x <: comp_tree v cl) k)))

(** **Preservation**: one transition of a well-formed machine leaves it well
    formed. The eight branches above, assembled. *)
val step_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
      (ensures wf_state cok (step apply apply_s s))

(**
 * **Progress, one step**: a well-formed machine does not wedge — preservation
 * read against the `Stuck` clause of `wf_state`, which is `False`.
 *
 * Compare `step_perform_stuck`, which reduces the absence of `Stuck` to *some
 * frame on the stack handles the action* but leaves open why a handler should
 * be there at all. Well-scopedness is the answer, and here the two meet.
 *)
val step_progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
      (ensures ~(Stuck? (step apply apply_s s)))

// ------------------------------------------------------------------ //
//  Progress                                                           //
// ------------------------------------------------------------------ //

(** **Preservation along a whole run**: the invariant is an invariant of `steps`,
    not merely of `step`. Induction on the fuel. *)
val steps_preserves_wf
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
      (ensures wf_state cok (steps apply apply_s n s))

(**
 * **Progress**: a well-formed machine never gets stuck, however long it runs.
 * `Hoop.Runtime.Machine` says of the `Stuck` constructor that it *should never occur as
 * long as the runtime is sound*; here that is discharged, against a precise
 * reading of *sound* — the program is well scoped, and the FFI's `apply`
 * respects well-scopedness.
 *)
val progress
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
      (ensures ~(Stuck? (steps apply apply_s n s)))

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
 * **From the invariant to the precondition of `run`.** `run` cannot take
 * `wf_state cok s` directly: it lives in `Hoop.Runtime.Machine` and would then need
 * `step_preserves_wf`, which lives here. Phrasing its precondition as *this run
 * never reaches `Stuck`* breaks the knot — that property is closed under `step`
 * by inspection, so `Hoop.Runtime.Machine` stays self-contained while the substance of
 * the argument is supplied by these two lemmas.
 *)
val wf_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
      (ensures never_stuck apply apply_s s)

(**
 * **The entry point**: a well-scoped program may be handed to `run`, and comes
 * back `Done`. Read with the type of `run`, this is the end-to-end statement of
 * the development — if the PureScript side only builds programs whose
 * `perform`s sit inside a matching `with`-block, and its clause interpreter
 * respects `apply_ok`, then the machine either diverges or returns a value; it
 * never reports an unhandled operation.
 *)
val load_never_stuck
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ ws cok (can_nothing ()) c)
      (ensures never_stuck apply apply_s (load c))

(* ================================================================== *)
(*  The var-semantics theorem                                         *)
(*                                                                    *)
(*  A characterisation of the REFERENCE SEMANTICS itself, and not a   *)
(*  machine-versus-reference property: as the latter it would add     *)
(*  nothing over `Hoop.Runtime.Machine.execute_agrees`, which already *)
(*  says the shipping machine agrees with                             *)
(*  `Hoop.Runtime.Semantics.step` on every program, cells included.   *)
(*                                                                    *)
(*  What it is instead is the human-auditable statement that          *)
(*  `set_param` changes EXACTLY the target cell and nothing else --   *)
(*  and, in its two splice halves, that where a cell sits relative to *)
(*  a capture is what decides whether a write survives a resumption.  *)
(*  That is precisely what rules out the implementation this design   *)
(*  was chosen over: a cell reached through a cached pointer passes   *)
(*  typing, progress and the monad laws, and fails `set_param_        *)
(*  captured` -- it would let one branch of a multi-shot resumption   *)
(*  see another branch's write.                                       *)
(*                                                                    *)
(*  Together with `set_param_handled` (no prompt moves) and           *)
(*  `set_param_param_in` (no cell appears or disappears), the four    *)
(*  below are a complete account of what a write does.                *)
(* ================================================================== *)

(** **LOCALITY**: a write to `l` changes the contents of no other cell. *)
val set_param_local
    (#v #cl: Type)
    (l: string)
    (x: v)
    (k k': stack v cl)
    (l2: string)
  : Lemma
      (requires set_param l x k == Some k' /\ l2 =!= l)
      (ensures find_param l2 k' == find_param l2 k)

(** **HIT**: and the target cell really does take the written value. *)
val set_param_hits
    (#v #cl: Type)
    (l: string)
    (x: v)
    (k k': stack v cl)
  : Lemma
      (requires set_param l x k == Some k')
      (ensures find_param l k' == Some x)

(**
 * **SPLICE FIDELITY**: a write whose cell is *not* in the captured segment
 * passes through the capture boundary and lands in `below`, leaving the
 * captured frames untouched. This is the half that makes a `ctl` clause which
 * writes and then resumes see its own write -- the shared reading, and the
 * Koka behaviour that the `state(choice)` fixture in `Hoop.Runtime.Test`
 * pins down.
 *)
val set_param_splice
    (#v #cl: Type)
    (l: string)
    (x: v)
    (cap below: stack v cl)
  : Lemma
      (requires None? (find_param l cap))
      (ensures
        (match set_param l x below with
          | None -> None? (set_param l x (cap @ below))
          | Some below' -> set_param l x (cap @ below) == Some (cap @ below')))

(**
 * **CAPTURE FIDELITY**, the dual: a write whose cell *is* in the captured
 * segment stays there, so every resumption of a capture holding the cell gets
 * its own copy. This is the per-branch reading, and the half a cached-pointer
 * implementation gets wrong; the `choice(state)` fixture pins it down.
 *)
val set_param_captured
    (#v #cl: Type)
    (l: string)
    (x: v)
    (cap below: stack v cl)
  : Lemma
      (requires Some? (find_param l cap))
      (ensures
        (let Some cap' = set_param l x cap in
         set_param l x (cap @ below) == Some (cap' @ below)))
