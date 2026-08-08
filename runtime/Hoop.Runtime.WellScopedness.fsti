(**
 * Well-scopedness: the discipline that rules the `Stuck` state out.
 *
 * A program is well scoped when every action it can fire is one some enclosing
 * handler offers. The apparatus here says that precisely -- `can_perform` for
 * the capability environment, `ws` and `wf_stack` for the judgement on
 * computations and on stacks, `wf_state` for the machine invariant they
 * assemble into -- and `apply_ok` states the one obligation that cannot be
 * discharged inside F*, because it concerns a PureScript closure arriving over
 * the FFI.
 *
 * **What this interface hides, and what it cannot.** Every definition below is
 * a transparent `let`, not an opaque `val`, and that is forced rather than
 * chosen: the module is `prop`-valued throughout and its consumers reason by
 * unfolding. `Hoop.Runtime.Metatheory` proves the defining equations of `ws`
 * -- `ws_var`, `wf_stack_nil`, and the backward halves of `ws_op` and
 * `ws_resumed` -- by `()`, which is only possible while `ws` and `wf_stack`
 * unfold to their step-indexed definitions; the environment lemmas
 * `av_bind` / `av_prompt` / `av_append` need `extend`, `can_in_with`, `can_in`,
 * `can_nothing` and `equiv_can`; `handler_ok_congr` needs `clause_ok_congr` and
 * `handler_ok`; the preservation lemmas need `wf_state`, `ret_ws` and
 * `apply_ok`. What the interface does hide is the step index itself
 * -- `ws_n` and `wf_stack_n` -- the step-indexed congruence lemmas, and every
 * proof.
 *
 * **A caveat on `private` here.** `ws_n` and `wf_stack_n` have to sit in this
 * interface, since `ws` and `wf_stack` are transparent and are defined by them.
 * `private` in an *interface* keeps a name out of clients but, unlike `private`
 * in an *implementation*, does not keep it from a `friend`. Nothing friends
 * this module; if anything ever does, it will be able to name `ws_n`, whereas
 * `ws_n_congr` and `wf_stack_n_congr` -- `private` in the implementation -- stay
 * out of reach.
 *)
module Hoop.Runtime.WellScopedness

open FStar.List.Tot

open Hoop.Runtime.Syntax
open Hoop.Runtime.Handlers
open Hoop.Runtime.Semantics

// ------------------------------------------------------------------ //
//  Capability environments                                            //
// ------------------------------------------------------------------ //

// The type of *capability environment* - that `can_perform eff op` holds means
// one can perform the action (eff, op) in current environment.
let can_perform = eff:string -> op:string -> prop

let can_nothing () : GTot can_perform = fun _ _ -> False

// Extending with handlers
let extend
    (#cl: Type)
    (hs: handlers cl)
    (c: can_perform)
  : GTot can_perform
  = fun eff op -> Some? (lookup_clause hs eff op) \/ c eff op

let can_in_with
    (#v #cl: Type)
    (k: stack v cl)
    (c: can_perform)
  : GTot can_perform
  = fun eff op -> Some? (find_prompt eff op k) \/ c eff op

let can_in
    (#v #cl: Type)
    (k: stack v cl)
  : GTot can_perform
  = can_in_with k (can_nothing ())

// Pointwise equivalence of capability environments.
let equiv_can
    (can1 can2: can_perform)
  : prop
  = forall (eff op: string). can1 eff op <==> can2 eff op

// ------------------------------------------------------------------ //
//  The judgement on clauses and handler tables                        //
// ------------------------------------------------------------------ //

(**
 * `clause_ok_t` is an *capability-indexed* predicate over the handler clause.
 * Given `cok : clause_ok_t cl`, read `cok can c` as "the handler clause `c`
 * only performs actions permitted by the capability environment `can`."
 *
 * Note that cok is not provable　within F*　and its validity is assumed to be
 * verified within PureScript's type system.
 *)
let clause_ok_t (cl: Type) = can_perform -> cl -> prop

let clause_ok_congr
    (#cl: Type)
    (cok: clause_ok_t cl)
  : prop
  = forall (can1 can2: can_perform) (c: cl).
      equiv_can can1 can2 ==> (cok can1 c <==> cok can2 c)

(**
 * A handler well-scopedness predicate: We **define** `handler_ok cok can hs` as
 * "every handler clause `c` in `hs` is well-scoped wrt `can`".
*)
let handler_ok
    (#cl: Type)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (hs: handlers cl)
  : prop
  = forall c. c `clause_memP` hs ==> cok can c

// ------------------------------------------------------------------ //
//  The judgement on computations and stacks                           //
// ------------------------------------------------------------------ //

(**
 * The well-scopedness of a computation tree. `ws_n n cok can c` states that
 * `c` is well-scoped within the environment `can`, inspected up to depth `n`.
 * `wf_stack_n` is its counterpart for stacks.
 *
 * Note that the `pure` clause of `Handle` is an option-wrapped function. Consequently,
 * F* cannot automatically deduce that `Some?.v (Handle?.pure c) v << c` to prove
 * the termination of structural recursion. This is why `ws_n` is explicitly
 * indexed by the computation tree depth `n`.
 *
 * It is `private`: no client can name it, and the only place the index is ever
 * peeled is the block of lemmas below, whose proofs live in the implementation.
 *)
private
let rec ws_n
    (#v #cl: Type)
    (n: nat)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (c: comp_tree v cl)
  : Tot prop (decreases %[n; 1; 0])
  = if n = 0 then True
    else
      match c with
      | Var _ -> True
      | Perform eff op _ -> can eff op
      | Op inner fn ->
          ws_n (n - 1) cok can inner /\ (forall (x: v). ws_n (n - 1) cok can (fn x))
      | Handle hs ret body ->
          ws_n (n - 1) cok (extend hs can) body /\
          handler_ok cok can hs /\
          (match ret with
            | None -> True
            | Some r -> forall (x: v). ws_n (n - 1) cok can (r x))
      | Resumed frames _ -> wf_stack_n n cok can frames

(**
 * Well-formedness of a stack: `wf_stack_n n cok can k means` that every computation suspended
 * in a frame is well scoped in the environment offered by the part of the stack *below* that
 * frame — exactly the environment in which the machine will eventually resume it. A `BindF`
 * frame contributes nothing to that environment; a `PromptF` frame installs its table.
 *)
and wf_stack_n
    (#v #cl: Type)
    (n: nat)
    (cok: clause_ok_t cl)
    (can: can_perform)
    (k: stack v cl)
  : Tot prop (decreases %[n; 0; length k])
  = if n = 0 then True
    else
      match k with
      | [] -> True
      | BindF fn :: rest ->
          (forall (x: v). ws_n (n - 1) cok (can_in_with rest can) (fn x)) /\ wf_stack_n n cok can rest
      | PromptF hs ret :: rest ->
          handler_ok cok (can_in_with rest can) hs /\
          (match ret with
            | None -> True
            | Some r -> forall (x: v). ws_n (n - 1) cok (can_in_with rest can) (r x)) /\
          wf_stack_n n cok can rest

// Well-scopedness: `c` fires no action outside `can`, at any depth.
let ws (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (c: comp_tree v cl) : GTot prop =
  forall (n: nat). ws_n n cok can c

// Well-formedness of a stack: every suspended computation it holds is well scoped where
// it will be resumed, at any depth.
let wf_stack (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (k: stack v cl) : GTot prop =
  forall (n: nat). wf_stack_n n cok can k

// The obligation carried by a return clause
let ret_ws (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (ret: option (v -> comp_tree v cl))
  : GTot prop
  = match ret with
    | None -> True
    | Some r -> forall (x: v). ws cok can (r x)

(* ------------------------------------------------------------------ *)
(*  Peeling the step index                                             *)
(*                                                                     *)
(*  These lemmas are the only place the index is ever peeled, and only  *)
(*  their statements are exported: the proofs stay in the              *)
(*  implementation. `Hoop.Runtime.Metatheory` assembles them into the   *)
(*  `<==>` equations of the structural definition, and the rest of the  *)
(*  development works through those.                                   *)
(*                                                                     *)
(*  Only the forward directions appear here, plus the two backward      *)
(*  directions that pass under an `option`. The remaining backward      *)
(*  directions are proved in `Metatheory` by unfolding `ws` outright,   *)
(*  which is why `ws` is a transparent `let` above.                     *)
(* ------------------------------------------------------------------ *)

val ws_perform_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                  (eff op: string) (payload: list v)
  : Lemma (ws cok can (Perform eff op payload) <==> can eff op)

val ws_op_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
              (c: comp_tree v cl) (fn: v -> comp_tree v cl)
  : Lemma (requires ws cok can (Op c fn))
          (ensures ws cok can c /\ (forall (x: v). ws cok can (fn x)))

val ws_handle_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok can (Handle hs ret body))
          (ensures ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)

val ws_handle_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)
          (ensures ws cok can (Handle hs ret body))

val ws_resumed_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                   (frames: stack v cl) (x: v)
  : Lemma (requires ws cok can (Resumed frames x)) (ensures wf_stack cok can frames)

val wf_stack_bind_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                      (fn: v -> comp_tree v cl) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (BindF fn :: rest))
          (ensures (forall (x: v). ws cok (can_in_with rest can) (fn x)) /\
                   wf_stack cok can rest)

val wf_stack_prompt_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (PromptF hs ret :: rest))
          (ensures handler_ok cok (can_in_with rest can) hs /\
                   ret_ws cok (can_in_with rest can) ret /\
                   wf_stack cok can rest)

val wf_stack_prompt_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires handler_ok cok (can_in_with rest can) hs /\
                    ret_ws cok (can_in_with rest can) ret /\
                    wf_stack cok can rest)
          (ensures wf_stack cok can (PromptF hs ret :: rest))

(** **Congruence in the environment**: `ws`, `wf_stack` and `handler_ok` see a
    capability environment only through its extension, so pointwise-equivalent
    environments give the same judgement. The step-indexed lemmas the proofs
    run on stay in the implementation, `private`.

    `handler_ok_congr` is `clause_ok_congr` read through `handler_ok`. It sits
    here, with the judgement it is about, rather than in
    `Hoop.Runtime.Metatheory` with the rest of the congruence reasoning: the
    step-indexed lemmas below need it, and that module is downstream of this
    one. *)
val handler_ok_congr (#cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform)
                     (hs: handlers cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures handler_ok cok can1 hs <==> handler_ok cok can2 hs)

val ws_congr_eq (#v #cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform)
                (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures ws cok can1 c <==> ws cok can2 c)

val wf_stack_congr_eq (#v #cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform)
                      (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures wf_stack cok can1 k <==> wf_stack cok can2 k)

// ------------------------------------------------------------------ //
//  The machine invariant, and the obligation on the FFI               //
// ------------------------------------------------------------------ //

(**
 * **The machine invariant**: the control component is well scoped in the
 * environment its own stack offers, and the stack is well formed at top level.
 * `Stuck` is ruled out outright. `Hoop.Runtime.Metatheory` shows the predicate
 * is preserved by `step` (`step_preserves_wf`), whence a well-formed state
 * never reaches `Stuck` however long it runs (`progress`).
 *)
let wf_state (#v #cl: Type) (cok: clause_ok_t cl) (s: state v cl) : GTot prop =
  match s with
  | Done _ -> True
  | Stuck _ _ -> False
  | Step c k -> ws cok (can_in k) c /\ wf_stack cok (can_nothing ()) k

(**
 * **The condition imposed on the FFI parameter `apply`**: a clause well scoped in
 * `can`, applied to a payload and to a continuation itself well scoped in `can`,
 * yields a computation well scoped in `can`.
 *
 * **IMPORTANT** This condition is NOT provable inside F*, and not meant to be --
 * `apply` is supplied by the handwritten OCaml in `runtime/ml/hoop_ffi.ml`, which
 * calls out to an arbitrary PureScript closure whose body F* never sees. This is
 * therefore an assumption on that boundary — the obligation the PureScript side must
 * discharge, by construction of its `Hoop` monad, for the progress theorem to apply
 * to a real run. It appears only as a hypothesis of the theorems in `Hoop.Runtime.Metatheory`,
 * never as something this module claims.
 *)
let apply_ok
    (#v #cl: Type)
    (apply: apply_t v cl)
    (cok: clause_ok_t cl)
  : prop
  = forall (can: can_perform) (c: cl) (payload: list v) (kf: (v -> comp_tree v cl)).
      (cok can c /\ (forall (x: v). ws cok can (kf x))) ==> ws cok can (apply c payload kf)
