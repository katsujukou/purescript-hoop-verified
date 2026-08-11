(**
 * Well-scopedness: the proofs.
 *
 * Every definition of this module lives in the interface -- see the header
 * there for why the `prop`-level ones cannot be made opaque. What is left here
 * is the part a client never needs: the proofs of the lemmas the interface
 * declares, and the step-indexed congruence they run on.
 *)
module Hoop.Runtime.WellScopedness

open FStar.List.Tot

open Hoop.Runtime.Syntax
open Hoop.Runtime.Handlers
open Hoop.Runtime.Semantics

(* ------------------------------------------------------------------ *)
(*  Peeling the step index                                             *)
(*                                                                     *)
(*  These lemmas are the only place the index is ever peeled.           *)
(*  `Hoop.Runtime.Metatheory` assembles them into the `<==>` equations  *)
(*  of the structural definition, and the rest of the development works *)
(*  through those.                                                     *)
(*                                                                     *)
(*  Each forward direction needs a hint -- the solver has to be told to *)
(*  look at index `n + 1`, where the head constructor is unfolded --    *)
(*  while each backward direction goes through on its own, except under *)
(*  an `option`, where the `match` has to be split by hand.             *)
(* ------------------------------------------------------------------ *)

let ws_perform_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                  (eff op: string) (payload: list v)
  : Lemma (ws cok can (Perform eff op payload) <==> (eff =!= var_eff /\ can eff op))
  = assert (ws_n 1 cok can (Perform eff op payload) <==> (eff =!= var_eff /\ can eff op))

let ws_performS_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                   (eff op: string) (payload: list v)
  : Lemma (ws cok can (PerformS eff op payload) <==> (eff =!= var_eff /\ can eff op))
  = assert (ws_n 1 cok can (PerformS eff op payload) <==> (eff =!= var_eff /\ can eff op))

let ws_op_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
              (c: comp_tree v cl) (fn: v -> comp_tree v cl)
  : Lemma (requires ws cok can (Op c fn))
          (ensures ws cok can c /\ (forall (x: v). ws cok can (fn x)))
  = assert (forall (n: nat). ws_n (n + 1) cok can (Op c fn))

let ws_handle_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok can (Handle hs ret body))
          (ensures ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)
  = assert (ws_n 1 cok can (Handle hs ret body));
    assert (forall (n: nat). ws_n (n + 1) cok can (Handle hs ret body));
    (match ret with
      | None -> ()
      | Some r -> assert (forall (x: v) (n: nat). ws_n n cok can (r x)))

#push-options "--split_queries always"
let ws_handle_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                  (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (requires ws cok (extend hs can) body /\ handler_ok cok can hs /\ ret_ws cok can ret)
          (ensures ws cok can (Handle hs ret body))
  = match ret with
    | None -> ()
    | Some r -> assert (forall (x: v) (n: nat). ws_n n cok can (r x))
#pop-options

let ws_splice_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                  (frames: stack v cl) (body: comp_tree v cl)
  : Lemma (requires ws cok can (Splice frames body))
          (ensures wf_stack cok can frames /\ ws cok (can_in_with frames can) body)
  = assert (forall (n: nat). ws_n (n + 1) cok can (Splice frames body))

let ws_weave_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                 (oeff oop: string) (prepared: stack v cl) (body: comp_tree v cl)
  : Lemma (requires ws cok can (Weave oeff oop prepared body))
          (ensures wf_stack cok can prepared /\ ws cok (can_in_with prepared can) body)
  = assert (forall (n: nat). ws_n (n + 1) cok can (Weave oeff oop prepared body))

// The `Var` specialisation. Nothing is re-derived: the body conjunct the general
// lemma delivers is about `Var x` and is simply dropped.
let ws_resumed_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                   (frames: stack v cl) (x: v)
  : Lemma (requires ws cok can (resumed frames x)) (ensures wf_stack cok can frames)
  = ws_splice_fwd cok can frames (Var x)

let wf_stack_bind_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                      (fn: v -> comp_tree v cl) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (BindF fn :: rest))
          (ensures (forall (x: v). ws cok (can_in_with rest can) (fn x)) /\
                   wf_stack cok can rest)
  = assert (forall (n: nat). wf_stack_n (n + 1) cok can (BindF fn :: rest))

let wf_stack_prompt_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires wf_stack cok can (PromptF hs ret :: rest))
          (ensures handler_ok cok (can_in_with rest can) hs /\
                   ret_ws cok (can_in_with rest can) ret /\
                   wf_stack cok can rest)
  = assert (wf_stack_n 1 cok can (PromptF hs ret :: rest));
    assert (forall (n: nat). wf_stack_n (n + 1) cok can (PromptF hs ret :: rest));
    (match ret with
      | None -> ()
      | Some r -> assert (forall (x: v) (n: nat). ws_n n cok (can_in_with rest can) (r x)))

#push-options "--split_queries always"
let wf_stack_prompt_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (hs: handlers cl)
                        (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (requires handler_ok cok (can_in_with rest can) hs /\
                    ret_ws cok (can_in_with rest can) ret /\
                    wf_stack cok can rest)
          (ensures wf_stack cok can (PromptF hs ret :: rest))
  = match ret with
    | None -> ()
    | Some r -> assert (forall (x: v) (n: nat). ws_n n cok (can_in_with rest can) (r x))
#pop-options

(** **The clause judgement is congruent**: `clause_ok_congr` read through
    `handler_ok`. It has to live here rather than with the rest of the
    metatheory, because the step-indexed congruence below needs it and
    `Hoop.Runtime.Metatheory` is downstream of this module. *)
let handler_ok_congr (#cl: Type) (cok: clause_ok_t cl) (can1 can2: can_perform) (hs: handlers cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures handler_ok cok can1 hs <==> handler_ok cok can2 hs)
  = introduce forall (c: cl). (cok can1 c <==> cok can2 c)
    with assert (clause_ok_congr cok)

(* Congruence has to be proved at every index before it can be closed over,
   hence a pair of step-indexed lemmas mirroring `ws_n` / `wf_stack_n`.
   `private` in an implementation is out of reach even of a `friend`, which is
   what keeps the index from escaping through these. *)
private
let rec ws_n_congr (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can1 can2: can_perform)
                  (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures ws_n n cok can1 c <==> ws_n n cok can2 c)
          (decreases %[n; 1; 0])
  = if n = 0 then ()
    else
      match c with
      | Var _ -> ()
      | Perform _ _ _ -> ()
      | PerformS _ _ _ -> ()
      | Op inner fn ->
          ws_n_congr (n - 1) cok can1 can2 inner;
          introduce forall (x: v).
            (ws_n (n - 1) cok can1 (fn x) <==> ws_n (n - 1) cok can2 (fn x))
          with ws_n_congr (n - 1) cok can1 can2 (fn x)
      | Handle hs ret body ->
          assert (equiv_can (extend hs can1) (extend hs can2));
          ws_n_congr (n - 1) cok (extend hs can1) (extend hs can2) body;
          handler_ok_congr cok can1 can2 hs;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws_n (n - 1) cok can1 (r x) <==> ws_n (n - 1) cok can2 (r x))
              with ws_n_congr (n - 1) cok can1 can2 (r x))
      | Splice fs body ->
          wf_stack_n_congr n cok can1 can2 fs;
          // The body is judged under the frames, so the two environments it is
          // compared at are the *extended* ones -- equivalent because
          // `can_in_with` is pointwise in its second argument.
          assert (equiv_can (can_in_with fs can1) (can_in_with fs can2));
          ws_n_congr (n - 1) cok (can_in_with fs can1) (can_in_with fs can2) body
      // The same shape as `Splice`, and for the same reason: the body is judged
      // under the segment, so the two environments it is compared at are the
      // extended ones. The origin is not judged, so it is not matched on.
      | Weave _ _ prepared body ->
          wf_stack_n_congr n cok can1 can2 prepared;
          assert (equiv_can (can_in_with prepared can1) (can_in_with prepared can2));
          ws_n_congr (n - 1) cok (can_in_with prepared can1) (can_in_with prepared can2) body
      | ReadP _ -> ()
      | WriteP _ _ -> ()
      | NewP l _ body ->
          assert (equiv_can (extend_param l can1) (extend_param l can2));
          ws_n_congr (n - 1) cok (extend_param l can1) (extend_param l can2) body

and wf_stack_n_congr (#v #cl: Type) (n: nat) (cok: clause_ok_t cl) (can1 can2: can_perform)
                     (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can can1 can2)
          (ensures wf_stack_n n cok can1 k <==> wf_stack_n n cok can2 k)
          (decreases %[n; 0; length k])
  = if n = 0 then ()
    else
      match k with
      | [] -> ()
      | BindF fn :: rest ->
          assert (equiv_can (can_in_with rest can1) (can_in_with rest can2));
          wf_stack_n_congr n cok can1 can2 rest;
          introduce forall (x: v).
            (ws_n (n - 1) cok (can_in_with rest can1) (fn x) <==>
             ws_n (n - 1) cok (can_in_with rest can2) (fn x))
          with ws_n_congr (n - 1) cok (can_in_with rest can1) (can_in_with rest can2) (fn x)
      | ParamF _ _ :: rest -> wf_stack_n_congr n cok can1 can2 rest
      | PromptF hs ret :: rest ->
          assert (equiv_can (can_in_with rest can1) (can_in_with rest can2));
          wf_stack_n_congr n cok can1 can2 rest;
          handler_ok_congr cok (can_in_with rest can1) (can_in_with rest can2) hs;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws_n (n - 1) cok (can_in_with rest can1) (r x) <==>
                 ws_n (n - 1) cok (can_in_with rest can2) (r x))
              with ws_n_congr (n - 1) cok (can_in_with rest can1) (can_in_with rest can2) (r x))

let ws_congr_eq
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (can1 can2: can_perform)
    (c: comp_tree v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can can1 can2)
      (ensures ws cok can1 c <==> ws cok can2 c)
  = introduce forall (n: nat). (ws_n n cok can1 c <==> ws_n n cok can2 c)
    with ws_n_congr n cok can1 can2 c

let wf_stack_congr_eq
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (can1 can2: can_perform)
    (k: stack v cl)
  : Lemma
      (requires clause_ok_congr cok /\ equiv_can can1 can2)
      (ensures wf_stack cok can1 k <==> wf_stack cok can2 k)
  = introduce forall (n: nat). (wf_stack_n n cok can1 k <==> wf_stack_n n cok can2 k)
    with wf_stack_n_congr n cok can1 can2 k


(* ------------------------------------------------------------------ *)
(*  Peeling, for prompt-local state                                    *)
(* ------------------------------------------------------------------ *)

let ws_newp_fwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                (l: string) (init: v) (body: comp_tree v cl)
  : Lemma (requires ws cok can (NewP l init body))
          (ensures ws cok (extend_param l can) body)
  = assert (forall (n: nat). ws_n (n + 1) cok can (NewP l init body))

let ws_newp_bwd (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                (l: string) (init: v) (body: comp_tree v cl)
  : Lemma (requires ws cok (extend_param l can) body)
          (ensures ws cok can (NewP l init body))
  = ()

let ws_readp_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (l: string)
  : Lemma (ws cok can (ReadP l <: comp_tree v cl) <==> can var_eff l)
  = assert (ws_n 1 cok can (ReadP l <: comp_tree v cl) <==> can var_eff l)

let ws_writep_eq (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform) (l: string) (x: v)
  : Lemma (ws cok can (WriteP l x <: comp_tree v cl) <==> can var_eff l)
  = assert (ws_n 1 cok can (WriteP l x <: comp_tree v cl) <==> can var_eff l)
