module Hoop.Runtime.Metatheory

open FStar.List.Tot

open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics
open Hoop.Runtime.WellScopedness

let rec find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures find_prompt_partitions_correctness eff op k)
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      // The search branches on `lookup_handler`, `handles` on `lookup_clause`;
      // the coherence lemma is what makes the two branchings the same one.
      lookup_handler_agrees hs eff op;
      (match lookup_handler hs eff op with
        | Some _ -> ()
        | None -> find_prompt_partitions eff op rest)
    | _ :: rest -> find_prompt_partitions eff op rest

let rec find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures find_prompt_last_correctness eff op k)
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      // The search branches on `lookup_handler`, `handles` on `lookup_clause`;
      // the coherence lemma is what makes the two branchings the same one.
      lookup_handler_agrees hs eff op;
      (match lookup_handler hs eff op with
        | Some _ -> ()
        | None -> find_prompt_last eff op rest)
    | _ :: rest -> find_prompt_last eff op rest

let rec find_prompt_innermost
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures (find_prompt_innermost_correctness eff op k))
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      // The search branches on `lookup_handler`, `handles` on `lookup_clause`;
      // the coherence lemma is what makes the two branchings the same one.
      lookup_handler_agrees hs eff op;
      (match lookup_handler hs eff op with
        | Some _ -> ()
        | None ->
          (find_prompt_last eff op rest;
            find_prompt_innermost eff op rest))
    | _ :: rest ->
      (find_prompt_last eff op rest;
        find_prompt_innermost eff op rest)

(* ------------------------------------------------------------------ *)

// The table being abstract, neither of these is an induction any more: the
// induction is on `table hs` and lives in `Hoop.Runtime.Handlers`. What is left
// here is the transport across `lookup_clause_spec`.
let lookup_clause_memP
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures (lookup_clause_soundness hs eff op))
  = assoc_clause_memP (table hs) eff op

let lookup_clause_none
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires None? (lookup_clause hs eff op))
      (ensures lookup_clause_completeness hs eff op)
  = assoc_clause_none (table hs) eff op

let step_perform
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures
          (let Some (captured, found, below) = find_prompt eff op k in
              (match found.kind with
                | KScoped ->
                    step apply apply_s (Step (Perform eff op payload) k) ==
                      Rejected (ClauseKindMismatch eff op KOrdinaryOperation KScoped)
                | _ ->
                    step apply apply_s (Step (Perform eff op payload) k) ==
                      Step (apply found.body payload (kont_of captured)) below) /\
              captured @ below == k))
  = find_prompt_partitions eff op k

let step_performS
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
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
  = find_prompt_partitions eff op k

let step_perform_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply apply_s (Step (Perform eff op payload) k) == Stuck eff op)
  = ()

let step_performS_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply apply_s (Step (PerformS eff op payload) k) == Stuck eff op)
  = ()

(* ------------------------------------------------------------------ *)

let steps_zero
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma (steps apply apply_s 0 s == s)
  = ()

let rec steps_terminal
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s \/ Rejected? s)
      (ensures steps apply apply_s n s == s)
      (decreases n)
  = if n = 0 then ()
    else steps_terminal apply apply_s (n - 1) s

let rec steps_add
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n m: nat) (s: state v cl)
  : Lemma
      (ensures steps apply apply_s (n + m) s == steps apply apply_s m (steps apply apply_s n s))
      (decreases n)
  = if n = 0 then ()
    else
      match s with
      | Done _ ->
          steps_terminal apply apply_s (n + m) s;
          steps_terminal apply apply_s n s;
          steps_terminal apply apply_s m s
      | Stuck _ _ ->
          steps_terminal apply apply_s (n + m) s;
          steps_terminal apply apply_s n s;
          steps_terminal apply apply_s m s
      | Rejected _ ->
          steps_terminal apply apply_s (n + m) s;
          steps_terminal apply apply_s n s;
          steps_terminal apply apply_s m s
      | Step _ _ ->
          steps_add apply apply_s (n - 1) m (step apply apply_s s)

let steps_unfold
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Step? s)
      (ensures steps apply apply_s (n + 1) s == steps apply apply_s n (step apply apply_s s))
  = ()

let steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply apply_s n s))
      (ensures steps apply apply_s (n + m) s == steps apply apply_s n s)
  = steps_add apply apply_s n m s;
    steps_terminal apply apply_s m (steps apply apply_s n s)
(* ------------------------------------------------------------------ *)
(* Well-scopedness: the defining equations                             *)
(*                                                                     *)
(* Each equation is proved in two halves. The half that peels the step  *)
(* index lives in `Hoop.Runtime`, since `ws_n` and `wf_stack_n` are     *)
(* private there; what is left here is the assembly into an `<==>`.     *)
(* ------------------------------------------------------------------ *)

let ws_var (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (x: v)
  : Lemma (ws cok a (Var x <: comp_tree v cl))
  = ()

let ws_perform (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
               (eff op: string) (payload: list v)
  : Lemma (ws cok a (Perform eff op payload <: comp_tree v cl) <==>
           (eff =!= var_eff /\ a eff op))
  = ws_perform_eq #v #cl cok a eff op payload

let ws_performS (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
                (eff op: string) (payload: list v)
  : Lemma (ws cok a (PerformS eff op payload <: comp_tree v cl) <==>
           (eff =!= var_eff /\ a eff op))
  = ws_performS_eq #v #cl cok a eff op payload

let ws_op (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
          (c: comp_tree v cl) (fn: v -> comp_tree v cl)
  : Lemma (ws cok a (Op c fn) <==> (ws cok a c /\ (forall (x: v). ws cok a (fn x))))
  = (introduce ws cok a (Op c fn) ==> (ws cok a c /\ (forall (x: v). ws cok a (fn x)))
     with ws_op_fwd cok a c fn);
    (introduce (ws cok a c /\ (forall (x: v). ws cok a (fn x))) ==> ws cok a (Op c fn)
     with ())

let ws_handle
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
  : Lemma
      (ws cok a (Handle hs ret body) <==>
      (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret))
  = introduce
      ws cok a (Handle hs ret body) ==>
        (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret)
     with ws_handle_fwd cok a hs ret body;
    introduce
      (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret) ==>
        ws cok a (Handle hs ret body)
     with ws_handle_bwd cok a hs ret body

let ws_splice
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (body: comp_tree v cl)
  : Lemma (ws cok a (Splice frames body) <==>
            (wf_stack cok a frames /\ ws cok (can_in_with frames a) body))
  = introduce
      ws cok a (Splice frames body) ==>
        (wf_stack cok a frames /\ ws cok (can_in_with frames a) body)
    with ws_splice_fwd cok a frames body;
    // The backward direction goes through by unfolding `ws` and `wf_stack`: at
    // each index the two conjuncts are instances of the two hypotheses, one at
    // `n` and one at `n - 1`.
    ()

// The same equation at the other splicing node. Nothing about borrowability
// appears in either direction, and nothing about the origin -- see the
// interface.
let ws_weave
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (oeff oop: string)
    (prepared: stack v cl)
    (body: comp_tree v cl)
  : Lemma (ws cok a (Weave oeff oop prepared body) <==>
            (wf_stack cok a prepared /\ ws cok (can_in_with prepared a) body))
  = introduce
      ws cok a (Weave oeff oop prepared body) ==>
        (wf_stack cok a prepared /\ ws cok (can_in_with prepared a) body)
    with ws_weave_fwd cok a oeff oop prepared body;
    ()

// The `Var` specialisation. `ws cok _ (Var x)` is `True`, so the body conjunct
// carries no information in either direction and this is `ws_splice` verbatim.
let ws_resumed
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (frames: stack v cl)
    (x: v)
  : Lemma (ws cok a (resumed frames x) <==> wf_stack cok a frames)
  = ws_splice cok a frames (Var x)

let wf_stack_nil
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
  : Lemma (wf_stack cok a ([] <: stack v cl))
  = ()

let wf_stack_bind
    (#v #cl: Type)
    (cok: clause_ok_t cl)
    (a: can_perform)
    (fn: (v -> comp_tree v cl))
    (rest: stack v cl)
  : Lemma
      (wf_stack cok a (BindF fn :: rest) <==>
            ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest))
  = introduce
      wf_stack cok a (BindF fn :: rest) ==>
        ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest)
    with wf_stack_bind_fwd cok a fn rest

let wf_stack_prompt
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
  = introduce
      wf_stack cok a (PromptF hs ret :: rest) ==>
        (handler_ok cok (can_in_with rest a) hs /\
          ret_ws cok (can_in_with rest a) ret /\ wf_stack cok a rest)
    with wf_stack_prompt_fwd cok a hs ret rest;
    introduce
      (handler_ok cok (can_in_with rest a) hs /\
        ret_ws cok (can_in_with rest a) ret /\ wf_stack cok a rest
      ) ==> wf_stack cok a (PromptF hs ret :: rest)
    with wf_stack_prompt_bwd cok a hs ret rest

(* ------------------------------------------------------------------ *)
(* Congruence in the environment                                       *)
(* ------------------------------------------------------------------ *)

let ws_congr (#v #cl: Type) (cok: clause_ok_t cl) (a1 a2: can_perform) (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can a1 a2)
          (ensures ws cok a1 c <==> ws cok a2 c)
  = ws_congr_eq cok a1 a2 c

let wf_stack_congr (#v #cl: Type) (cok: clause_ok_t cl) (a1 a2: can_perform) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can a1 a2)
          (ensures wf_stack cok a1 k <==> wf_stack cok a2 k)
  = wf_stack_congr_eq cok a1 a2 k

(* ------------------------------------------------------------------ *)
(* How the environment reacts to the stack surgery `step` performs     *)
(* ------------------------------------------------------------------ *)

let av_bind (#v #cl: Type) (fn: v -> comp_tree v cl) (k: stack v cl) (a: can_perform)
  : Lemma (equiv_can (can_in_with (BindF fn :: k) a) (can_in_with k a))
  = ()

let av_prompt (#v #cl: Type) (hs: handlers cl) (ret: option (v -> comp_tree v cl))
              (k: stack v cl) (a: can_perform)
  : Lemma (equiv_can (can_in_with (PromptF hs ret :: k) a) (extend hs (can_in_with k a)))
  = ()

let av_append (#v #cl: Type) (k1 k2: stack v cl) (a: can_perform)
  : Lemma (equiv_can (can_in_with (k1 @ k2) a) (can_in_with k1 (can_in_with k2 a)))
  = introduce forall (e o: string).
      (can_in_with (k1 @ k2) a) e o <==> (can_in_with k1 (can_in_with k2 a)) e o
    with append_memP_forall k1 k2

(* ------------------------------------------------------------------ *)
(* Splitting and joining a well-formed stack                           *)
(* ------------------------------------------------------------------ *)

let rec wf_stack_append (#v #cl: Type) (cok: clause_ok_t cl) (k1 k2: stack v cl) (a: can_perform)
  : Lemma (requires clause_ok_congr cok)
          (ensures wf_stack cok a (k1 @ k2) <==> (wf_stack cok (can_in_with k2 a) k1 /\ wf_stack cok a k2))
          (decreases k1)
  = match k1 with
    | [] -> wf_stack_nil #v #cl cok (can_in_with k2 a)
    | f :: r1 ->
      wf_stack_append cok r1 k2 a;
      av_append r1 k2 a;
      (match f with
        | ParamF _ _ -> ()
        | BindF fn ->
          wf_stack_bind cok a fn (r1 @ k2);
          wf_stack_bind cok (can_in_with k2 a) fn r1;
          introduce forall (x: v).
            (ws cok (can_in_with (r1 @ k2) a) (fn x) <==> ws cok (can_in_with r1 (can_in_with k2 a)) (fn x))
          with ws_congr cok (can_in_with (r1 @ k2) a) (can_in_with r1 (can_in_with k2 a)) (fn x)
        | PromptF hs ret ->
          wf_stack_prompt cok a hs ret (r1 @ k2);
          wf_stack_prompt cok (can_in_with k2 a) hs ret r1;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws cok (can_in_with (r1 @ k2) a) (r x) <==>
                 ws cok (can_in_with r1 (can_in_with k2 a)) (r x))
              with ws_congr cok (can_in_with (r1 @ k2) a) (can_in_with r1 (can_in_with k2 a)) (r x)))

let wf_stack_split_prompt (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
                     (k1: stack v cl) (hs: handlers cl)
                     (ret: option (v -> comp_tree v cl)) (k2: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_stack cok a (k1 @ (PromptF hs ret :: k2)))
          (ensures handler_ok cok (can_in_with k2 a) hs)
  = wf_stack_append cok k1 (PromptF hs ret :: k2) a;
    wf_stack_prompt cok a hs ret k2

(* ------------------------------------------------------------------ *)
(* The segment a scope runs under                                      *)
(* ------------------------------------------------------------------ *)

(* `can_in_with` reads a stack through exactly two searches, so `borrow_can`
   below is those two lemmas and nothing else. Both are stated through the
   searches rather than through `handled_in` / `param_in`, whose existentials
   over `memP` would have to be taken apart and rebuilt at every frame; the
   refinements on `find_prompt` and `find_param` hand back the propositional
   readings for free. Private: they say nothing a client wants that
   `borrow_can` does not say better. *)

private
let rec borrow_handled (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (ensures Some? (find_prompt eff op (borrow k)) <==> Some? (find_prompt eff op k))
          (decreases k)
  = match k with
    // A bind frame handles nothing, so removing it removes no answer.
    | BindF _ :: r -> borrow_handled eff op r
    | ParamF _ _ :: r -> borrow_handled eff op r
    // The search branches on `lookup_handler hs`, which `borrow` leaves alone;
    // it never looks at `ret`, which is the only thing `borrow` touches here.
    | PromptF _ _ :: r -> borrow_handled eff op r
    | [] -> ()

private
let rec borrow_param (#v #cl: Type) (l: string) (k: stack v cl)
  : Lemma (ensures param_in l (borrow k) <==> param_in l k) (decreases k)
  = match k with
    | BindF _ :: r -> borrow_param l r
    // The cell survives with its label AND its value, so the search takes the
    // same branch on both sides -- and at a matching label both sides stop.
    | ParamF l' _ :: r -> if l' = l then () else borrow_param l r
    | PromptF _ _ :: r -> borrow_param l r
    | [] -> ()

let borrow_can (#v #cl: Type) (k: stack v cl) (a: can_perform)
  : Lemma (equiv_can (can_in_with (borrow k) a) (can_in_with k a))
  = introduce forall (eff op: string).
      can_in_with (borrow k) a eff op <==> can_in_with k a eff op
    with (borrow_handled eff op k; borrow_param op k)

let prepare_scope_can (#v #cl: Type) (intermediates: stack v cl)
                      (owner: frame v cl { PromptF? owner }) (can: can_perform)
  : Lemma (equiv_can (can_in_with (prepare_scope intermediates owner) can)
                     (can_in_with (intermediates @ [owner]) can))
  = // Both sides split at the same place -- the owner is common to them -- so
    // the whole difference is `borrow` on the part above it.
    av_append (borrow intermediates) [owner] can;
    av_append intermediates [owner] can;
    borrow_can intermediates (can_in_with [owner] can)

let rec borrow_wf (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_stack cok a k)
          (ensures wf_stack cok a (borrow k))
          (decreases k)
  = match k with
    | [] -> wf_stack_nil #v #cl cok a
    // The bind frame's own obligation is DISCHARGED BY BEING DROPPED: the
    // suspended continuation is gone, so nothing is owed for it. Nothing below
    // it changes, so the rest is the induction hypothesis verbatim.
    | BindF fn :: r ->
      wf_stack_bind cok a fn r;
      borrow_wf cok a r
    // A cell owes nothing either way -- it suspends no computation and installs
    // no table -- so both sides reduce to the tail and the hypothesis is the
    // whole case. (`wf_stack_param` says exactly this, but is declared further
    // down the interface than this section sits; the definition unfolds here
    // for the same reason its own proof is `()`.) The cell is carried across so
    // that the CAPABILITY survives, which is `borrow_can`'s business, not this
    // lemma's.
    | ParamF _ _ :: r -> borrow_wf cok a r
    | PromptF hs ret :: r ->
      wf_stack_prompt cok a hs ret r;
      borrow_wf cok a r;
      // THE ONE PLACE ANY WORK HAPPENS. The table's obligation was recorded
      // against `r` and must now hold against `borrow r`, which is a different
      // stack whenever `r` held a `BindF`. `borrow_can` -- the statement one
      // suffix down -- says the two offer the same capabilities, and
      // `clause_ok_congr` is what turns that into the same judgement.
      borrow_can r a;
      handler_ok_congr cok (can_in_with r a) (can_in_with (borrow r) a) hs;
      // `ret_ws _ _ None` is `True`, so the return clause's obligation is not
      // transported: it is discarded with the clause.
      wf_stack_prompt cok a hs (None #(v -> comp_tree v cl)) (borrow r)

let prepare_scope_wf (#v #cl: Type) (cok: clause_ok_t cl) (intermediates: stack v cl)
                     (owner: frame v cl { PromptF? owner }) (can: can_perform)
  : Lemma (requires clause_ok_congr cok /\ wf_stack cok can (intermediates @ [owner]))
          (ensures wf_stack cok can (prepare_scope intermediates owner))
  = // Split at the owner, borrow above it, join back. The second conjunct
    // `wf_stack cok can [owner]` is LITERALLY THE SAME PROPOSITION on both
    // sides of the surgery -- it is not re-proved, transported, or weakened.
    wf_stack_append cok intermediates [owner] can;
    borrow_wf cok (can_in_with [owner] can) intermediates;
    wf_stack_append cok (borrow intermediates) [owner] can

(* ------------------------------------------------------------------ *)
(* Preservation of the machine invariant, one transition at a time     *)
(* ------------------------------------------------------------------ *)

let pres_op (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
            (inner: comp_tree v cl) (fn: v -> comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Op inner fn) k))
          (ensures wf_state cok (step apply apply_s (Step (Op inner fn) k)))
  = ws_op cok (can_in k) inner fn;
    av_bind fn k (can_nothing ());
    ws_congr cok (can_in k) (can_in (BindF fn :: k)) inner;
    wf_stack_bind cok (can_nothing ()) fn k

let pres_handle (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                (hs: handlers cl) (ret: option (v -> comp_tree v cl))
                (body: comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Handle hs ret body) k))
          (ensures wf_state cok (step apply apply_s (Step (Handle hs ret body) k)))
  = ws_handle cok (can_in k) hs ret body;
    av_prompt hs ret k (can_nothing ());
    ws_congr cok (extend hs (can_in k)) (can_in (PromptF hs ret :: k)) body;
    wf_stack_prompt cok (can_nothing ()) hs ret k

let pres_var (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
             (value: v) (k: stack v cl)
  : Lemma (requires wf_state cok (Step (Var value <: comp_tree v cl) k))
          (ensures wf_state cok (step apply apply_s (Step (Var value <: comp_tree v cl) k)))
  = match k with
    | [] -> ()
    | ParamF _ _ :: rest -> ()
    | BindF fn :: rest -> wf_stack_bind cok (can_nothing ()) fn rest
    | PromptF hs ret :: rest -> wf_stack_prompt cok (can_nothing ()) hs ret rest

let pres_splice (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                (frames: stack v cl) (body: comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Splice frames body) k))
          (ensures wf_state cok (step apply apply_s (Step (Splice frames body) k)))
  = ws_splice cok (can_in k) frames body;
    // The stack: `frames` is well formed over `k`, so the join is.
    wf_stack_append cok frames k (can_nothing ());
    // The body: `ws_splice` recorded it against the environment `frames` offers
    // on top of `k`'s, and after the splice the machine runs it under the joined
    // stack. `av_append` says those are the same environment.
    av_append frames k (can_nothing ());
    ws_congr cok (can_in_with frames (can_in k)) (can_in (frames @ k)) body

// The `Var` specialisation, the transition `continue` takes. The body obligation
// `pres_splice` discharges is about `Var value` and is vacuous, so nothing here
// is re-derived.
let pres_resumed (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                 (captured: stack v cl) (value: v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (resumed captured value) k))
          (ensures wf_state cok (step apply apply_s (Step (resumed captured value) k)))
  = pres_splice cok apply apply_s captured (Var value) k

#push-options "--split_queries always"
let pres_perform (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                 (eff op: string) (payload: list v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\
                    wf_state cok (Step (Perform eff op payload) k))
          (ensures wf_state cok (step apply apply_s (Step (Perform eff op payload) k)))
  = ws_perform #v #cl cok (can_in k) eff op payload;
    assert (Some? (find_prompt eff op k));
    let Some (captured, found, below) = find_prompt eff op k in
    step_perform eff op payload k apply apply_s;
    find_prompt_partitions eff op k;
    find_prompt_last eff op k;
    assert (captured @ below == k);
    assert (Cons? captured);
    (* the prompt that owns `found` is the last frame of `captured` *)
    append_init_last captured;
    append_assoc (init captured) [last captured] below;
    assert (k == init captured @ (last captured :: below));
    assert (PromptF? (last captured));
    let PromptF phs pret = last captured in
    assert (lookup_handler phs eff op == Some found);
    (* `handler_ok` is stated of `lookup_clause`, which is where the coherence
       lemma is spent: the clause this prompt dispatches is `found.body`. *)
    lookup_handler_agrees phs eff op;
    assert (lookup_clause phs eff op == Some found.body);
    wf_stack_split_prompt cok (can_nothing ()) (init captured) phs pret below;
    assert (handler_ok cok (can_in below) phs);
    assert (cok (can_in below) found.body);
    (* the captured segment is well formed on top of `below` *)
    wf_stack_append cok captured below (can_nothing ());
    assert (wf_stack cok (can_in below) captured);
    let kf : v -> comp_tree v cl = kont_of captured in
    introduce forall (x: v). ws cok (can_in below) (kf x)
    with ws_resumed cok (can_in below) captured x;
    assert (ws cok (can_in below) (apply found.body payload kf))
#pop-options

#push-options "--split_queries always"
let pres_performS (#v #cl: Type) (cok: clause_ok_t cl)
                  (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                  (eff op: string) (payload: list v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_scoped_ok apply_s cok /\
                    wf_state cok (Step (PerformS eff op payload) k))
          (ensures wf_state cok (step apply apply_s (Step (PerformS eff op payload) k)))
  = ws_performS #v #cl cok (can_in k) eff op payload;
    assert (Some? (find_prompt eff op k));
    let Some (captured, found, below) = find_prompt eff op k in
    step_performS eff op payload k apply apply_s;
    match found.kind with
    // Refused at the boundary. `wf_state (Rejected _)` is `True`, and there is
    // nothing here to prove -- which is the whole point of the outcome being
    // separate from `Stuck`.
    | KFull -> ()
    | KFast -> ()
    | KScoped ->
      find_prompt_partitions eff op k;
      find_prompt_last eff op k;
      assert (captured @ below == k);
      assert (Cons? captured);
      (* the owner: the prompt holding `found`, and the last frame of the
         captured segment *)
      append_init_last captured;
      append_assoc (init captured) [last captured] below;
      assert (k == init captured @ (last captured :: below));
      assert (PromptF? (last captured));
      let PromptF phs pret = last captured in
      assert (lookup_handler phs eff op == Some found);
      lookup_handler_agrees phs eff op;
      wf_stack_split_prompt cok (can_nothing ()) (init captured) phs pret below;
      assert (cok (can_in below) found.body);
      (* the captured segment is well formed on top of `below`, which is both the
         continuation's obligation and the input to the weave's *)
      wf_stack_append cok captured below (can_nothing ());
      assert (wf_stack cok (can_in below) captured);
      let kf : v -> comp_tree v cl = kont_of captured in
      introduce forall (x: v). ws cok (can_in below) (kf x)
      with ws_resumed cok (can_in below) captured x;
      (* THE WEAVE. `can_clause` is the environment the clause runs in, and
         `can_site` the one the perform site had; the machine owes the passage
         from the second to the first, and pays it here. *)
      let can_clause = can_in below in
      let can_site = can_in_with captured can_clause in
      let prepared = prepare_captured_fast captured in
      prepare_captured_is_prepare_scope (init captured) (last captured);
      assert (prepared == prepare_scope (init captured) (last captured));
      // well formed: the borrowed intermediates carry no obligation the captured
      // ones did not, and the owner's are reused unchanged.
      prepare_scope_wf cok (init captured) (last captured) can_clause;
      assert (wf_stack cok can_clause prepared);
      // and it offers the same capabilities, so a computation well scoped at the
      // perform site is well scoped under it.
      prepare_scope_can (init captured) (last captured) can_clause;
      introduce forall (d: comp_tree v cl).
        ws cok can_site d ==> ws cok can_clause (weave_of eff op prepared d)
      with introduce _ ==> _
      with begin
        ws_congr cok can_site (can_in_with prepared can_clause) d;
        ws_weave cok can_clause eff op prepared d
      end;
      assert (weave_ok cok can_site can_clause (weave_of eff op prepared));
      assert (ws cok can_clause (apply_s found.body payload (weave_of eff op prepared) kf))
#pop-options

let pres_weave (#v #cl: Type) (cok: clause_ok_t cl)
               (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
               (oeff oop: string)
               (prepared: stack v cl) (body: comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Weave oeff oop prepared body) k))
          (ensures wf_state cok (step apply apply_s (Step (Weave oeff oop prepared body) k)))
  = match scope_blockers prepared with
    // The borrow is refused: terminal, and well formed by `wf_state`'s own arm.
    // The origin travels into the rejection, where nothing is judged of it.
    | _ :: _ -> ()
    // The borrow is taken, and from here this is `pres_splice` verbatim at the
    // prepared segment.
    | [] ->
      ws_weave cok (can_in k) oeff oop prepared body;
      wf_stack_append cok prepared k (can_nothing ());
      av_append prepared k (can_nothing ());
      ws_congr cok (can_in_with prepared (can_in k)) (can_in (prepared @ k)) body

(* ------------------------------------------------------------------ *)
(* Preservation for prompt-local state                                 *)
(* ------------------------------------------------------------------ *)

let wf_stack_param (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                   (l: string) (x: v) (rest: stack v cl)
  : Lemma (wf_stack cok can (ParamF l x :: rest) <==> wf_stack cok can rest)
  = ()

let rec set_param_handled (#v #cl: Type) (l: string) (x: v) (k k': stack v cl) (eff op: string)
  : Lemma (requires set_param l x k == Some k')
          (ensures Some? (find_prompt eff op k') <==> Some? (find_prompt eff op k))
          (decreases k)
  = match k with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then ()
        else (let Some rest' = set_param l x rest in
              set_param_handled l x rest rest' eff op)
    | f :: rest ->
        let Some rest' = set_param l x rest in
        set_param_handled l x rest rest' eff op

let rec set_param_param_in (#v #cl: Type) (l: string) (x: v) (k k': stack v cl) (l2: string)
  : Lemma (requires set_param l x k == Some k')
          (ensures Some? (find_param l2 k') <==> Some? (find_param l2 k))
          (decreases k)
  = match k with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then ()
        else (let Some rest' = set_param l x rest in
              set_param_param_in l x rest rest' l2)
    | f :: rest ->
        let Some rest' = set_param l x rest in
        set_param_param_in l x rest rest' l2

let set_param_equiv_can (#v #cl: Type) (l: string) (x: v) (k k': stack v cl) (can: can_perform)
  : Lemma (requires set_param l x k == Some k')
          (ensures equiv_can (can_in_with k' can) (can_in_with k can))
  = introduce forall (eff op: string). (can_in_with k' can) eff op <==> (can_in_with k can) eff op
    with (set_param_handled l x k k' eff op; set_param_param_in l x k k' op)

let rec set_param_wf (#v #cl: Type) (cok: clause_ok_t cl) (can: can_perform)
                     (l: string) (x: v) (k k': stack v cl)
  : Lemma (requires clause_ok_congr cok /\ set_param l x k == Some k' /\ wf_stack cok can k)
          (ensures wf_stack cok can k')
          (decreases k)
  = match k with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then (wf_stack_param cok can l' y rest; wf_stack_param cok can l x rest)
        else begin
          let Some rest' = set_param l x rest in
          wf_stack_param cok can l' y rest;
          set_param_wf cok can l x rest rest';
          wf_stack_param cok can l' y rest'
        end
    | BindF fn :: rest ->
        let Some rest' = set_param l x rest in
        wf_stack_bind cok can fn rest;
        set_param_wf cok can l x rest rest';
        set_param_equiv_can l x rest rest' can;
        introduce forall (y: v). ws cok (can_in_with rest' can) (fn y)
        with ws_congr cok (can_in_with rest can) (can_in_with rest' can) (fn y);
        wf_stack_bind cok can fn rest'
    | PromptF hs ret :: rest ->
        let Some rest' = set_param l x rest in
        wf_stack_prompt cok can hs ret rest;
        set_param_wf cok can l x rest rest';
        set_param_equiv_can l x rest rest' can;
        handler_ok_congr cok (can_in_with rest can) (can_in_with rest' can) hs;
        (match ret with
          | None -> ()
          | Some r ->
            introduce forall (y: v). ws cok (can_in_with rest' can) (r y)
            with ws_congr cok (can_in_with rest can) (can_in_with rest' can) (r y));
        wf_stack_prompt cok can hs ret rest'

let pres_newp (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
              (l: string) (init: v) (body: comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (NewP l init body) k))
          (ensures wf_state cok (step apply apply_s (Step (NewP l init body) k)))
  = ws_newp_fwd cok (can_in k) l init body;
    assert (ws cok (extend_param l (can_in k)) body);
    assert (equiv_can (extend_param l (can_in k)) (can_in (ParamF l init :: k)));
    ws_congr_eq cok (extend_param l (can_in k)) (can_in (ParamF l init :: k)) body;
    wf_stack_param cok (can_nothing ()) l init k

let pres_readp (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
               (l: string) (k: stack v cl)
  : Lemma (requires wf_state cok (Step (ReadP l <: comp_tree v cl) k))
          (ensures wf_state cok (step apply apply_s (Step (ReadP l <: comp_tree v cl) k)))
  = ws_readp_eq #v #cl cok (can_in k) l

let pres_writep (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                (l: string) (x: v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\
                    wf_state cok (Step (WriteP l x <: comp_tree v cl) k))
          (ensures wf_state cok (step apply apply_s (Step (WriteP l x <: comp_tree v cl) k)))
  = ws_writep_eq #v #cl cok (can_in k) l x;
    let Some k' = set_param l x k in
    set_param_wf cok (can_nothing ()) l x k k'

let step_preserves_wf (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
          (ensures wf_state cok (step apply apply_s s))
  = match s with
    | Done _ -> ()
    | Stuck _ _ -> ()
    // A terminal state steps to itself, and `wf_state (Rejected _)` is `True`,
    // so preservation here is unconditional -- no borrowability hypothesis, and
    // none available to use.
    | Rejected _ -> ()
    | Step c k ->
      (match c with
        | Op inner fn -> pres_op cok apply apply_s inner fn k
        | Var value -> pres_var cok apply apply_s value k
        | Handle hs ret body -> pres_handle cok apply apply_s hs ret body k
        | Splice frames body -> pres_splice cok apply apply_s frames body k
        | Perform eff op payload -> pres_perform cok apply apply_s eff op payload k
        | PerformS eff op payload -> pres_performS cok apply apply_s eff op payload k
        | Weave oeff oop prepared body -> pres_weave cok apply apply_s oeff oop prepared body k
        | NewP l init body -> pres_newp cok apply apply_s l init body k
        | ReadP l -> pres_readp cok apply apply_s l k
        | WriteP l x -> pres_writep cok apply apply_s l x k)

let step_progress (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
          (ensures ~(Stuck? (step apply apply_s s)))
  = step_preserves_wf cok apply apply_s s

(* ------------------------------------------------------------------ *)
(* Progress                                                            *)
(* ------------------------------------------------------------------ *)

let rec steps_preserves_wf (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                           (n: nat) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
          (ensures wf_state cok (steps apply apply_s n s))
          (decreases n)
  = if n = 0 then ()
    else
      match s with
      | Done _ -> ()
      | Stuck _ _ -> ()
      | Rejected _ -> ()
      | Step _ _ ->
        step_preserves_wf cok apply apply_s s;
        steps_preserves_wf cok apply apply_s (n - 1) (step apply apply_s s)

let progress (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl) (n: nat) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
          (ensures ~(Stuck? (steps apply apply_s n s)))
  = steps_preserves_wf cok apply apply_s n s

let load_wf (#v #cl: Type) (cok: clause_ok_t cl) (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ ws cok (can_nothing ()) c)
          (ensures wf_state cok (load c))
  = wf_stack_nil #v #cl cok (can_nothing ());
    ws_congr cok (can_nothing ()) (can_in ([] <: stack v cl)) c

let wf_never_stuck (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ wf_state cok s)
          (ensures never_stuck apply apply_s s)
  = introduce forall (n: nat). ~(Stuck? (steps apply apply_s n s))
    with progress cok apply apply_s n s

let load_never_stuck (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
                     (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ apply_scoped_ok apply_s cok /\ ws cok (can_nothing ()) c)
          (ensures never_stuck apply apply_s (load c))
  = load_wf cok c;
    wf_never_stuck cok apply apply_s (load c)

let steps_done_unique
    (#v #cl : Type)
    (apply: apply_t v cl) (apply_s: scoped_apply_t v cl)
    (n m : nat)
    (s : state v cl)
  : Lemma
      (requires Done? (steps apply apply_s n s) /\ Done? (steps apply apply_s m s))
      (ensures steps apply apply_s n s == steps apply apply_s m s)
  = if n <= m then steps_stable apply apply_s n (m - n) s
    else steps_stable apply apply_s m (n - m) s

(* ================================================================== *)
(*  The var-semantics theorem -- see the interface for what it is for. *)
(* ================================================================== *)

let rec set_param_local (#v #cl: Type) (l: string) (x: v) (k k': stack v cl) (l2: string)
  : Lemma (requires set_param l x k == Some k' /\ l2 =!= l)
          (ensures find_param l2 k' == find_param l2 k)
          (decreases k)
  = match k with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then ()
        else (let Some rest' = set_param l x rest in set_param_local l x rest rest' l2)
    | f :: rest ->
        let Some rest' = set_param l x rest in
        set_param_local l x rest rest' l2

let rec set_param_hits (#v #cl: Type) (l: string) (x: v) (k k': stack v cl)
  : Lemma (requires set_param l x k == Some k')
          (ensures find_param l k' == Some x)
          (decreases k)
  = match k with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then ()
        else (let Some rest' = set_param l x rest in set_param_hits l x rest rest')
    | f :: rest ->
        let Some rest' = set_param l x rest in
        set_param_hits l x rest rest'

let rec set_param_splice (#v #cl: Type) (l: string) (x: v) (cap below: stack v cl)
  : Lemma (requires None? (find_param l cap))
          (ensures
            (match set_param l x below with
              | None -> None? (set_param l x (cap @ below))
              | Some below' -> set_param l x (cap @ below) == Some (cap @ below')))
          (decreases cap)
  = match cap with
    | [] -> ()
    | ParamF l' y :: rest -> set_param_splice l x rest below
    | f :: rest -> set_param_splice l x rest below

let rec set_param_captured (#v #cl: Type) (l: string) (x: v) (cap below: stack v cl)
  : Lemma (requires Some? (find_param l cap))
          (ensures
            (let Some cap' = set_param l x cap in
             set_param l x (cap @ below) == Some (cap' @ below)))
          (decreases cap)
  = match cap with
    | [] -> ()
    | ParamF l' y :: rest ->
        if l' = l then () else set_param_captured l x rest below
    | f :: rest -> set_param_captured l x rest below
