module Hoop.Runtime.Properties

open FStar.List.Tot

open Hoop.Runtime

// `Hoop.Runtime.find_prompt` is implemented tail-recursively, which 
// is stack-safe and more performant, but hard to use to prove theorems.
// Here, find_prompt' is non-tail recursive variant and intend to be used 
// inside the theorem proofs.
let rec find_prompt'
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : GTot (option (stack v cl & cl & stack v cl)) 
  = match k with
    | [] -> None
    | PromptF hs ret :: rest ->
      (match lookup_clause hs eff op with
        | Some c -> Some ([PromptF hs ret], c, rest)
        | None ->
          (match find_prompt' eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PromptF hs ret :: cap, c, below)))
    | f :: rest ->
      (match find_prompt' eff op rest with
        | None -> None
        | Some (cap, c, below) -> Some (f :: cap, c, below))

// The use of find_prompt' in the proofs is justified by the following two lemmas:
let rec find_prompt_aux_correct (#v #cl: Type) (eff op: string) (soFar k: stack v cl)
    : Lemma
      (ensures
        (find_prompt_aux eff op soFar k ==
          (match find_prompt' eff op k with
            | None -> None
            | Some (cap, c, below) -> Some (rev_acc soFar cap, c, below)))) (decreases k) =
  match k with
  | [] -> ()
  | hd :: tl ->
    (match hd with
      | PromptF hs _ ->
        (match lookup_clause hs eff op with
          | Some _ -> ()
          | None -> find_prompt_aux_correct eff op (hd :: soFar) tl)
      | BindF _ -> find_prompt_aux_correct eff op (hd :: soFar) tl)

let find_prompt_correct
    (#v #cl: Type)
    (eff op: string) 
    (k: stack v cl)
  : Lemma 
      (ensures find_prompt eff op k == find_prompt' eff op k)
  = find_prompt_aux_correct eff op [] k

let rec find_prompt_partitions_spec
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma 
      (requires Some? (find_prompt' eff op k))
      (ensures find_prompt_partitions_correctness (find_prompt' #v #cl) eff op k)
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      (match lookup_clause hs eff op with
        | Some _ -> ()
        | None -> find_prompt_partitions_spec eff op rest)
    | _ :: rest -> find_prompt_partitions_spec eff op rest

// Corollary: The property of `find_prompt_partitions` also holds for the extract version of `find_prompt`.
let find_prompt_partitions
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma 
      (requires Some? (find_prompt eff op k))
      (ensures find_prompt_partitions_correctness (find_prompt #v #cl) eff op k)
  = find_prompt_correct eff op k; 
    find_prompt_partitions_spec eff op k

let rec find_prompt_last_spec 
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt' eff op k))
      (ensures (find_prompt_last_correctness (find_prompt' #v #cl) eff op k))
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      (match lookup_clause hs eff op with
        | Some _ -> ()
        | None -> find_prompt_last_spec eff op rest)
    | _ :: rest -> find_prompt_last_spec eff op rest

// Corollary: The property of `find_prompt_last` also holds for the extract version of `find_prompt`.
let find_prompt_last
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_last_correctness (find_prompt #v #cl) eff op k))
  = find_prompt_correct eff op k;
    find_prompt_last_spec eff op k

let rec find_prompt_innermost_spec 
    (#v #cl: Type) 
    (eff op: string) 
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt' eff op k))
      (ensures (find_prompt_innermost_correctness (find_prompt' #v #cl) eff op k))
      (decreases k) 
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      (match lookup_clause hs eff op with
        | Some _ -> ()
        | None ->
          (find_prompt_last_spec eff op rest;
            find_prompt_innermost_spec eff op rest))
    | _ :: rest ->
      (find_prompt_last_spec eff op rest;
        find_prompt_innermost_spec eff op rest)

// Corollary
let find_prompt_innermost
    (#v #cl: Type) 
    (eff op: string) 
    (k: stack v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures (find_prompt_innermost_correctness (find_prompt #v #cl) eff op k))
      (decreases k) 
  = find_prompt_correct eff op k;
    find_prompt_innermost_spec eff op k

let rec find_prompt_none_spec
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures find_prompt_none_correctness (find_prompt' #v #cl) eff op k)
      (decreases k)
  = match k with
    | [] -> ()
    | PromptF hs _ :: rest ->
      (match lookup_clause hs eff op with
        | Some _ -> ()
        | None -> find_prompt_none_spec eff op rest)
    | _ :: rest -> find_prompt_none_spec eff op rest

// Corollary
let find_prompt_none
    (#v #cl: Type)
    (eff op: string)
    (k: stack v cl)
  : Lemma
      (ensures find_prompt_none_correctness (find_prompt #v #cl) eff op k)
  = find_prompt_correct eff op k; find_prompt_none_spec eff op k

(* ------------------------------------------------------------------ *)

let rec lookup_clause_memP
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma
      (requires Some? (lookup_clause hs eff op))
      (ensures (lookup_clause_soundness hs eff op)) 
      (decreases hs)
  = match hs with
    | [] -> ()
    | (e, o, _) :: rest -> if e = eff && o = op then () else lookup_clause_memP rest eff op

let rec lookup_clause_none 
    (#cl: Type)
    (hs: handlers cl)
    (eff op: string)
  : Lemma 
      (requires None? (lookup_clause hs eff op))
      (ensures lookup_clause_completeness hs eff op)
      (decreases hs)
  = match hs with
    | [] -> ()
    | (e, o, _) :: rest -> lookup_clause_none rest eff op

let step_perform
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (requires Some? (find_prompt eff op k))
      (ensures 
          (let Some (captured, clause, below) = find_prompt eff op k in
              (step apply (Step (Perform eff op payload) k) == 
                  Step (apply clause payload (fun x -> Resumed captured x)) below) /\
              captured @ below == k))
  = find_prompt_partitions eff op k

let step_perform_stuck
    (#v #cl: Type)
    (eff op: string)
    (payload: list v)
    (k: stack v cl)
    (apply: apply_t v cl)
  : Lemma
      (~(handled_in eff op k) <==>
          step apply (Step (Perform eff op payload) k) == Stuck eff op)
  = find_prompt_none eff op k

let step_resumed
    (#v #cl : Type)
    (apply: apply_t v cl)
    (comp : comp_tree v cl { Resumed? comp })
    (cc : stack v cl)
  : Lemma 
      (step apply (Step comp cc) == 
        Step (Var (Resumed?.value comp)) ((Resumed?.frames comp) @ cc))
  = ()

let capture_resume_roundtrip
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
  = find_prompt_partitions eff op k

let step_op
    (#v #cl: Type)
    (apply: apply_t v cl)
    (c: comp_tree v cl)
    (fn: v -> comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Op c fn) k) == Step c (BindF fn :: k))
  = ()

let step_handle
    (#v #cl: Type)
    (apply: apply_t v cl)
    (hs: handlers cl)
    (ret: option (v -> comp_tree v cl))
    (body: comp_tree v cl)
    (k: stack v cl)
  : Lemma (step apply (Step (Handle hs ret body) k) == Step body (PromptF hs ret :: k))
  = ()

let step_var_done
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
  : Lemma (step apply (Step (Var value) []) == Done value)
  = ()

let step_var_bind
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (fn: v -> comp_tree v cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (BindF fn :: rest)) == Step (fn value) rest)
  = ()

let step_var_prompt
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
  = ()

let step_var_prompt_identity
    (#v #cl: Type)
    (apply: apply_t v cl)
    (value: v)
    (hs: handlers cl)
    (rest: stack v cl)
  : Lemma (step apply (Step (Var value) (PromptF hs None :: rest)) == Step (Var value) rest)
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

let handled_in_cons
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
    (k: stack v cl)
  : Lemma
      (requires handled_in eff op k)
      (ensures handled_in eff op (f :: k))
  = ()

(* ------------------------------------------------------------------ *)

// Zero fuel is a no-op.
let steps_zero 
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma (steps apply 0 s == s)
  = ()

let rec steps_terminal
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s)
      (ensures steps apply n s == s)
      (decreases n)
  = if n = 0 then () 
    else steps_terminal apply (n - 1) s

let rec steps_add
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat) (s: state v cl)
  : Lemma
      (ensures steps apply (n + m) s == steps apply m (steps apply n s))
      (decreases n)
  = if n = 0 then ()
    else
      match s with
      | Done _ ->
          steps_terminal apply (n + m) s;
          steps_terminal apply n s;
          steps_terminal apply m s
      | Stuck _ _ ->
          steps_terminal apply (n + m) s;
          steps_terminal apply n s;
          steps_terminal apply m s
      | Step _ _ ->
          steps_add apply (n - 1) m (step apply s)

let steps_unfold
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n: nat)
    (s: state v cl)
  : Lemma
      (requires Step? s)
      (ensures steps apply (n + 1) s == steps apply n (step apply s))
  = ()

let steps_stable
    (#v #cl: Type)
    (apply: apply_t v cl)
    (n m: nat)
    (s: state v cl)
  : Lemma
      (requires Done? (steps apply n s))
      (ensures steps apply (n + m) s == steps apply n s)
  = steps_add apply n m s;
    steps_terminal apply m (steps apply n s)
(* ------------------------------------------------------------------ *)
(* Well-scopedness: the defining equations                             *)
(*                                                                     *)
(* Each equation is proved in two halves, and the half that has to peel *)
(* the step index lives in `Hoop.Runtime` -- `ws_n` and `wf_stack_n`    *)
(* are private there, so `..._fwd` / `..._bwd` are as close as this     *)
(* module ever gets to the index. What is left here is the assembly of  *)
(* the two halves into an `<==>`, plus the backward directions that go  *)
(* through on their own.                                                *)
(* ------------------------------------------------------------------ *)

let ws_var (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (x: v)
  : Lemma (ws cok a (Var x <: comp_tree v cl))
  = ()

let ws_perform (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
               (eff op: string) (payload: list v)
  : Lemma (ws cok a (Perform eff op payload <: comp_tree v cl) <==> a eff op == true)
  = ws_perform_eq #v #cl cok a eff op payload

let ws_op (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
          (c: comp_tree v cl) (fn: v -> comp_tree v cl)
  : Lemma (ws cok a (Op c fn) <==> (ws cok a c /\ (forall (x: v). ws cok a (fn x))))
  = (introduce ws cok a (Op c fn) ==> (ws cok a c /\ (forall (x: v). ws cok a (fn x)))
     with _. ws_op_fwd cok a c fn);
    (introduce (ws cok a c /\ (forall (x: v). ws cok a (fn x))) ==> ws cok a (Op c fn)
     with _. ())

let ws_handle (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (hs: handlers cl)
              (ret: option (v -> comp_tree v cl)) (body: comp_tree v cl)
  : Lemma (ws cok a (Handle hs ret body) <==>
            (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret))
  = (introduce ws cok a (Handle hs ret body) ==>
               (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret)
     with _. ws_handle_fwd cok a hs ret body);
    (introduce (ws cok (extend hs a) body /\ handler_ok cok a hs /\ ret_ws cok a ret) ==>
               ws cok a (Handle hs ret body)
     with _. ws_handle_bwd cok a hs ret body)

let ws_resumed (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (frames: stack v cl) (x: v)
  : Lemma (ws cok a (Resumed frames x) <==> wf_stack cok a frames)
  = (introduce ws cok a (Resumed frames x) ==> wf_stack cok a frames
     with _. ws_resumed_fwd cok a frames x);
    (introduce wf_stack cok a frames ==> ws cok a (Resumed frames x) with _. ())

let wf_stack_nil (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
  : Lemma (wf_stack cok a ([] <: stack v cl))
  = ()

let wf_stack_bind (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
             (fn: v -> comp_tree v cl) (rest: stack v cl)
  : Lemma (wf_stack cok a (BindF fn :: rest) <==>
            ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest))
  = (introduce wf_stack cok a (BindF fn :: rest) ==>
               ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest)
     with _. wf_stack_bind_fwd cok a fn rest);
    (introduce ((forall (x: v). ws cok (can_in_with rest a) (fn x)) /\ wf_stack cok a rest) ==>
               wf_stack cok a (BindF fn :: rest)
     with _. ())

let wf_stack_prompt (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform) (hs: handlers cl)
               (ret: option (v -> comp_tree v cl)) (rest: stack v cl)
  : Lemma (wf_stack cok a (PromptF hs ret :: rest) <==>
            (handler_ok cok (can_in_with rest a) hs /\
             ret_ws cok (can_in_with rest a) ret /\
             wf_stack cok a rest))
  = (introduce wf_stack cok a (PromptF hs ret :: rest) ==>
               (handler_ok cok (can_in_with rest a) hs /\
                ret_ws cok (can_in_with rest a) ret /\ wf_stack cok a rest)
     with _. wf_stack_prompt_fwd cok a hs ret rest);
    (introduce (handler_ok cok (can_in_with rest a) hs /\
                ret_ws cok (can_in_with rest a) ret /\ wf_stack cok a rest) ==>
               wf_stack cok a (PromptF hs ret :: rest)
     with _. wf_stack_prompt_bwd cok a hs ret rest)

(* ------------------------------------------------------------------ *)
(* Congruence in the environment                                       *)
(* ------------------------------------------------------------------ *)

let clauses_ok_cong (#cl: Type) (cok: clause_ok_t cl) (a1 a2: can_perform) (hs: handlers cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can a1 a2)
          (ensures handler_ok cok a1 hs <==> handler_ok cok a2 hs)
  = introduce forall (c: cl). (cok a1 c <==> cok a2 c)
    with assert (clause_ok_congr cok)

let ws_cong (#v #cl: Type) (cok: clause_ok_t cl) (a1 a2: can_perform) (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can a1 a2)
          (ensures ws cok a1 c <==> ws cok a2 c)
  = ws_cong_eq cok a1 a2 c

let wf_stack_cong (#v #cl: Type) (cok: clause_ok_t cl) (a1 a2: can_perform) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ equiv_can a1 a2)
          (ensures wf_stack cok a1 k <==> wf_stack cok a2 k)
  = wf_stack_cong_eq cok a1 a2 k

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
      (can_in_with (k1 @ k2) a) e o == (can_in_with k1 (can_in_with k2 a)) e o
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
        | BindF fn ->
          wf_stack_bind cok a fn (r1 @ k2);
          wf_stack_bind cok (can_in_with k2 a) fn r1;
          introduce forall (x: v).
            (ws cok (can_in_with (r1 @ k2) a) (fn x) <==> ws cok (can_in_with r1 (can_in_with k2 a)) (fn x))
          with ws_cong cok (can_in_with (r1 @ k2) a) (can_in_with r1 (can_in_with k2 a)) (fn x)
        | PromptF hs ret ->
          wf_stack_prompt cok a hs ret (r1 @ k2);
          wf_stack_prompt cok (can_in_with k2 a) hs ret r1;
          (match ret with
            | None -> ()
            | Some r ->
              introduce forall (x: v).
                (ws cok (can_in_with (r1 @ k2) a) (r x) <==>
                 ws cok (can_in_with r1 (can_in_with k2 a)) (r x))
              with ws_cong cok (can_in_with (r1 @ k2) a) (can_in_with r1 (can_in_with k2 a)) (r x)))

let wf_stack_split_prompt (#v #cl: Type) (cok: clause_ok_t cl) (a: can_perform)
                     (k1: stack v cl) (hs: handlers cl)
                     (ret: option (v -> comp_tree v cl)) (k2: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_stack cok a (k1 @ (PromptF hs ret :: k2)))
          (ensures handler_ok cok (can_in_with k2 a) hs)
  = wf_stack_append cok k1 (PromptF hs ret :: k2) a;
    wf_stack_prompt cok a hs ret k2

(* ------------------------------------------------------------------ *)
(* Preservation of the machine invariant, one transition at a time     *)
(* ------------------------------------------------------------------ *)

let pres_op (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
            (inner: comp_tree v cl) (fn: v -> comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Op inner fn) k))
          (ensures wf_state cok (step apply (Step (Op inner fn) k)))
  = ws_op cok (can_in k) inner fn;
    av_bind fn k (can_nothing ());
    ws_cong cok (can_in k) (can_in (BindF fn :: k)) inner;
    wf_stack_bind cok (can_nothing ()) fn k

let pres_handle (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
                (hs: handlers cl) (ret: option (v -> comp_tree v cl))
                (body: comp_tree v cl) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Handle hs ret body) k))
          (ensures wf_state cok (step apply (Step (Handle hs ret body) k)))
  = ws_handle cok (can_in k) hs ret body;
    av_prompt hs ret k (can_nothing ());
    ws_cong cok (extend hs (can_in k)) (can_in (PromptF hs ret :: k)) body;
    wf_stack_prompt cok (can_nothing ()) hs ret k

let pres_var (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
             (value: v) (k: stack v cl)
  : Lemma (requires wf_state cok (Step (Var value <: comp_tree v cl) k))
          (ensures wf_state cok (step apply (Step (Var value <: comp_tree v cl) k)))
  = match k with
    | [] -> ()
    | BindF fn :: rest -> wf_stack_bind cok (can_nothing ()) fn rest
    | PromptF hs ret :: rest -> wf_stack_prompt cok (can_nothing ()) hs ret rest

let pres_resumed (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
                 (captured: stack v cl) (value: v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ wf_state cok (Step (Resumed captured value) k))
          (ensures wf_state cok (step apply (Step (Resumed captured value) k)))
  = ws_resumed cok (can_in k) captured value;
    wf_stack_append cok captured k (can_nothing ())

#push-options "--split_queries always"
let pres_perform (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
                 (eff op: string) (payload: list v) (k: stack v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\
                    wf_state cok (Step (Perform eff op payload) k))
          (ensures wf_state cok (step apply (Step (Perform eff op payload) k)))
  = ws_perform #v #cl cok (can_in k) eff op payload;
    assert (Some? (find_prompt eff op k));
    let Some (captured, clause, below) = find_prompt eff op k in
    step_perform eff op payload k apply;
    find_prompt_partitions eff op k;
    find_prompt_last eff op k;
    assert (captured @ below == k);
    assert (Cons? captured);
    (* the prompt that owns `clause` is the last frame of `captured` *)
    append_init_last captured;
    append_assoc (init captured) [last captured] below;
    assert (k == init captured @ (last captured :: below));
    assert (PromptF? (last captured));
    let PromptF phs pret = last captured in
    assert (lookup_clause phs eff op == Some clause);
    wf_stack_split_prompt cok (can_nothing ()) (init captured) phs pret below;
    assert (handler_ok cok (can_in below) phs);
    assert (cok (can_in below) clause);
    (* the captured segment is well formed on top of `below` *)
    wf_stack_append cok captured below (can_nothing ());
    assert (wf_stack cok (can_in below) captured);
    let kf : v -> comp_tree v cl = fun x -> Resumed captured x in
    introduce forall (x: v). ws cok (can_in below) (kf x)
    with ws_resumed cok (can_in below) captured x;
    assert (ws cok (can_in below) (apply clause payload kf))
#pop-options

let step_preserves_wf (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
          (ensures wf_state cok (step apply s))
  = match s with
    | Done _ -> ()
    | Stuck _ _ -> ()
    | Step c k ->
      (match c with
        | Op inner fn -> pres_op cok apply inner fn k
        | Var value -> pres_var cok apply value k
        | Handle hs ret body -> pres_handle cok apply hs ret body k
        | Resumed captured value -> pres_resumed cok apply captured value k
        | Perform eff op payload -> pres_perform cok apply eff op payload k)

let step_progress (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
          (ensures ~(Stuck? (step apply s)))
  = step_preserves_wf cok apply s

(* ------------------------------------------------------------------ *)
(* Progress                                                            *)
(* ------------------------------------------------------------------ *)

let rec steps_preserves_wf (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
                           (n: nat) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
          (ensures wf_state cok (steps apply n s))
          (decreases n)
  = if n = 0 then ()
    else
      match s with
      | Done _ -> ()
      | Stuck _ _ -> ()
      | Step _ _ ->
        step_preserves_wf cok apply s;
        steps_preserves_wf cok apply (n - 1) (step apply s)

let progress (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (n: nat) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
          (ensures ~(Stuck? (steps apply n s)))
  = steps_preserves_wf cok apply n s

let load_wf (#v #cl: Type) (cok: clause_ok_t cl) (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ ws cok (can_nothing ()) c)
          (ensures wf_state cok (load c))
  = wf_stack_nil #v #cl cok (can_nothing ());
    ws_cong cok (can_nothing ()) (can_in ([] <: stack v cl)) c

let wf_never_stuck (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl) (s: state v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ wf_state cok s)
          (ensures never_stuck apply s)
  = introduce forall (n: nat). ~(Stuck? (steps apply n s))
    with progress cok apply n s

let load_never_stuck (#v #cl: Type) (cok: clause_ok_t cl) (apply: apply_t v cl)
                     (c: comp_tree v cl)
  : Lemma (requires clause_ok_congr cok /\ apply_ok apply cok /\ ws cok (can_nothing ()) c)
          (ensures never_stuck apply (load c))
  = load_wf cok c;
    wf_never_stuck cok apply (load c)
