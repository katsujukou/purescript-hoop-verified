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