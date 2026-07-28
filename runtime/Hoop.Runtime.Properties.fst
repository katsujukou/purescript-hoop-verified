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