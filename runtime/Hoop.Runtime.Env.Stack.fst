(**
 * The correspondence between the evidence environment and the stack, proved.
 *
 * Everything rests on one induction, `walk`: `Hoop.Runtime.Env.find_level` on
 * the levels a stack offers and `Hoop.Runtime.Semantics.find_prompt` on the stack
 * itself descend in lockstep, stopping at the same frame. That lemma carries
 * the clause, the height, the outer environment and the *position* of the
 * prompt, and the interface's correspondence theorems are read off it --
 * `find_prompt_partitions` and `find_prompt_last` supplying the facts about the
 * captured segment that `walk` itself says nothing about.
 *
 * No property of `find_prompt` is re-proved here; the two walks are related and
 * the existing theorems transported.
 *)
module Hoop.Runtime.Env.Stack

open FStar.List.Tot
open Hoop.Runtime.Syntax
open Hoop.Runtime.Semantics
open Hoop.Runtime.WellScopedness

module E = Hoop.Runtime.Env
module MT = Hoop.Runtime.Metatheory
module LP = FStar.List.Pure.Properties

(* ------------------------------------------------------------------ *)
(*  The two walks                                                      *)
(* ------------------------------------------------------------------ *)

(* What `walk` establishes at every depth of the two descents. Nothing is
   claimed about the captured segment -- only what the environment records,
   plus the position of the prompt as a decomposition of the stack. The segment
   is recovered from `find_prompt_partitions`. *)
private
let walk_correctness (#v #cl: Type) (eff op: string) (k: stack v cl) : GTot prop =
  match E.find_level (E.levels (env_of_stack k)) (eff, op) with
  | None -> None? (find_prompt eff op k)
  | Some (p, outer) ->
      (match find_prompt eff op k with
        | None -> False
        | Some (_, c, below) ->
            p.h == length below /\
            outer == E.levels (env_of_stack below) /\
            lookup_clause (PromptF?.hs p.pf) eff op == Some c /\
            (exists (above: stack v cl). k == above @ ((p.pf <: frame v cl) :: below)))

(* Pushing a frame keeps a decomposition a decomposition. The only step of
   `walk` the solver does not take by itself, the witness having to be named. *)
private
let cons_witness (#v #cl: Type) (f: frame v cl) (p: frame v cl) (rest below: stack v cl)
  : Lemma
      (requires exists (above: stack v cl). rest == above @ (p :: below))
      (ensures exists (above: stack v cl). (f :: rest) == above @ (p :: below))
  = eliminate exists (above: stack v cl). rest == above @ (p :: below)
    with
      introduce exists (above2: stack v cl). (f :: rest) == above2 @ (p :: below)
      with (f :: above) and ()

private
let rec walk (#v #cl: Type) (eff op: string) (k: stack v cl)
  : Lemma (ensures walk_correctness eff op k) (decreases k)
  = match k with
    | [] -> ()
    (* The head frame does not stop the search, so the recursive answer carries
       over: same clause, same stack below, one more frame in the
       decomposition. *)
    | BindF fn :: rest ->
        walk eff op rest;
        (match E.find_level (E.levels (env_of_stack rest)) (eff, op), find_prompt eff op rest with
          | Some (p, _), Some (_, _, below) -> cons_witness (BindF fn) p.pf rest below
          | _ -> ())
    | PromptF hs ret :: rest ->
        keys_correct hs eff op;
        (match lookup_clause hs eff op with
          | Some _ ->
              introduce exists (above: stack v cl).
                        k == above @ ((PromptF hs ret <: frame v cl) :: rest)
              with [] and ()
          | None ->
              walk eff op rest;
              (match E.find_level (E.levels (env_of_stack rest)) (eff, op), find_prompt eff op rest with
                | Some (p, _), Some (_, _, below) -> cons_witness (PromptF hs ret) p.pf rest below
                | _ -> ()))

(* ------------------------------------------------------------------ *)
(*  The correspondence                                                 *)
(* ------------------------------------------------------------------ *)

let lookup_iff_handled #v #cl eff op k = walk eff op k

let lookup_finds_prompt #v #cl eff op k =
  walk eff op k;
  MT.find_prompt_partitions eff op k;
  MT.find_prompt_last eff op k;
  match find_prompt eff op k with
  | None -> ()
  | Some (cap, _, below) ->
      (match E.lookup (env_of_stack k) (eff, op) with
        | None -> ()
        | Some ev ->
            let pf : frame v cl = ev.E.prompt.pf in
            eliminate exists (above: stack v cl). k == above @ (pf :: below)
            with
              begin
                append_assoc above [pf] below;
                append_inv_tail below cap (above @ [pf]);
                lemma_append_last above [pf]
              end)

let lookup_height #v #cl eff op k = walk eff op k

let lookup_below #v #cl eff op k = walk eff op k

let split_at_height_agrees #v #cl eff op k n =
  lookup_height eff op k;
  lookup_finds_prompt eff op k;
  MT.find_prompt_partitions eff op k;
  match find_prompt eff op k with
  | None -> ()
  | Some (cap, _, below) ->
      (match E.lookup (env_of_stack k) (eff, op) with
        | None -> ()
        | Some _ ->
            append_length cap below;
            LP.lemma_append_splitAt cap below)

let perform_split_agrees #v #cl eff op k n =
  lookup_iff_handled eff op k;
  lookup_finds_prompt eff op k;
  split_at_height_agrees eff op k n

let step_perform_via_env_agrees #v #cl apply eff op payload k n =
  perform_split_agrees eff op k n

(* ------------------------------------------------------------------ *)
(*  Invariants                                                         *)
(* ------------------------------------------------------------------ *)

let rec env_of_stack_well_keyed #v #cl k =
  match k with
  | [] -> ()
  | BindF _ :: rest -> env_of_stack_well_keyed rest
  | PromptF hs ret :: rest -> env_of_stack_well_keyed rest

let rec env_prompts_of_stack #v #cl k =
  match k with
  | [] -> ()
  | BindF _ :: rest -> env_prompts_of_stack rest
  | PromptF _ _ :: rest -> env_prompts_of_stack rest

(* `sublist_of` is reflexive: the exact-agreement invariant implies the weak
   one. *)
private
let rec sublist_of_refl (#a: Type) (l: list a) : Lemma (ensures sublist_of l l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> sublist_of_refl tl

(* Pushing a frame keeps a payload where it was: one more frame above it, the
   same number below. *)
private
let located_in_cons (#v #cl: Type) (f: frame v cl) (p: pframe v cl) (rest: stack v cl)
  : Lemma (requires located_in p rest) (ensures located_in p (f :: rest))
  = eliminate exists (above below: stack v cl).
                rest == above @ ((p.pf <: frame v cl) :: below) /\ length below == p.h
    with
      introduce exists (above2 below2: stack v cl).
                (f :: rest) == above2 @ ((p.pf <: frame v cl) :: below2) /\ length below2 == p.h
      with (f :: above) below
      and ()

private
let rec env_of_stack_located (#v #cl: Type) (k: stack v cl)
  : Lemma (ensures env_located (env_of_stack k) k) (decreases k)
  = match k with
    | [] -> ()
    | f :: rest ->
        env_of_stack_located rest;
        introduce forall (l: E.level (pframe v cl)).
                    l `memP` E.levels (env_of_stack rest) ==> located_in l.E.payload k
        with introduce _ ==> _
        with located_in_cons f l.E.payload rest;
        (match f with
          | BindF _ -> ()
          | PromptF hs ret ->
              let p : pframe v cl = { pf = (PromptF hs ret <: prompt v cl); h = length rest } in
              introduce exists (above below: stack v cl).
                        k == above @ ((p.pf <: frame v cl) :: below) /\ length below == p.h
              with [] rest
              and ())

let env_matches_implies_ok #v #cl w k =
  env_of_stack_well_keyed k;
  env_of_stack_located k;
  env_prompts_of_stack k;
  sublist_of_refl (prompts_of k)

(* The level a successful `find_level` stopped at is a level of the list, binds
   the key, and has the returned payload. All the two evidence lemmas need. *)
private
let rec find_level_sound (#a: Type) (ls: list (E.level a)) (ky: key)
  : Lemma
      (ensures
        (match E.find_level ls ky with
          | None -> True
          | Some (x, _) ->
              exists (l: E.level a). l `memP` ls /\ l.E.payload == x /\ ky `mem` l.E.keys))
      (decreases ls)
  = match ls with
    | [] -> ()
    | l :: outer ->
        if ky `mem` l.E.keys
        then
          introduce exists (l2: E.level a).
                    l2 `memP` ls /\ l2.E.payload == l.E.payload /\ ky `mem` l2.E.keys
          with l and ()
        else begin
          find_level_sound outer ky;
          match E.find_level outer ky with
          | None -> ()
          | Some (x, _) ->
              eliminate exists (l2: E.level a).
                        l2 `memP` outer /\ l2.E.payload == x /\ ky `mem` l2.E.keys
              with
                introduce exists (l3: E.level a).
                          l3 `memP` ls /\ l3.E.payload == x /\ ky `mem` l3.E.keys
                with l2 and ()
        end

(* A frame that occurs in a decomposition of the stack occurs in the stack. *)
private
let located_in_memP (#v #cl: Type) (p: pframe v cl) (k: stack v cl)
  : Lemma (requires located_in p k) (ensures (p.pf <: frame v cl) `memP` k)
  = eliminate exists (above below: stack v cl).
                k == above @ ((p.pf <: frame v cl) :: below) /\ length below == p.h
    with append_memP above ((p.pf <: frame v cl) :: below) p.pf

let evidence_live #v #cl w k eff op =
  find_level_sound (E.levels w) (eff, op);
  let ev = Some?.v (E.lookup w (eff, op)) in
  eliminate exists (l: E.level (pframe v cl)).
              l `memP` E.levels w /\ l.E.payload == ev.E.prompt /\ (eff, op) `mem` l.E.keys
  with located_in_memP ev.E.prompt k

let evidence_has_clause #v #cl w eff op =
  find_level_sound (E.levels w) (eff, op)

let split_at_height_located #v #cl p k n =
  eliminate exists (above below: stack v cl).
              k == above @ ((p.pf <: frame v cl) :: below) /\ length below == p.h
  with
    begin
      let pf : frame v cl = p.pf in
      append_assoc above [pf] below;
      append_length above [pf];
      append_length (above @ [pf]) below;
      LP.lemma_append_splitAt (above @ [pf]) below;
      lemma_append_last above [pf]
    end

(* ------------------------------------------------------------------ *)
(*  Preservation                                                       *)
(* ------------------------------------------------------------------ *)

let perform_preserves_env_matches #v #cl eff op k n =
  lookup_iff_handled eff op k;
  lookup_height eff op k;
  lookup_below eff op k;
  perform_split_agrees eff op k n

let env_matches_bind #v #cl w k fn = ()

let env_matches_handle #v #cl w k hs ret = ()

let env_matches_pop #v #cl w k hs ret = ()

let rec env_of_stack_append #v #cl k1 k2 =
  match k1 with
  | [] -> ()
  | BindF _ :: rest -> env_of_stack_append rest k2
  | PromptF _ _ :: rest ->
      env_of_stack_append rest k2;
      append_length rest k2

let rec reinstall_equiv #v #cl base w1 w2 k n =
  match k with
  | [] -> ()
  | BindF _ :: rest -> reinstall_equiv base w1 w2 rest (n - 1)
  | PromptF _ _ :: rest -> reinstall_equiv base w1 w2 rest (n - 1)

(* A loop over a concatenation is the two loops in sequence, the counter picked
   up where the first left it. Needed because `rev` is consumed through `rev'`,
   whose recursive equation appends. *)
private
let rec reinstall_loop_append
    (#v #cl: Type)
    (base: nat)
    (w: E.env (pframe v cl))
    (j: nat)
    (l1 l2: stack v cl)
  : Lemma
      (ensures
        reinstall_loop base w j (l1 @ l2)
          == reinstall_loop base (reinstall_loop base w j l1) (j + length l1) l2)
      (decreases l1)
  = match l1 with
    | [] -> ()
    | BindF _ :: rest -> reinstall_loop_append base w (j + 1) rest l2
    | PromptF hs ret :: rest ->
        reinstall_loop_append base
          (E.extend w (keys hs) ({ pf = (PromptF hs ret <: prompt v cl); h = base + j }))
          (j + 1) rest l2

(* `rev (f :: rest)` is `rev rest @ [f]`, so the append lemma splits the loop
   into the induction hypothesis followed by a single frame -- stamped with
   `length rest` either way: on the loop's side because that is how far the
   counter has come, on the specification's because that is what lies below. *)
let rec reinstall_loop_rev #v #cl base w k =
  match k with
  | [] -> ()
  | f :: rest ->
      reinstall_loop_rev base w rest;
      rev_rev' k;
      rev_rev' rest;
      rev_length rest;
      reinstall_loop_append base w 0 (rev rest) [f]

(* ------------------------------------------------------------------ *)
(*  Bridge to well-scopedness                                          *)
(* ------------------------------------------------------------------ *)

let can_env_agrees #v #cl k =
  introduce forall (eff op: string). (can_env (env_of_stack k) eff op <==> can_in k eff op)
  with lookup_iff_handled eff op k
