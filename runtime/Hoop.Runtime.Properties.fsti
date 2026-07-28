module Hoop.Runtime.Properties

open Hoop.Runtime
open FStar.List.Tot

// Is this frame responsible for the action identified as `(eff, op)`?
let handles
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
  : bool
  = match f with
    | PromptF hs _ -> Some? (lookup_clause hs eff op)
    | BindF _ -> false

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
 * the prompt frame that holds the returning clause.
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
 * In other words, `lookup_clause` never forge the handler clause.
 * 
 * Together with `find_prompt_last`, ensures that:
 * the returned clause is indeed a member of handlers installed by the prompt at the bottom of
 * the caputured continuation.
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

