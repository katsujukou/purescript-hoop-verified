(**
 * The operational semantics of the Hoop runtime machine. This is a CEK-like 
 * stack machine where 'C' represents a computation tree and 'K' represents 
 * an explicit stack of defunctionalized continuation frames. The machine 
 * executes a program by repeatedly transitioning between states of the form 
 * `Step c k`.
 * 
 * This module serves as a reference implementation of the specification, where 
 * handler dispatch is performed via a linear search of the stack. Although this 
 * is the most straightforward implementation of deep-handler semantics, walking 
 * the K-stack on every operation execution is inefficient. Therefore, the actual 
 * runtime engine called from PureScript (`Hoop.Runtime`) employs a more performant 
 * evidence-passing mechanism, where the E-part serves as an evidence environment. 
 * The equivalence of these two machines is proved under appropriate assumptions.
 *)
module Hoop.Runtime.Semantics

open FStar.List.Tot
open Hoop.Runtime.Syntax

type stack (v: Type) (cl: Type) = list (frame v cl)

(** The machine state *)
noeq
type state (v: Type) (cl: Type) =
  | Done : (value:v) -> state v cl
  | Step : (c:comp_tree v cl) -> (k:stack v cl) -> state v cl
  // Unhandled effect operation exception which should never occur
  // as long as the runtime is sound
  | Stuck : eff: string -> op: string -> state v cl

// ------------------------------------------------------------------ //

// Is this frame responsible for the action `(eff, op)`?
let handles
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
  : GTot (b:bool { b <==> (PromptF? f /\ Some? (lookup_clause (PromptF?.hs f) eff op) )})
  = match f with
    | PromptF hs _ -> Some? (lookup_clause hs eff op)
    | BindF _ -> false

// Can this action be handled within this stack?
let handled_in
    (#v #cl : Type)
    (eff op : string)
    (k: stack v cl)
  : GTot prop
  = exists (f: frame v cl). (f `memP` k /\ handles eff op f)

// Finds the prompt holding the handler for the given action and splits the
// stack there, returning `(captured, clause, below)`. The captured segment is
// every frame above the matching prompt, prompt included, so resuming
// reinstalls the handler — deep-handler semantics.
let rec find_prompt
    (#v #cl : Type)
    (eff op : string)
    (k : stack v cl)
  : GTot
      (o: option (stack v cl & cl & stack v cl) { handled_in eff op k <==> Some? o })
      (decreases k)
  = match k with
    | [] -> None
    | PromptF hs ret :: rest ->
      (match lookup_clause hs eff op with
        | Some c -> Some ([PromptF hs ret], c, rest)
        | None ->
          (match find_prompt eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PromptF hs ret :: cap, c, below)))
    | f :: rest ->
      (match find_prompt eff op rest with
        | None -> None
        | Some (cap, c, below) -> Some (f :: cap, c, below))


// The delimited continuation handed to a clause.
// While `kont_of captured` is definitionally `fun x -> Resumed captured x`, 
// it is worth defining it as a top-level named function due to the limitation 
// described in the book:
// https://fstar-lang.org/tutorial/book/part1/part1_quicksort.html#limitations-of-smt-based-proofs-at-higher-order
let kont_of (#v #cl: Type)
    (captured: stack v cl)
    (x: v)
  : comp_tree v cl
  = Resumed captured x

// The small-step semantics of the machine.
let step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : GTot (state v cl)
  = match s with
    | Done _ -> s
    | Stuck _ _ -> s
    | Step c k ->
      match c with
      | Op comp fn -> Step comp (BindF fn :: k)
      | Handle hs pure body -> Step body (PromptF hs pure :: k)
      | Perform eff op payload ->
        (match find_prompt eff op k with
          | None -> Stuck eff op
          | Some (captured, clause, below) ->
            Step (apply clause payload (kont_of captured)) below)
      | Var value ->
        (match k with
          | [] -> Done value
          | (BindF fn)::rest -> Step (fn value) rest
          | (PromptF _ pure)::rest ->
            (match pure with
              | Some fn -> Step (fn value) rest
              | None -> Step (Var value) rest
            )
        )
      | Resumed kont value -> Step (Var value) (kont @ k)


// The multi-step relation: the iteration of `step`, cut off at `fuel` transitions.
let rec steps
    (#v #cl: Type)
    (apply: apply_t v cl)
    (fuel: nat)
    (s: state v cl)
  : GTot (state v cl)
  = if fuel = 0 then s
    else
      match s with
      | Done _ -> s
      | Stuck _ _ -> s
      | Step _ _ -> steps apply (fuel - 1) (step apply s)

let one_more_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { Step? s })
    (r: state v cl)
  : Lemma
      (requires exists (n:nat). r == steps apply n (step apply s))
      (ensures (exists (m:nat). r == steps apply m s))
  = eliminate exists (n:nat). r == steps apply n (step apply s)
    with
      introduce exists (m:nat). r == steps apply m s
      with (n + 1) and ()

let no_more_steps
    (#v #cl : Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s)
      (ensures exists (n:nat). s == steps apply n s)
  = introduce exists (n:nat). s == steps apply n s
    with 0
    and ()

let never_stuck
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : GTot prop
  = forall (n: nat). ~(Stuck? (steps apply n s))

let never_stuck_now
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires never_stuck apply s)
      (ensures ~(Stuck? s))
  = assert (steps apply 0 s == s)

let never_stuck_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { Step? s })
  : Lemma
      (requires never_stuck apply s)
      (ensures never_stuck apply (step apply s))
  = introduce forall (n: nat). ~(Stuck? (steps apply n (step apply s)))
    with assert (steps apply (n + 1) s == steps apply n (step apply s))

(** **Loading a program**: the state a run starts from. Every theorem about a
    whole run is indexed by this, and `Hoop.Runtime.execute`'s postcondition
    reads `steps apply n (load c)`. *)
let load (#v #cl: Type) (c: comp_tree v cl) : GTot (state v cl) = Step c []
