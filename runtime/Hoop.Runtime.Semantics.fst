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

(* ------------------------------------------------------------------ *)
(*  Boundary rejections                                                *)
(*                                                                     *)
(*  A rejection is NOT a `Stuck`. Keeping the two apart is the whole    *)
(*  point of the type below, so the distinction is stated once, here,   *)
(*  and referred to from both constructors.                            *)
(*                                                                     *)
(*  `Stuck` means one thing throughout this development: A REQUIRED     *)
(*  DYNAMIC CAPABILITY IS ABSENT -- an operation no prompt on the stack *)
(*  handles, or a `read`/`write` with no `ParamF` to reach.             *)
(*  `Hoop.Runtime.WellScopedness.wf_state` sets that state to `False`,  *)
(*  and `Hoop.Runtime.Metatheory.progress` PROVES it unreachable from a *)
(*  well-scoped one.                                                   *)
(*                                                                     *)
(*  A rejection is a different failure. The operation IS handled and    *)
(*  the transition IS defined; what cannot be guaranteed on this side   *)
(*  of the boundary is the ANSWER-TYPE AGREEMENT the PureScript surface *)
(*  assumes when it hands a clause over. Folding the two together would *)
(*  inject that agreement into a theorem which currently says something *)
(*  else, so the two axes are kept orthogonal:                          *)
(*                                                                     *)
(*    well-scopedness               -> never Stuck                     *)
(*    typed-boundary compatibility  -> never Rejected                  *)
(*    termination + both            -> Done                            *)
(*                                                                     *)
(*  See docs/study-notes/2026-08-11-scoped-effects-detailed-design.md,  *)
(*  Decision 7.                                                        *)
(* ------------------------------------------------------------------ *)

(**
 * **What kind of operation an AST node asks for**, as read off the node itself
 * -- the counterpart, on the perform side, of
 * `Hoop.Runtime.Handlers.clause_kind` on the table side.
 *
 * **Inhabited meaningfully only once a scoped perform node exists.** The AST has
 * a single perform constructor today, so every node this repository can build
 * reads as `KOrdinaryOperation`; `KScopedOperation` is what a dedicated scoped
 * perform will read as. It is declared here rather than with that node so that
 * `ClauseKindMismatch` below -- which has to name the kind the node ASKED for
 * beside the kind the table ACTUALLY held -- means the same thing before and
 * after, and so that adding the node does not reopen this type.
 *)
type operation_kind =
  | KOrdinaryOperation
  | KScopedOperation

(**
 * **Why a dispatch was refused at the boundary.**
 *
 * Flat, and deliberately independent of `v` and `cl`: `clause_kind` is flat for
 * the reason its own comment gives, so a rejection can be named in this
 * `cl`-polymorphic module and BOTH machines can share the one type --
 * `Hoop.Runtime.erase_st` maps `MRejected r` to `Rejected r` with nothing to
 * translate.
 *
 *   - `ClauseKindMismatch`: the node asked for one kind of operation and the
 *     entry it dispatched to held another. The PureScript surface rules this
 *     out -- an operation's signature is the single source of truth from which
 *     both the perform site and the clause's canonical type are derived -- but
 *     the runtime cannot assume it, and a wrong answer is worse than a refusal.
 *
 *   - `UnborrowableScope`: a scope could not be entered because prompts between
 *     it and its owner hold clauses that cannot be borrowed. `blocking_effects`
 *     names the effect labels responsible, which is the only thing that makes
 *     the failure actionable to whoever wrote the handler stack.
 *
 * **Nothing in this repository builds one yet.** No transition returns
 * `Rejected`, so `never_rejected` below is trivially satisfiable and the
 * guarded half of `Hoop.Runtime.execute` is exactly as strong as it was. The
 * outcome is introduced ahead of its producers because it is a terminal state
 * -- its meaning is complete without them -- and because the alternative is to
 * change the same public signature twice.
 *)
type rejection =
  | ClauseKindMismatch : eff:string -> op:string
                      -> expected:operation_kind -> actual:clause_kind -> rejection
  | UnborrowableScope  : eff:string -> op:string
                      -> blocking_effects:list string -> rejection

(** The machine state *)
noeq
type state (v: Type) (cl: Type) =
  | Done : (value:v) -> state v cl
  | Step : (c:comp_tree v cl) -> (k:stack v cl) -> state v cl
  // Unhandled effect operation exception which should never occur
  // as long as the runtime is sound
  | Stuck : eff: string -> op: string -> state v cl
  // A dispatch refused at the typed boundary. Terminal, exactly as `Done` and
  // `Stuck` are, and ruled out by a DIFFERENT condition than `Stuck` is -- see
  // the note above `rejection`.
  | Rejected : rejection -> state v cl

// ------------------------------------------------------------------ //

// Is this frame responsible for the action `(eff, op)`?
let handles
    (#v #cl: Type)
    (eff op: string)
    (f: frame v cl)
  : GTot (b:bool { b <==> (PromptF? f /\ Some? (lookup_clause (PromptF?.hs f) eff op) )})
  = match f with
    | PromptF hs _ -> Some? (lookup_clause hs eff op)
    | ParamF _ _ -> false
    | BindF _ -> false

// Can this action be handled within this stack?
let handled_in
    (#v #cl : Type)
    (eff op : string)
    (k: stack v cl)
  : GTot prop
  = exists (f: frame v cl). (f `memP` k /\ handles eff op f)

// Finds the prompt holding the handler for the given action and splits the
// stack there, returning `(captured, found, below)`. The captured segment is
// every frame above the matching prompt, prompt included, so resuming
// reinstalls the handler — deep-handler semantics.
//
// The middle component is a `found_clause`: the clause together with the kind
// the table it came from gave it. It is carried rather than looked up again
// because the two would then be two searches that could disagree, and because
// the kind is what decides which interpreter a clause may be unwrapped to. The
// dispatch below reads only `.body`; every existing theorem about this function
// therefore says what it always said, at one component's new type.
let rec find_prompt
    (#v #cl : Type)
    (eff op : string)
    (k : stack v cl)
  : GTot
      (o: option (stack v cl & found_clause cl & stack v cl) { handled_in eff op k <==> Some? o })
      (decreases k)
  = match k with
    | [] -> None
    | PromptF hs ret :: rest ->
      // `handles` — and so `handled_in`, which the refinement above is stated in
      // — asks `lookup_clause`; the search asks `lookup_handler`. That the two
      // miss together is the coherence lemma, and this is the one place the
      // reference machine spends it.
      lookup_handler_agrees hs eff op;
      (match lookup_handler hs eff op with
        | Some c -> Some ([PromptF hs ret], c, rest)
        | None ->
          (match find_prompt eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PromptF hs ret :: cap, c, below)))
    | f :: rest ->
      (match find_prompt eff op rest with
        | None -> None
        | Some (cap, c, below) -> Some (f :: cap, c, below))


(* ------------------------------------------------------------------ *)
(*  Prompt-local state                                                 *)
(*                                                                     *)
(*  A cell is a `ParamF` frame. Reading walks to the nearest one with   *)
(*  the right label; writing REBUILDS the stack down to it. Nothing is  *)
(*  mutated, so a `ParamF` sitting inside a captured segment travels    *)
(*  with the capture and every resumption gets its own copy -- which is *)
(*  what makes the composition order of two handlers observable.        *)
(* ------------------------------------------------------------------ *)

(**
 * **The reserved effect name a cell is a capability under.** Cells share the
 * capability environment of `Hoop.Runtime.WellScopedness` with handlers, and the
 * key namespace is partitioned: no handler table may bind an operation under
 * this name and no `Perform` may claim one. See `ws_n` there.
 *)
let var_eff : string = "%hoop.var"

// Does this frame hold the cell labelled `l`?
let binds_param (#v #cl: Type) (l: string) (f: frame v cl)
  : GTot (b:bool { b <==> (ParamF? f /\ ParamF?.label f == l) })
  = match f with
    | ParamF l' _ -> l' = l
    | _ -> false

// Is the cell `l` reachable in this stack?
let param_in (#v #cl: Type) (l: string) (k: stack v cl) : GTot prop
  = exists (f: frame v cl). (f `memP` k /\ binds_param l f)

// `read`: the current contents of the nearest cell labelled `l`.
let rec find_param (#v #cl: Type) (l: string) (k: stack v cl)
  : GTot (o: option v { param_in l k <==> Some? o }) (decreases k)
  = match k with
    | [] -> None
    | ParamF l' x :: rest -> if l' = l then Some x else find_param l rest
    | _ :: rest -> find_param l rest

// `write`: the stack with the nearest cell labelled `l` set to `x`. The frames
// above the cell are rebuilt, the frames below are shared.
let rec set_param (#v #cl: Type) (l: string) (x: v) (k: stack v cl)
  : GTot (o: option (stack v cl) { param_in l k <==> Some? o }) (decreases k)
  = match k with
    | [] -> None
    | ParamF l' y :: rest ->
        if l' = l then Some (ParamF l x :: rest)
        else (match set_param l x rest with
              | None -> None
              | Some rest' -> Some (ParamF l' y :: rest'))
    | f :: rest ->
        (match set_param l x rest with
          | None -> None
          | Some rest' -> Some (f :: rest'))

// The delimited continuation handed to a clause.
// While `kont_of captured` is definitionally `fun x -> resumed captured x`, that is,
// `fun x -> Splice captured (Var x)`,
// it is worth defining it as a top-level named function due to the limitation
// described in the book:
// https://fstar-lang.org/tutorial/book/part1/part1_quicksort.html#limitations-of-smt-based-proofs-at-higher-order
let kont_of (#v #cl: Type)
    (captured: stack v cl)
    (x: v)
  : comp_tree v cl
  = resumed captured x

// The small-step semantics of the machine.
let step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : GTot (state v cl)
  = match s with
    | Done _ -> s
    | Stuck _ _ -> s
    | Rejected _ -> s
    | Step c k ->
      match c with
      | Op comp fn -> Step comp (BindF fn :: k)
      | Handle hs pure body -> Step body (PromptF hs pure :: k)
      | Perform eff op payload ->
        (match find_prompt eff op k with
          | None -> Stuck eff op
          | Some (captured, found, below) ->
            Step (apply found.body payload (kont_of captured)) below)
      | Var value ->
        (match k with
          | [] -> Done value
          | (BindF fn)::rest -> Step (fn value) rest
          | (ParamF _ _)::rest -> Step (Var value) rest
          | (PromptF _ pure)::rest ->
            (match pure with
              | Some fn -> Step (fn value) rest
              | None -> Step (Var value) rest
            )
        )
      // Push the captured frames back, then run the body under them. At
      // `body = Var x` -- which is `resumed fs x`, the only shape the machine
      // builds today -- this reads `Step (Var x) (fs @ k)`: the resumption rule,
      // unchanged and definitionally so.
      | Splice fs c -> Step c (fs @ k)
      | NewP l init body -> Step body (ParamF l init :: k)
      | ReadP l ->
        (match find_param l k with
          | None -> Stuck var_eff l
          | Some x -> Step (Var x) k)
      | WriteP l x ->
        (match set_param l x k with
          | None -> Stuck var_eff l
          | Some k' -> Step (Var x) k')


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
      | Rejected _ -> s
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
      (requires Done? s \/ Stuck? s \/ Rejected? s)
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
