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

(* ------------------------------------------------------------------ *)
(*  The context a scope runs under                                     *)
(*                                                                     *)
(*  A scoped operation does not resume its perform site: it runs an     *)
(*  INNER COMPUTATION under the handlers that site could see. Which     *)
(*  handlers those are, and on what terms they are offered, is the      *)
(*  whole content of the two functions below.                          *)
(*                                                                     *)
(*  NOTHING CALLS THEM YET, and that is deliberate. A scoped perform    *)
(*  node and the transition that dispatches it are one semantic slice   *)
(*  together; this is the stack surgery that slice will rest on,        *)
(*  landed on its own so that the two facts everything downstream       *)
(*  needs -- `Hoop.Runtime.Metatheory.prepare_scope_can` and            *)
(*  `prepare_scope_wf` -- are proved before anything depends on them.   *)
(*                                                                     *)
(*  See docs/study-notes/2026-08-11-scoped-effects-detailed-design.md,  *)
(*  Decision 2.                                                        *)
(* ------------------------------------------------------------------ *)

(**
 * **Borrowing a stack segment**: what is left of it once it is offered for
 * DISPATCH but no longer as an ANSWER BOUNDARY.
 *
 * Three clauses, and each of them is a separate decision:
 *
 *   - `BindF` is DROPPED. A bind frame is the perform site's own continuation,
 *     and a scope is not a resumption -- the inner computation runs *instead
 *     of* the rest of the enclosing block, not before it. Dropping it is also
 *     what keeps a masked prompt out: while a tail-resumptive clause body is in
 *     flight, the erasure has already absorbed that clause's own prompt into a
 *     `BindF (kont_of ...)`, so a handler the perform site could not see cannot
 *     re-enter through the borrowed context either.
 *
 *   - `PromptF` KEEPS ITS TABLE AND LOSES ITS RETURN CLAUSE. The table is
 *     exactly the capability the scope is being lent; the return clause is an
 *     answer transformation, and a borrowed prompt is not where the scope's
 *     answer is formed. `ret = None` says that with the option the frame
 *     already carries -- no new constructor, and so no new case in the erasure,
 *     the machine, or the FFI whitelist.
 *
 *   - `ParamF` is KEPT ENTIRE, label AND value. A cell is a capability under
 *     `var_eff` in the very same environment that tables live in, so dropping
 *     one would silently withdraw a capability the perform site had:
 *     `Hoop.Runtime.Metatheory.prepare_scope_can` is FALSE without this clause,
 *     because `param_in` would not be preserved. Keeping the cell where it
 *     stood relative to its prompt is what makes the borrowing coherent -- a
 *     borrowed clause still meets its own cell first, with no runtime label
 *     minting. And because the frame holds the VALUE and not a pointer to one,
 *     what a scope receives is a snapshot that branches; a cell stays live only
 *     for a handler sitting outside the scoped one, which is the composition
 *     order deciding it, not new machinery.
 *
 * Frame order is preserved throughout. This is a filter-and-rewrite, never a
 * reordering, and every claim that the result is "the same context" rests on
 * that.
 *
 * *This is the specification*, and it is `noextract` for that reason: what runs
 * is `borrow_rev` below, which computes the same list with an accumulator. See
 * `prepare_scope_fast` for why the difference is not a matter of taste.
 *)
noextract
let rec borrow (#v #cl: Type) (k: stack v cl) : Tot (stack v cl) (decreases k)
  = match k with
    | [] -> []
    | BindF _ :: r -> borrow r
    | ParamF l x :: r -> ParamF l x :: borrow r
    | PromptF hs _ :: r -> PromptF hs None :: borrow r

(**
 * **The segment a scope runs under**, assembled from the two parts a dispatch
 * hands over. `Hoop.Runtime.Metatheory.find_prompt_partitions` and
 * `find_prompt_last` between them give `captured == intermediates @ [owner]`
 * with `PromptF? owner`, and the two parts play DIFFERENT ROLES.
 *
 * The intermediates are borrowed. The owner -- the prompt whose table holds the
 * clause being dispatched to -- is NOT: it keeps its handler table *and* its
 * return clause, unchanged. That return clause is the answer former the surface
 * relies on to report a scope's result at the handler's own answer type;
 * setting it to `None` would make handlers such as `once` inexpressible. With
 * head = innermost the ordering works out on its own: a value leaving the scope
 * passes the transparent borrowed frames and meets the owner LAST, so the
 * answer transformation is applied exactly once.
 *
 * **The two roles are visible in this SIGNATURE rather than in a frame
 * constructor.** `frame` gains nothing, so the erasure, the build guards and the
 * FFI whitelist all stay as they are; the refinement on `owner` is what carries
 * the distinction instead. Splitting a real `captured` into the two parts is the
 * caller's job, and belongs with the transition that does the dispatch.
 *
 * **Borrowability is neither checked here nor assumed.** Whether the borrowed
 * prompts may be borrowed at all is a different question, answered at the
 * transition and reported as a rejection rather than as a stuck state. This
 * function is the transformation and nothing else -- which is precisely what
 * lets its two lemmas be proved with no premise about what kind of clause any
 * table holds.
 *
 * *This is the specification.* What runs is `prepare_scope_fast` below, which
 * `prepare_scope_fast_agrees` proves computes this very list. The two reasons
 * this one is `noextract` -- the `@`, and the shape of the recursion in `borrow`
 * -- are both recorded there.
 *)
noextract
let prepare_scope
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
  : stack v cl
  = borrow intermediates @ [owner]

(**
 * **`borrow`, as a loop.** Same three decisions, same frame order, taken from
 * the outside in onto an accumulator -- so the result comes out reversed, and
 * the one `rev` in `prepare_scope_fast` puts it back.
 *
 * `borrow_rev k acc == rev (borrow k) @ acc`, which is `borrow_rev_spec` below.
 *)
let rec borrow_rev (#v #cl: Type) (k: stack v cl) (acc: stack v cl)
  : Tot (stack v cl) (decreases k)
  = match k with
    | [] -> acc
    | BindF _ :: rest -> borrow_rev rest acc
    | ParamF l x :: rest -> borrow_rev rest (ParamF l x :: acc)
    | PromptF hs _ :: rest -> borrow_rev rest (PromptF hs None :: acc)

(* Pushing one frame onto the accumulator prepends it to the reversed answer.
   The only arithmetic of `rev` the induction below needs, stated once so that
   the two frame-keeping branches cite it rather than re-derive it. *)
private
let rev_cons_append (#a: Type) (x: a) (acc l: list a)
  : Lemma (rev (x :: acc) @ l == rev acc @ (x :: l))
  = rev_rev' (x :: acc);
    rev_rev' acc;
    append_assoc (rev acc) [x] l

private
let rec borrow_rev_spec (#v #cl: Type) (k: stack v cl) (acc: stack v cl)
  : Lemma (ensures borrow_rev k acc == rev (borrow k) @ acc) (decreases k)
  = match k with
    | [] -> ()
    | BindF _ :: rest -> borrow_rev_spec rest acc
    | ParamF l x :: rest ->
        borrow_rev_spec rest (ParamF l x :: acc);
        rev_cons_append (ParamF l x <: frame v cl) (borrow rest) acc
    | PromptF hs _ :: rest ->
        borrow_rev_spec rest (PromptF hs None :: acc);
        rev_cons_append (PromptF hs (None #(v -> comp_tree v cl)) <: frame v cl)
                        (borrow rest) acc

(**
 * **The segment a scope runs under, as the machine builds it.** An accumulating
 * walk and one final `rev`; `prepare_scope_fast_agrees` says it is
 * `prepare_scope`, frame for frame.
 *
 * *Why the specification is `noextract` and this is what ships.* Two reasons,
 * and only one of them is about `@`.
 *
 *   - `prepare_scope` appends with `@`, which extracts to
 *     `FStar_List_Tot_Base.op_At`. `runtime/ml/shim/FStar_List_Tot_Base.ml`
 *     holds only what is live and deleted `op_At` once nothing called it, under
 *     its own policy that dead trusted code is the kind that is still trusted
 *     when someone makes it live again. Extracting the specification would put
 *     that entry back, growing the TCB by one, for an append proportional to its
 *     left argument.
 *
 *   - `borrow` conses on the way OUT of its recursion, so it is not tail
 *     recursive: extracted, it holds one host frame per frame of the segment.
 *     That is the whole argument the shim's header gives for writing `rev` and
 *     `rev_append` tail-recursively there -- Melange compiles OCaml's stack onto
 *     JavaScript's, where the frame limit is a few tens of thousands, so a
 *     direct recursion over a user-sized list is a ceiling on how deeply a
 *     user's program may nest, reported as an opaque `RangeError` rather than as
 *     anything the program did. The segment here is exactly a run of the user's
 *     handler nesting, so it is precisely the list that argument is about. The
 *     accumulator is therefore not a micro-optimisation; it is what keeps the
 *     shipped path flat.
 *
 * `borrow_rev` is a tail call in every branch, and `rev` is a loop in the shim,
 * so nothing here recurses to the segment's depth. Both `borrow` and
 * `prepare_scope` are `noextract`, which also buys a guard: a later transition
 * that reaches for the specification instead of this fails at EXTRACTION rather
 * than shipping a stack-hungry path.
 *)
let prepare_scope_fast
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
  : stack v cl
  = rev (owner :: borrow_rev intermediates [])

(**
 * **The two agree.** Route: `borrow_rev_spec` at `acc = []` turns the walk into
 * `rev (borrow intermediates)`; reversing `owner ::` that is
 * `rev (rev (borrow intermediates)) @ [owner]`, and `rev_involutive` collapses
 * the double reversal to `borrow intermediates @ [owner]`, which is
 * `prepare_scope`.
 *)
let prepare_scope_fast_agrees
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
  : Lemma (prepare_scope_fast intermediates owner == prepare_scope intermediates owner)
  = borrow_rev_spec intermediates [];
    append_l_nil (rev (borrow intermediates));
    // `borrow_rev intermediates [] == rev (borrow intermediates)`; call it `l`.
    rev_cons_append owner (rev (borrow intermediates)) [];
    append_l_nil (rev (owner :: rev (borrow intermediates)));
    // `rev (owner :: l) == rev l @ [owner]`, and `rev l` is `borrow intermediates`.
    rev_involutive (borrow intermediates)

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

(**
 * **The rejection axis**, stated separately from `never_stuck` and proved from
 * a different condition. See the note above `rejection`: a run may be
 * `never_stuck` and still be rejected, and conversely, so neither predicate
 * implies the other and neither may be weakened into the other.
 *
 * It holds *vacuously* of every program this repository can build, since no
 * transition returns `Rejected`. That is the point of introducing it now: the
 * statement it strengthens -- `Hoop.Runtime.execute`'s guarded conjunct -- is
 * written once, in the form it will keep.
 *)
let never_rejected
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : GTot prop
  = forall (n: nat). ~(Rejected? (steps apply n s))

let never_rejected_now
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires never_rejected apply s)
      (ensures ~(Rejected? s))
  = assert (steps apply 0 s == s)

let never_rejected_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (s: state v cl { Step? s })
  : Lemma
      (requires never_rejected apply s)
      (ensures never_rejected apply (step apply s))
  = introduce forall (n: nat). ~(Rejected? (steps apply n (step apply s)))
    with assert (steps apply (n + 1) s == steps apply n (step apply s))

(** **Loading a program**: the state a run starts from. Every theorem about a
    whole run is indexed by this, and `Hoop.Runtime.execute`'s postcondition
    reads `steps apply n (load c)`. *)
let load (#v #cl: Type) (c: comp_tree v cl) : GTot (state v cl) = Step c []
