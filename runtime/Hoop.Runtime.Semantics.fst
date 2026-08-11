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
 * `Perform` reads as `KOrdinaryOperation` and `PerformS` as `KScopedOperation`,
 * and that reading is the whole of what distinguishes the two dispatch rules
 * below. `ClauseKindMismatch` names the kind the NODE asked for beside the kind
 * the TABLE actually held, so both sides of the comparison have a type of their
 * own.
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
 *     it and its owner hold clauses that cannot be borrowed. `eff` and `op` name
 *     the scoped operation the scope belongs to -- carried on the `Weave` node
 *     from the dispatch that built it, since by the time the borrow is refused
 *     that dispatch may be arbitrarily far away -- and `blocking_effects` names
 *     the effect labels responsible. Both halves are what make the failure
 *     actionable to whoever wrote the handler stack: the first says which scope,
 *     the second says what stands in its way.
 *
 * **Both are produced by the transitions below**, and by different ones: a kind
 * mismatch arises at the dispatch of a `Perform` or a `PerformS`, borrowability
 * at the evaluation of a `Weave`. Keeping them unmixed is what lets each be read
 * as the one thing it is.
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

(* ------------------------------------------------------------------ *)
(*  The same segment, from the ONE list a dispatch actually holds      *)
(*                                                                     *)
(*  `prepare_scope` takes the two parts separately, which is how the   *)
(*  design states the two roles. A transition does not hold them       *)
(*  separately: `find_prompt` -- and `Hoop.Runtime.msplit_fast` -- hand *)
(*  back ONE captured segment, and that it splits as                   *)
(*  `intermediates @ [owner]` with `PromptF? owner` is                 *)
(*  `Hoop.Runtime.Metatheory.find_prompt_last`, a LEMMA ABOUT THE       *)
(*  GENERATION PATH rather than a refinement anything carries.          *)
(*                                                                     *)
(*  Splitting it at the transition is therefore not available: `mstep`  *)
(*  is total on an arbitrary configuration and has no precondition to   *)
(*  spend, and a split that walked the segment to find its last frame   *)
(*  would put back exactly the recursion proportional to the user's     *)
(*  handler nesting that `prepare_scope_fast` exists to keep off the    *)
(*  host stack. So the transition takes the segment whole, and this is  *)
(*  the same transformation read off it: BORROW EVERY FRAME BUT THE     *)
(*  LAST, AND KEEP THE LAST ENTIRE.                                    *)
(*                                                                     *)
(*  `prepare_captured_is_prepare_scope` below is what says the two are  *)
(*  one function seen from two sides; every fact proved about           *)
(*  `prepare_scope` -- `prepare_scope_can`, `prepare_scope_wf` -- is    *)
(*  reached through it, and nothing is restated.                        *)
(* ------------------------------------------------------------------ *)

(**
 * **The segment a scope runs under, from the captured segment alone.** The
 * specification; `prepare_captured_fast` below is what runs.
 *
 * The `[owner]` arm is what makes this the owner's clause: a one-frame segment
 * is kept exactly as it stands, table and return clause both, and every frame
 * reached before that arm is borrowed by the three rules of `borrow`. On a
 * segment that does not end in a prompt -- which no dispatch produces -- it is
 * still total, and simply keeps whatever the last frame is.
 *)
noextract
let rec prepare_captured (#v #cl: Type) (captured: stack v cl)
  : Tot (stack v cl) (decreases captured)
  = match captured with
    | [] -> []
    // The owner. NOT borrowed: it keeps its handler table *and* its return
    // clause, which is the answer former the surface reports a scope's result
    // through. See `prepare_scope`.
    | [owner] -> [owner]
    | BindF _ :: r -> prepare_captured r
    | ParamF l x :: r -> ParamF l x :: prepare_captured r
    | PromptF hs _ :: r -> PromptF hs None :: prepare_captured r

(**
 * **Everything above a non-empty tail is simply borrowed.** The form the monad
 * laws want: they replace a prompt-free block of frames inside a captured
 * segment, and `borrow` drops every frame of such a block, so both sides of a
 * law build the SAME prepared segment. `Hoop.Runtime.Laws` reads the blindness
 * off this together with `borrow_append` there.
 *)
let rec prepare_captured_append (#v #cl: Type) (a: stack v cl) (c: stack v cl)
  : Lemma (requires Cons? c)
          (ensures prepare_captured (a @ c) == borrow a @ prepare_captured c)
          (decreases a)
  = match a with
    | [] -> ()
    // `a @ c` has at least two frames, so the `[owner]` arm cannot fire and both
    // sides peel the same head.
    | _ :: r -> prepare_captured_append r c

(** **The two readings agree.** `prepare_captured` of a segment that really does
    split as `intermediates @ [owner]` is `prepare_scope` of its two parts --
    which is how every lemma proved about the latter is reached from the
    transition, with nothing restated. *)
let prepare_captured_is_prepare_scope
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
  : Lemma (prepare_captured (intermediates @ [owner]) == prepare_scope intermediates owner)
  = prepare_captured_append intermediates [owner]

(** **`prepare_captured`, as a loop**: the accumulating walk of `borrow_rev`,
    with the last frame kept entire. Reversed on the way out, exactly as
    `borrow_rev` is, and for the reason recorded at `prepare_scope_fast`: this
    runs over the user's own handler nesting, and Melange compiles OCaml's stack
    onto JavaScript's. *)
let rec prepare_captured_rev (#v #cl: Type) (captured: stack v cl) (acc: stack v cl)
  : Tot (stack v cl) (decreases captured)
  = match captured with
    | [] -> acc
    | [owner] -> owner :: acc
    | BindF _ :: r -> prepare_captured_rev r acc
    | ParamF l x :: r -> prepare_captured_rev r (ParamF l x :: acc)
    | PromptF hs _ :: r -> prepare_captured_rev r (PromptF hs None :: acc)

private
let rec prepare_captured_rev_spec (#v #cl: Type) (captured: stack v cl) (acc: stack v cl)
  : Lemma (ensures prepare_captured_rev captured acc == rev (prepare_captured captured) @ acc)
          (decreases captured)
  = match captured with
    | [] -> ()
    | [owner] ->
        rev_cons_append owner ([] <: stack v cl) acc;
        append_l_nil (rev ([] <: stack v cl))
    | BindF _ :: r -> prepare_captured_rev_spec r acc
    | ParamF l x :: r ->
        prepare_captured_rev_spec r (ParamF l x :: acc);
        rev_cons_append (ParamF l x <: frame v cl) (prepare_captured r) acc
    | PromptF hs _ :: r ->
        prepare_captured_rev_spec r (PromptF hs None :: acc);
        rev_cons_append (PromptF hs (None #(v -> comp_tree v cl)) <: frame v cl)
                        (prepare_captured r) acc

(**
 * **What the transitions run.** The answer is the specification's, and the
 * equality is in the type, so every statement about `prepare_captured` -- and
 * hence, through `prepare_captured_is_prepare_scope`, about `prepare_scope` --
 * is a statement about what runs.
 *
 * `prepare_scope` and `borrow` stay `noextract`, so a transition that reached
 * for the specification instead would fail at EXTRACTION rather than ship a
 * stack-hungry path with an `@` on it. That guard is the reason for the pairing.
 *)
let prepare_captured_fast (#v #cl: Type) (captured: stack v cl)
  : Tot (o: stack v cl { o == prepare_captured captured })
  = prepare_captured_rev_spec captured [];
    append_l_nil (rev (prepare_captured captured));
    rev_involutive (prepare_captured captured);
    rev (prepare_captured_rev captured [])

(** **And on a real captured segment it is `prepare_scope_fast`**, frame for
    frame: the accumulating walk this runs is the accumulating walk that one
    runs, with the owner pushed by the `[owner]` arm instead of by hand. Stated
    so that the claim "the shipped path computes the fast preparation and never
    the specification" is a proposition and not a reading of two definitions. *)
let prepare_captured_fast_is_prepare_scope_fast
    (#v #cl: Type)
    (intermediates: stack v cl)
    (owner: frame v cl { PromptF? owner })
  : Lemma (prepare_captured_fast (intermediates @ [owner])
             == prepare_scope_fast intermediates owner)
  = prepare_captured_is_prepare_scope intermediates owner;
    prepare_scope_fast_agrees intermediates owner

(* ------------------------------------------------------------------ *)
(*  Borrowability, checked where the borrow is taken                   *)
(* ------------------------------------------------------------------ *)

(**
 * **The effects that stand in the way of this scope**, or `[]` if none do.
 *
 * Every `PromptF` of the prepared segment BUT THE LAST is inspected: the last
 * one is the owner, which is not borrowed and so has nothing to be borrowable
 * for. `BindF` cannot occur in a prepared segment and `ParamF` does not bear on
 * borrowability; both are simply walked past, and neither branch asserts that it
 * is unreachable -- this is **total on an arbitrary segment**, and that a real
 * one is `borrow intermediates @ [owner]` is a lemma about the generation path
 * rather than a refinement on the constructor.
 *
 * `Hoop.Runtime.Handlers.blocking_effects` is what judges a table, and it is
 * stated through `lookup_handler`, so it judges only the entry that would
 * actually be DISPATCHED: a `Full` clause shadowed by a `Fast` one blocks
 * nothing, exactly as it is invisible to `handler_ok`.
 *
 * **The first blocker wins.** What the report needs is a handler stack the user
 * can act on, and the innermost offender is the one to name; accumulating every
 * blocker would mean appending lists on a path that must not call `@` -- see the
 * note on `prepare_scope_fast` -- for a longer message about the same fault.
 *)
let rec scope_blockers (#v #cl: Type) (prepared: stack v cl)
  : Tot (list string) (decreases prepared)
  = match prepared with
    | [] -> []
    // The owner. Not borrowed, so not checked.
    | [_] -> []
    | PromptF hs _ :: rest ->
        (match blocking_effects hs with
          | [] -> scope_blockers rest
          | bs -> bs)
    | _ :: rest -> scope_blockers rest

(**
 * **Applying the weave capability.** A named top-level function for the same
 * reason `kont_of` is one: what a clause receives is the partial application
 * `weave_of eff op prepared`, whose SMT symbol depends on the ORIGIN and the
 * PREPARED SEGMENT alone, rather than a lambda closing over whatever the
 * transition happened to have in scope. The monad laws are proved by showing the
 * two sides build the same three, and that argument is worth nothing if the two
 * weaves are unrelated symbols anyway.
 *
 * All three are identical on the two sides of a law: the redex block a law
 * replaces is `no_prompt`, so it contributes nothing to the prepared segment
 * (`prepare_blind`) and it is not the dispatch, so it contributes nothing to the
 * origin either. The origin therefore adds no obligation to
 * `apply_scoped_obs_congr`, which still speaks of a single fixed weave.
 *)
let weave_of (#v #cl: Type) (eff op: string) (prepared: stack v cl) (d: comp_tree v cl)
  : comp_tree v cl
  = Weave eff op prepared d

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
//
// **Two interpreters, and they stay apart.** `apply` reads an ordinary clause,
// `apply_s` a scoped one; which of the two a dispatch reaches is decided by the
// AST node, and the KIND STORED ON THE TABLE ENTRY is what decides whether that
// dispatch happens at all. Keeping the two interpreters separate is what keeps
// `Hoop.Runtime.WellScopedness.apply_ok` -- an assumption about every program,
// scoped or not -- from having to be conditioned on a clause kind.
let step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
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
      // An ordinary operation. The clause is unwrapped by whatever `apply`
      // makes of it -- the tag on the clause VALUE, which is this module's
      // business only through the abstract `cl` -- but whether an ordinary
      // dispatch is admissible at all is decided HERE, by the kind the table
      // stored beside the clause. A `KScoped` entry reached from a `Perform` is
      // a broken typed boundary, and refusing it is what keeps the machine from
      // handing a scoped clause a continuation where it expects a weave.
      | Perform eff op payload ->
        (match find_prompt eff op k with
          | None -> Stuck eff op
          | Some (captured, found, below) ->
            (match found.kind with
              | KScoped -> Rejected (ClauseKindMismatch eff op KOrdinaryOperation KScoped)
              | _ -> Step (apply found.body payload (kont_of captured)) below))
      // A scoped operation. The clause is handed the payload, a WEAVE
      // CAPABILITY and the continuation, in that order.
      //
      // The weave carries the segment the scope is to run under, prepared from
      // the captured one: the intermediates borrowed -- available for dispatch,
      // no longer an answer boundary -- and the owner kept entire. Nothing about
      // BORROWABILITY is asked here, and that is Decision 5: a scoped clause is
      // entitled to discard an inner computation, so a prompt that could not be
      // borrowed is no reason to refuse a dispatch whose weave may never be
      // applied. The question is asked at the `Weave` node, and only if one is
      // ever evaluated.
      | PerformS eff op payload ->
        (match find_prompt eff op k with
          | None -> Stuck eff op
          | Some (captured, found, below) ->
            (match found.kind with
              | KScoped ->
                Step (apply_s found.body payload
                        (weave_of eff op (prepare_captured_fast captured))
                        (kont_of captured))
                     below
              | KFull -> Rejected (ClauseKindMismatch eff op KScopedOperation KFull)
              | KFast -> Rejected (ClauseKindMismatch eff op KScopedOperation KFast)))
      // Entering a scope. On success this is `Splice`'s rule at the prepared
      // segment -- push the frames, run the body under them -- and the whole of
      // the difference is the guard in front of it.
      //
      // **The rejection names the operation the scope belongs to.** The node
      // carries its origin beside the normalized plan, for exactly the reason it
      // could not be recovered here otherwise: a `Weave` may be evaluated
      // arbitrarily far from the dispatch that produced it -- a clause is free
      // to build a woven computation and run it later, or not at all -- so by
      // this point the dispatch is long gone. Normalization (Decision 7) is a
      // condition on `prepared`, the execution-relevant component, and the
      // guard and the transition below read only that; the origin travels
      // beside it and is read only by the rejection.
      //
      // The other actionable half is the list of handlers that blocked, which is
      // what `scope_blockers` returns. `runtime/ml/melange/hoop_ffi.ml` prints
      // both.
      | Weave oeff oop prepared body ->
        (match scope_blockers prepared with
          | [] -> Step body (prepared @ k)
          | bs -> Rejected (UnborrowableScope oeff oop bs))
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
    (apply_s: scoped_apply_t v cl)
    (fuel: nat)
    (s: state v cl)
  : GTot (state v cl)
  = if fuel = 0 then s
    else
      match s with
      | Done _ -> s
      | Stuck _ _ -> s
      | Rejected _ -> s
      | Step _ _ -> steps apply apply_s (fuel - 1) (step apply apply_s s)

let one_more_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl { Step? s })
    (r: state v cl)
  : Lemma
      (requires exists (n:nat). r == steps apply apply_s n (step apply apply_s s))
      (ensures (exists (m:nat). r == steps apply apply_s m s))
  = eliminate exists (n:nat). r == steps apply apply_s n (step apply apply_s s)
    with
      introduce exists (m:nat). r == steps apply apply_s m s
      with (n + 1) and ()

let no_more_steps
    (#v #cl : Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires Done? s \/ Stuck? s \/ Rejected? s)
      (ensures exists (n:nat). s == steps apply apply_s n s)
  = introduce exists (n:nat). s == steps apply apply_s n s
    with 0
    and ()

let never_stuck
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : GTot prop
  = forall (n: nat). ~(Stuck? (steps apply apply_s n s))

let never_stuck_now
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires never_stuck apply apply_s s)
      (ensures ~(Stuck? s))
  = assert (steps apply apply_s 0 s == s)

let never_stuck_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl { Step? s })
  : Lemma
      (requires never_stuck apply apply_s s)
      (ensures never_stuck apply apply_s (step apply apply_s s))
  = introduce forall (n: nat). ~(Stuck? (steps apply apply_s n (step apply apply_s s)))
    with assert (steps apply apply_s (n + 1) s == steps apply apply_s n (step apply apply_s s))

(**
 * **The rejection axis**, stated separately from `never_stuck` and proved from
 * a different condition. See the note above `rejection`: a run may be
 * `never_stuck` and still be rejected, and conversely, so neither predicate
 * implies the other and neither may be weakened into the other.
 *
 * Two transitions can now refuse: a dispatch whose node and whose table entry
 * disagree about the kind of the operation, and a `Weave` whose prepared segment
 * crosses a prompt that cannot be borrowed. Neither is a missing capability, so
 * neither is `Stuck`, and this is the condition that rules them out.
 *)
let never_rejected
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : GTot prop
  = forall (n: nat). ~(Rejected? (steps apply apply_s n s))

let never_rejected_now
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl)
  : Lemma
      (requires never_rejected apply apply_s s)
      (ensures ~(Rejected? s))
  = assert (steps apply apply_s 0 s == s)

let never_rejected_step
    (#v #cl: Type)
    (apply: apply_t v cl)
    (apply_s: scoped_apply_t v cl)
    (s: state v cl { Step? s })
  : Lemma
      (requires never_rejected apply apply_s s)
      (ensures never_rejected apply apply_s (step apply apply_s s))
  = introduce forall (n: nat). ~(Rejected? (steps apply apply_s n (step apply apply_s s)))
    with assert (steps apply apply_s (n + 1) s == steps apply apply_s n (step apply apply_s s))

(** **Loading a program**: the state a run starts from. Every theorem about a
    whole run is indexed by this, and `Hoop.Runtime.execute`'s postcondition
    reads `steps apply apply_s n (load c)`. *)
let load (#v #cl: Type) (c: comp_tree v cl) : GTot (state v cl) = Step c []
