(**
 * **B1 -- the general weave, as an executable REFERENCE semantics.**
 *
 * A scope may cross an intervening prompt today only when every clause that
 * prompt can dispatch is `KFast`; anything else is
 * `Hoop.Runtime.Semantics.Rejected (UnborrowableScope ...)`. The reason is not
 * operational: a `Full` clause's canonical surface type mentions the handler's
 * answer type, so a prompt built at one answer type cannot be reinstalled at the
 * scope's unknown result type. See the design note,
 * `docs/study-notes/2026-08-11-scoped-effects-detailed-design.md`, "What
 * borrowability actually is".
 *
 * The reframing this module implements: at the machine level there is ONE value
 * type `v` and ONE clause type `cl`, and the surface erases types, so
 * **re-instantiating a table costs nothing** -- the same table is already
 * correct at every answer type *provided there is evidence it was built as a
 * family*. That evidence is the one half of the classification that cannot be
 * recovered from an erased table, so it is carried on the prompt as
 * PROVENANCE. Everything else is derived from the real frame data.
 *
 * *What this module is.* A small machine, not a copy of the production one. It
 * holds only what the general weave needs: prompt provenance, the classification
 * derived from it, the scope PLAN a captured segment is turned into, the three
 * context operations over that plan, a step relation that covers them, and the
 * laws they owe -- **stated, not proved**. Clarity over efficiency throughout,
 * and no optimization pass at all: the transparent case here is part of the
 * general path and is NOT yet a fast path. Making it one, and proving the two
 * agree, is B3.
 *
 * *What it is not.* It is not extracted, not reachable from the FFI, and not in
 * the bundle -- `scripts/build-runtime.sh` verifies `runtime/proto/*.fst` and
 * checks that a prototype cannot be named into an extracted namespace.
 * `Hoop.Runtime.*` is untouched: this module READS those modules (the handler
 * table, `rejection`, `var_eff`) and rewrites the parts whose representation is
 * under design.
 *
 * *What it deliberately leaves out, and why.* There is no scoped DISPATCH rule
 * here -- no general `PerformS`. The reason is that the CONTINUATION a general
 * scoped clause receives is not the one the shipped machine hands over, and
 * settling which it is belongs with the law that constrains it rather than with
 * a transition written first.
 *
 * `Hoop.Runtime.Semantics.kont_of captured` is a function that SPLICES the
 * captured segment. The plan re-installs that segment itself -- that is what
 * `plan_resume_frames` is -- so a clause holding such a splice and handing it to
 * `resume_C` would install every prompt of the segment twice. What `resume_C`
 * takes is therefore the perform site's INNER continuation, a function run at
 * each value the context holds and UNDER the re-entered segment, and
 * "`continue k x`" at the general level is `resume_C` at a one-value context --
 * which is precisely what `law_resume_matches_continuation` says, and why it is
 * the law that ties this machine to the one that ships.
 *
 * So the node a dispatch would build (`PWeave`) is here and the dispatch that
 * would build it is not; the same posture `Hoop.Runtime.Semantics.prepare_scope`
 * was landed in, and for the same reason -- the facts everything downstream
 * needs are proved before anything depends on them.
 *)
module Hoop.Proto.GeneralWeave

open FStar.List.Tot
// `handlers`, `lookup_handler`, `found_clause`, `blocking_effects`, `borrowable`
// -- the table is NOT under design here and is taken as it ships.
open Hoop.Runtime.Syntax
// `rejection` / `UnborrowableScope` / `var_eff`. The rejection type is flat and
// independent of `v` and `cl` precisely so that a second machine can share it
// with nothing to translate; that is what lets plan construction below fail into
// the SAME rejection the shipped machine produces.
open Hoop.Runtime.Semantics

(* ------------------------------------------------------------------ *)
(*  Provenance                                                         *)
(* ------------------------------------------------------------------ *)

(**
 * **Where a prompt came from**, and the ONLY new thing a frame carries.
 *
 * `PFamily` is what a family installation -- `withF` on the surface -- attaches.
 * `PMono` is what an ordinary `with` attaches.
 *
 * **The asymmetry recorded here is the entire justification for a new field.**
 * The other two halves of the classification -- `ret = None`, and "every
 * dispatch-visible clause is `KFast`" -- are facts about the REAL `ret` field
 * and the REAL table, and are read off them below. They are never taken from a
 * boolean supplied by the FFI: a boundary that could assert "this prompt is
 * transparent" would be asserting the very thing the borrow check exists to
 * verify, exactly as a boundary-supplied clause classifier would be (which is
 * why `Hoop.Runtime.Handlers.mk_handlers` takes the classifier and
 * `scripts/build-runtime.sh` forbids the FFI from calling it).
 *
 * Provenance is different in kind and that is why it must be carried:
 * `withF (HandlerF installer) = installer` calls the ordinary `withImpl`, so the
 * `HandlerF` type is gone by the time a prompt frame exists, and an erased table
 * cannot be asked whether it came from a family. Re-instantiation is free as
 * COMPUTATION, not as EVIDENCE.
 *)
type prompt_provenance =
  | PMono
  | PFamily

(**
 * **The three-way classification**, derived below rather than stored.
 *
 *   - `Family`             -- provenance is `PFamily`.
 *   - `ContextTransparent` -- provenance is `PMono`, `ret = None`, and the table
 *                             blocks nothing (`blocking_effects hs == []`).
 *   - `Monomorphic`        -- otherwise; a scope may not cross it.
 *
 * `ContextTransparent` rather than `Borrowable`: the second names an
 * implementation, the first names the property that makes the implementation
 * sound.
 *
 * **This is narrower than today's criterion, deliberately.**
 * `Hoop.Runtime.Semantics.scope_blockers` reads clause kinds only, so an
 * all-fast handler with a non-identity `pure` is borrowed today and its return
 * transformation silently dropped inside the scope. Here such a handler
 * installed with plain `with` is `Monomorphic`, i.e. refused. A fourth
 * "context-discarding" class to preserve the old answer was considered and
 * rejected: it would formalise exactly the silent semantic difference this
 * project avoids everywhere else.
 *)
type prompt_class =
  | Family
  | ContextTransparent
  | Monomorphic

(* ------------------------------------------------------------------ *)
(*  The prototype AST                                                  *)
(*                                                                     *)
(*  `Hoop.Runtime.Syntax.comp_tree` / `frame` with provenance on the    *)
(*  prompt, and with the three context operations given nodes of their  *)
(*  own. Every constructor is renamed (`P...`) so that nothing here     *)
(*  shadows the production type: a prototype that could be confused for  *)
(*  the shipped AST at a call site is a prototype that will be, and     *)
(*  `--print_full_names` is not something a reader runs by default.     *)
(*                                                                     *)
(*  The block is mutually recursive and cannot be split: `plan_item`    *)
(*  holds return clauses (`v -> pcomp`), `pctx` holds a computation,    *)
(*  and the extend/resume nodes hold a `plan` and a `pctx`.             *)
(* ------------------------------------------------------------------ *)

noeq
type pcomp (v: Type u#a) (cl: Type u#a) : Type u#a =
  | POp: c:pcomp v cl -> fn:(v -> pcomp v cl) -> pcomp v cl
  | PVar: value:v -> pcomp v cl
  | PPerform: eff:string -> op:string -> payload:list v -> pcomp v cl
  // `PromptF` installation, WITH provenance. This is the surface's `with`
  // (`PMono`) and `withF` (`PFamily`) at one node: they differ in the evidence
  // they attach and in nothing else, which is the reframing made syntax.
  | PHandle:
      hs:handlers cl ->
      ret:option (v -> pcomp v cl) ->
      prov:prompt_provenance ->
      body:pcomp v cl ->
      pcomp v cl
  | PSplice: frames:list (pframe v cl) -> body:pcomp v cl -> pcomp v cl
  // **Entering a scope.** The general-level counterpart of
  // `Hoop.Runtime.Syntax.Weave`, and it carries the segment UNPREPARED -- the
  // raw intervening frames and the owner -- because at the general level the
  // preparation IS the plan construction, and plan construction is what can
  // fail. Preparing at the dispatch, as the shipped machine does, would put the
  // failure at a point where Decision 5 says it does not belong: a scoped clause
  // is entitled to discard an inner computation, so a layer that cannot be
  // crossed is no reason to refuse a dispatch whose weave may never be applied.
  //
  // The origin (`oeff`, `oop`) travels for the reason it travels on `Weave`: by
  // the time the plan is built the dispatch may be arbitrarily far away, and the
  // rejection has to name the scope it is refusing.
  //
  // **The owner is a field of its own, not the last frame of a list.** That is
  // the same decision `Hoop.Runtime.Semantics.prepare_scope` takes in its
  // SIGNATURE, and here it is taken in the CONSTRUCTOR: an owner that had to be
  // recovered as the last element of a segment would be an owner that could be
  // borrowed by a walk that stopped one frame early.
  | PWeave:
      oeff:string -> oop:string ->
      intermediates:list (pframe v cl) ->
      owner:powner v cl ->
      body:pcomp v cl ->
      pcomp v cl
  // The two context operations that consume a context. `enter_C` needs no node
  // of its own: it is what `PWeave` steps to.
  | PExtendC: pl:plan v cl -> cx:pctx v cl -> g:(v -> pcomp v cl) -> pcomp v cl
  | PResumeC: pl:plan v cl -> cx:pctx v cl -> k:(v -> pcomp v cl) -> pcomp v cl
  | PNewP: label:string -> init:v -> body:pcomp v cl -> pcomp v cl
  | PReadP: label:string -> pcomp v cl
  | PWriteP: label:string -> value:v -> pcomp v cl

and pframe (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PBindF: fn:(v -> pcomp v cl) -> pframe v cl
  | PParamF: label:string -> value:v -> pframe v cl
  | PPromptF:
      hs:handlers cl ->
      ret:option (v -> pcomp v cl) ->
      prov:prompt_provenance ->
      pframe v cl

(**
 * **The owner of a scope**, as a thing with a name.
 *
 * It is the prompt whose table holds the clause being dispatched to, and it is
 * NOT an intervening layer: it is not borrowed, it is not classified, and it
 * keeps its table AND its return clause -- that clause is the answer former the
 * surface reports a scope's result through, and setting it to `None` would make
 * handlers such as `once` inexpressible.
 *
 * Its provenance is carried but never read by the classification, because the
 * owner is never classified. It is carried so that re-installing the owner
 * inside the scope puts back the frame that was there: a scope nested inside
 * this one meets this prompt as an INTERVENING one, and must classify it then
 * from the same evidence.
 *)
and powner (v: Type u#a) (cl: Type u#a) : Type u#a =
  | POwner:
      hs:handlers cl ->
      ret:option (v -> pcomp v cl) ->
      prov:prompt_provenance ->
      powner v cl

(**
 * **One entry of the plan**, and there is one constructor per MECHANISM.
 *
 * A mixed stack -- transparent / family / transparent / family -- is a list
 * mixing these constructors, each handled by its own rule, which is what the
 * requirement "do not force one uniform treatment" asks for. A single
 * constructor with a `prompt_class` field would have been shorter and would have
 * made every consumer re-decide, at every use, which of the three it was looking
 * at.
 *
 *   - `PIBind` is the perform site's own continuation, RECORDED AND NOT DROPPED
 *     -- which is the one place this plan departs from
 *     `Hoop.Runtime.Semantics.borrow`, and it is forced. `borrow` may drop a bind
 *     frame because the shipped machine keeps a SECOND list, the raw `captured`,
 *     and resumes through that one; the plan is a single object and both roles
 *     are read off it, so a dropped bind frame would be a piece of the perform
 *     site's continuation that nothing could put back. It cannot be recovered
 *     from the outside either: the bind frames are INTERLEAVED with the prompts
 *     (`[bind, layer, bind, owner]` is an ordinary stack), so a continuation
 *     supplied at re-entry could only be spliced innermost and would land the
 *     later ones in the wrong place.
 *
 *     What survives of `borrow`'s decision is the same decision, moved one step
 *     later: `plan_enter_frames` DROPS these and `plan_resume_frames` KEEPS them,
 *     because a scope is not a resumption -- the inner computation runs *instead
 *     of* the rest of the enclosing block, while a resumption continues it. Two
 *     projections of one ordered list, in place of two lists whose orders could
 *     drift apart.
 *
 *   - `PICell` is a prompt-local cell, KEPT ENTIRE, label and value. A cell is a
 *     capability under `var_eff` in the same environment tables live in, so
 *     dropping one would silently withdraw a capability the perform site had.
 *     Identical to `Hoop.Runtime.Semantics.borrow`'s `ParamF` clause and for
 *     identical reasons.
 *
 *   - `PITransparent` holds a table and NO return clause -- not because the
 *     return clause is dropped, but because the classification already
 *     established there was none. That is the one visible difference from
 *     today's `borrow`, which clears a `ret` it finds; here a prompt with a
 *     `ret` is not transparent in the first place. The constructor's shape is
 *     what says so.
 *
 *   - `PIReenter` is a family layer: table AND return clause, kept. It is the
 *     only kind that CONTRIBUTES A LAYER to the context -- a transparent prompt
 *     contributes none, which is exactly why `ctx` is `Identity` at the shipped
 *     borrowable milestone.
 *)
and plan_item (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PIBind: fn:(v -> pcomp v cl) -> plan_item v cl
  | PICell: label:string -> value:v -> plan_item v cl
  | PITransparent: hs:handlers cl -> plan_item v cl
  | PIReenter: hs:handlers cl -> ret:option (v -> pcomp v cl) -> plan_item v cl

(**
 * **The scope plan.**
 *
 * `layers` is a SINGLE LIST IN THE CAPTURED ORDER, innermost first -- the same
 * order, frame for frame, that the intervening segment had. Plan construction
 * below is a rewrite and never a reordering, exactly as
 * `Hoop.Runtime.Semantics.borrow` is, and every claim about composition order
 * rests on that. It is not even a FILTER: every frame of the captured segment
 * becomes exactly one item, so the correspondence is positional, and what used
 * to be `borrow`'s dropping of a bind frame is now a decision taken by the
 * projections instead -- `plan_enter_frames` versus `plan_resume_frames`.
 *
 * *Why one list rather than, say, a list of family layers beside a list of
 * borrowed frames.* Nesting order would then be RECONSTRUCTIBLE -- from
 * positions, or from an index kept alongside -- rather than MANIFEST. Two lists
 * can be zipped back in the wrong order by a function that typechecks, and the
 * composition order of two handlers is observable (a `ParamF` holds its value by
 * value, so a captured continuation carries its own copy; see
 * `Hoop.Runtime.Syntax.ParamF`). With one list, "the plan preserves nesting
 * order" is not a lemma about a pairing: the frames come back out by mapping the
 * list, in place, and a rule that reordered them could not be written without
 * naming `rev` or `sort`.
 *
 * The owner is a field of its own, for the reason recorded at `powner`.
 *)
and plan (v: Type u#a) (cl: Type u#a) : Type u#a =
  | Plan:
      layers:list (plan_item v cl) ->
      owner:powner v cl ->
      plan v cl

(**
 * **A context value.**
 *
 * `C x` of the design note, at F*'s single value type: the SUSPENDED INNER
 * COMPUTATION whose leaf values the context holds. It is not a `v`, and that is
 * deliberate -- a machine-side datum the surface receives as an opaque token,
 * which is what the design's stop condition "the FFI passing anything but a
 * context plan or an opaque context value" already anticipates.
 *
 * **Why a suspension and not the value the layers produced.** The alternative is
 * to let a context be the layer's own answer -- `Array x` for a nondeterministic
 * layer -- and it is unimplementable at this level: the machine cannot take
 * `Array x` apart, so it could not run a continuation at each value the context
 * holds, and nothing short of a per-layer distributive law (`f (m x) -> n (f x)`,
 * which is evidence about a handler's BEHAVIOUR, not about its provenance) would
 * give it one. Keeping the inner computation is what lets the three operations
 * below be defined from provenance alone.
 *
 * **What it costs, stated plainly because B2 must not discover it.** Re-entering
 * a context RE-RUNS the inner computation. A clause that observes a context and
 * then resumes it -- which is precisely what `catch` does, `runScope try`
 * followed by `resumeScope cx k` -- runs `try` twice. The design note already
 * records the same effect from the other side ("two `bindScope` calls on the same
 * context re-enter the intervening context twice, which for a nondeterministic
 * `ctx` duplicates branches"), so replay is not a surprise here; what is new is
 * that it applies to observe-then-resume as well, and that the B3 obligation "a
 * transparent plan is observationally equal to the existing borrow" is therefore
 * NOT free -- at a transparent plan the shipped machine hands the value to the
 * continuation and re-runs nothing. See the note on `resume_C`.
 *
 * A context does NOT carry the plan it belongs to. The plan is what the machine
 * holds at the transition, and a context carrying its own copy would be a second
 * plan that can disagree with it. The operations take both.
 *)
and pctx (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PCtx: pending:pcomp v cl -> pctx v cl

(* ------------------------------------------------------------------ *)
(*  The classification, derived                                        *)
(* ------------------------------------------------------------------ *)

(**
 * **The classifier.** Provenance is carried; the class is computed.
 *
 * **The priority is fixed and load-bearing, and the match makes it
 * syntactically evident**: `PFamily` is answered before anything about `ret` or
 * the table is even looked at. A family prompt that HAPPENS to be all-fast with
 * `ret = None` is still `Family`. Dropping such a prompt to the transparent path
 * is an OPTIMISATION -- it must be justified by an observational-equivalence
 * proof, which is B3's job -- and never a default. Written as
 * `if transparent then ... else if family then ...` the two would silently swap,
 * and nothing in the file would say which had been intended.
 *
 * The `PMono` arm reads the REAL frame data: the actual `ret` field, and
 * `blocking_effects` of the actual table (which judges only the entries that
 * would really be dispatched, since it is stated through `lookup_handler`).
 * Nothing here consults a flag.
 *)
let classify_prompt
    (#v #cl: Type)
    (prov: prompt_provenance)
    (hs: handlers cl)
    (ret: option (v -> pcomp v cl))
  : prompt_class
  = match prov with
    | PFamily -> Family
    | PMono ->
      match ret with
      | Some _ -> Monomorphic
      | None -> if borrowable hs then ContextTransparent else Monomorphic

(* ------------------------------------------------------------------ *)
(*  Building the plan                                                  *)
(* ------------------------------------------------------------------ *)

(**
 * **Why plan construction can fail**, and what the failure carries.
 *
 * The caller turns this into the existing
 * `Hoop.Runtime.Semantics.UnborrowableScope eff op blocking`, so the payload is
 * the payload that rejection already takes: the effect labels responsible.
 *
 * **A gap worth recording rather than papering over.** A prompt that is
 * `Monomorphic` because it has a RETURN CLAUSE -- all-fast table, non-identity
 * `pure` -- has no blocking clause to name, so `blocking_effects` of its table is
 * `[]` and the list below is empty. The actionable thing to report would be the
 * effect labels that prompt HANDLES, and they cannot be computed: the table's
 * entries are behind `Hoop.Runtime.Handlers.table`, which is `GTot`, and its
 * `keys` are a `keyset` that answers membership but does not enumerate. Naming
 * the offending handler in that case therefore needs a `Tot` projection the
 * table interface does not offer today. Left as it is, because inventing one
 * here would be editing `Hoop.Runtime.*` for a prototype's sake.
 *)
type plan_failure =
  | MonomorphicLayer: blocking:list string -> plan_failure

(**
 * **The intervening segment, classified.**
 *
 * Three decisions:
 *
 *   - `PBindF` is RECORDED, in place. Whether it is reinstalled is decided by the
 *     PROJECTION and not here -- see `PIBind`, where the reason the plan cannot
 *     simply drop it is set out.
 *
 *   - `PParamF` is KEPT ENTIRE, label and value, exactly as in `borrow`.
 *
 *   - A prompt is CLASSIFIED, and each class becomes its own plan item.
 *
 * **This function is a total walk that either refuses or rewrites frame for
 * frame.** It never inspects a table for anything but its blocking effects, and
 * it never looks past the frame it is on -- so the plan it builds is the
 * captured segment with each frame replaced by one item, and the correspondence
 * is positional. That is what "nesting order is manifest" means here.
 *
 * **The innermost blocker wins**, as in `Hoop.Runtime.Semantics.scope_blockers`:
 * the recursion refuses at the first `Monomorphic` prompt it meets, which is the
 * one nearest the perform site and so the one whose handler stack the user can
 * act on.
 *
 * Order is preserved: every kept frame is consed in the position it was found.
 *)
let rec plan_layers (#v #cl: Type) (ints: list (pframe v cl))
  : Tot (either plan_failure (list (plan_item v cl))) (decreases ints)
  = match ints with
    | [] -> Inr []
    | PBindF fn :: rest ->
      (match plan_layers rest with
        | Inl e -> Inl e
        | Inr ls -> Inr (PIBind fn :: ls))
    | PParamF l x :: rest ->
      (match plan_layers rest with
        | Inl e -> Inl e
        | Inr ls -> Inr (PICell l x :: ls))
    | PPromptF hs ret prov :: rest ->
      (match classify_prompt prov hs ret with
        | Monomorphic -> Inl (MonomorphicLayer (blocking_effects hs))
        | ContextTransparent ->
          (match plan_layers rest with
            | Inl e -> Inl e
            | Inr ls -> Inr (PITransparent hs :: ls))
        | Family ->
          (match plan_layers rest with
            | Inl e -> Inl e
            | Inr ls -> Inr (PIReenter hs ret :: ls)))

(** **The plan**: the classified intervening segment, and the owner beside it,
    unclassified and unborrowed. *)
let plan_of (#v #cl: Type) (ints: list (pframe v cl)) (own: powner v cl)
  : either plan_failure (plan v cl)
  = match plan_layers ints with
    | Inl e -> Inl e
    | Inr ls -> Inr (Plan ls own)

(* ------------------------------------------------------------------ *)
(*  Reading the plan back out as frames                                *)
(* ------------------------------------------------------------------ *)

(** **The owner, as the frame it was.** Table, return clause and provenance all
    survive the round trip; nothing about the owner is rewritten. *)
let owner_frame (#v #cl: Type) (own: powner v cl) : pframe v cl
  = PPromptF (POwner?.hs own) (POwner?.ret own) (POwner?.prov own)

(**
 * **The layers, as the frames a SCOPE runs under.** The plan's order, which is
 * the captured order.
 *
 * A `PIBind` contributes NOTHING: a scope is not a resumption, so the perform
 * site's continuation is not reinstalled around the inner computation. This is
 * `borrow`'s first clause, unchanged in effect and moved from plan construction
 * to this projection.
 *
 * A transparent item comes back as `PPromptF hs None PMono`, which is the
 * borrowed frame today's `borrow` produces; since a transparent prompt had no
 * return clause to begin with, this rewrites nothing, and the equality with
 * `borrow` at an all-transparent plan is B3's obligation.
 *
 * A family item comes back **table, return clause and `PFamily` all intact**.
 * Keeping the provenance is not bookkeeping: a scope opened INSIDE this one
 * meets this prompt as an intervening prompt and has to classify it, from the
 * same evidence, to the same class. Reinstalling it as `PMono` would silently
 * demote a family layer to `Monomorphic` one nesting level in.
 *)
let rec enter_layer_frames (#v #cl: Type) (ls: list (plan_item v cl))
  : Tot (list (pframe v cl)) (decreases ls)
  = match ls with
    | [] -> []
    | PIBind _ :: rest -> enter_layer_frames rest
    | PICell l x :: rest -> PParamF l x :: enter_layer_frames rest
    | PITransparent hs :: rest -> PPromptF hs None PMono :: enter_layer_frames rest
    | PIReenter hs ret :: rest -> PPromptF hs ret PFamily :: enter_layer_frames rest

(**
 * **The layers, as the frames a RESUMPTION returns through.** The same walk, and
 * the same order, with the bind frames put back where they stood.
 *
 * The two projections differ in ONE clause, which is the whole of the difference
 * between entering a scope and resuming a perform site, and it is visible as one
 * line rather than as two lists built by two functions that must be kept in
 * step. In the shipped machine the same distinction is `prepared` versus
 * `captured` -- `weave_of` uses one and `kont_of` the other, and the design note
 * observes that "two different lists ... is what makes 'not inside, exactly once
 * outside' come out".
 *)
let rec resume_layer_frames (#v #cl: Type) (ls: list (plan_item v cl))
  : Tot (list (pframe v cl)) (decreases ls)
  = match ls with
    | [] -> []
    | PIBind fn :: rest -> PBindF fn :: resume_layer_frames rest
    | PICell l x :: rest -> PParamF l x :: resume_layer_frames rest
    | PITransparent hs :: rest -> PPromptF hs None PMono :: resume_layer_frames rest
    | PIReenter hs ret :: rest -> PPromptF hs ret PFamily :: resume_layer_frames rest

(**
 * **The segment a scope runs under**: the layers, innermost first, and the owner
 * last.
 *
 * Head = innermost, so a value leaving the scope meets the layers in the order
 * it met them originally and meets the owner LAST -- the answer transformation
 * is applied exactly once, and after every layer's. That is what makes the woven
 * result `f (ctx x)` and not `ctx (f x)`.
 *
 * `@` is used, and would not be on a shipped path (see
 * `Hoop.Runtime.Semantics.prepare_scope_fast` on why the shipped preparation is
 * an accumulating walk with one `rev`). B1 is a prototype and is never
 * extracted; writing the specification twice here would buy nothing and cost the
 * clarity the whole file is for.
 *)
let plan_enter_frames (#v #cl: Type) (pl: plan v cl) : list (pframe v cl)
  = enter_layer_frames (Plan?.layers pl) @ [owner_frame (Plan?.owner pl)]

(**
 * **The segment a resumption returns through**: the same, with the perform
 * site's continuation back in place.
 *
 * The owner is in it, and must be: a resumed value has to meet the owner's
 * return clause on its way out, which is what puts it at the answer type the
 * clause's result is spliced in at. It is the last frame here for the same
 * reason it is the last frame there.
 *
 * **This is `Hoop.Runtime.Semantics.kont_of`'s captured segment.** At a plan
 * built by `plan_of` from a real captured segment it is that segment, frame for
 * frame -- transparent prompts had no return clause to lose, family prompts keep
 * theirs, cells and binds are untouched -- so `law_resume_matches_continuation`
 * below is a statement about the machine that ships and not only about this one.
 * Proving that identity is B2's; it is a straightforward induction, and it is
 * left with the laws rather than snuck in here, because a prototype that proves
 * one convenient lemma and states the rest is a prototype whose author chose
 * which obligations to look at.
 *)
let plan_resume_frames (#v #cl: Type) (pl: plan v cl) : list (pframe v cl)
  = resume_layer_frames (Plan?.layers pl) @ [owner_frame (Plan?.owner pl)]

(* ------------------------------------------------------------------ *)
(*  The three context operations                                       *)
(*                                                                     *)
(*  The reference MEANING of the three scope tactics. Gate A            *)
(*  established that their types do not force these implementations --  *)
(*  a `runScope` that injects each value into a singleton typechecks     *)
(*  and is wrong -- which is exactly why they are defined here, in a    *)
(*  machine with a reference semantics, rather than on the PureScript   *)
(*  side. The surface's job is to delegate; nothing that can be wrong    *)
(*  should be written there.                                            *)
(* ------------------------------------------------------------------ *)

(** **The inner monad's bind**, named so that the laws below and the operations
    speak of one SMT symbol rather than of an `POp` a reader has to recognise.
    This is `Hoop.Runtime.Syntax.Op` under the prototype's name. *)
unfold
let pbind (#v #cl: Type) (c: pcomp v cl) (f: v -> pcomp v cl) : pcomp v cl
  = POp c f

(**
 * **Entering a scope**: run the inner computation under the plan.
 *
 * Every layer is re-entered -- a transparent one as the borrowed frame it
 * becomes, a family one as itself -- and the owner is re-installed entire, so
 * the value this produces is `f (ctx x)`: the owner's answer former applied to
 * whatever the layers made of `x`.
 *
 * It re-enters the layers; it does NOT inject a value into a context, because
 * there is no value yet to inject. The wrong implementation Gate A's condition 6
 * exhibits is the one that runs the body under the owner alone and treats the
 * result as a one-value context, and it is the anchored half of `law_assoc`, and
 * `law_resume_matches_continuation`, that separate the two -- see `flat_ops`.
 *
 * The ENTER projection is used, so the perform site's continuation is not
 * reinstalled: the scope runs instead of the rest of the enclosing block.
 *)
let enter_C (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) : pcomp v cl
  = PSplice (plan_enter_frames pl) c

(** **The context that entering produces**: the inner computation itself. The
    machine keeps the suspension; the surface receives an opaque token. *)
let enter_ctx_C (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) : pctx v cl
  = PCtx c

(**
 * **Extending a context**: continue, at each value the context holds, with an
 * INNER computation.
 *
 * The layers are re-entered and the continuation is appended at the leaves, so
 * the layer's own algebra -- its clauses, its return clause -- is what rebuilds
 * the context around the results. Nothing decomposes a context; nothing injects
 * into one. This is `bindScope`, whose function argument is `x -> Hoop inner y`,
 * over the VALUE rather than over `ctx x`: the clause never sees inside, and the
 * machine is what re-enters the intervening prompts and applies the function
 * there.
 *
 * **The ENTER projection, like `enter_C` and unlike `resume_C`.** An extension
 * stays inside the scope -- its answer is another `f (ctx y)`, to be extended or
 * resumed again -- so the perform site's continuation must not be reinstalled
 * around it. That is the whole difference between this and `resume_C`, and it is
 * one function call wide.
 *)
let extend_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: v -> pcomp v cl)
  : pcomp v cl
  = PSplice (plan_enter_frames pl) (pbind (PCtx?.pending cx) g)

(** **The context extending produces.** The suspension, extended -- which is why
    `law_assoc` below is a statement the representation can even make: the two
    sides of associativity are two bracketings of the same `pbind` chain. *)
let extend_ctx_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: v -> pcomp v cl)
  : pctx v cl
  = PCtx (pbind (PCtx?.pending cx) g)

(**
 * **Resuming a context onto the continuation** -- the important one.
 *
 * **It is NOT "hand the context value to the continuation".** It is: re-enter
 * the saved family prompts, run the continuation at each value the context
 * holds, and let each handler's own algebra rebuild the context. The plan is
 * read in the very first thing it does; **an implementation of `resume_C` that
 * could be written without touching the plan is wrong**, and the one Gate A
 * exhibits --
 *
 * ```purescript
 * resumeScopeAtArray _weave = \cx k -> case Array.head cx of
 *   Just x -> continue k x
 *   Nothing -> ?noValueToReturn
 * ```
 *
 * -- is exactly that: it ignores the `_weave`, takes one value out of the
 * context, and has nothing to return when the context holds none. Here the
 * context is never taken apart and the "none" case does not arise: a layer that
 * produced no leaves runs the continuation nowhere, and its own algebra says
 * what that means.
 *
 * **What separates it from `extend_C`**, since at the machine level the two
 * would otherwise be one function -- types are erased here, and `bindScope`'s
 * `x -> Hoop inner y` and `resumeScope`'s `Cont x r o` are the same arrow. The
 * difference is the PROJECTION: a resumption returns to the perform site, so the
 * bind frames the plan recorded are put back, in their original interleaving
 * with the prompts. An extension does not, and does not get them.
 *
 * That difference is what makes the two operations two, and it is worth noting
 * that it was NOT visible until the plan was asked to serve both roles: a
 * representation that had dropped the bind frames at construction, as
 * `Hoop.Runtime.Semantics.borrow` does, would have made `resume_C` and
 * `extend_C` literally the same definition and nothing in the file would have
 * said which of them was wrong.
 *)
let resume_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (k: v -> pcomp v cl)
  : pcomp v cl
  = PSplice (plan_resume_frames pl) (pbind (PCtx?.pending cx) k)

(* ------------------------------------------------------------------ *)
(*  The operations as data                                             *)
(*                                                                     *)
(*  The laws are stated over this record rather than over the three     *)
(*  definitions above, and that is what gives them their discriminating *)
(*  power: a law over a fixed implementation is a proposition about one  *)
(*  program, while a law over the record is a proposition an ALTERNATIVE *)
(*  implementation can be plugged into and fail. Two wrong ones are      *)
(*  supplied below for exactly that purpose.                            *)
(* ------------------------------------------------------------------ *)

noeq
type ctx_ops (v: Type) (cl: Type) = {
  o_enter: plan v cl -> pcomp v cl -> pcomp v cl;
  o_enter_ctx: plan v cl -> pcomp v cl -> pctx v cl;
  o_extend: plan v cl -> pctx v cl -> (v -> pcomp v cl) -> pcomp v cl;
  o_extend_ctx: plan v cl -> pctx v cl -> (v -> pcomp v cl) -> pctx v cl;
  o_resume: plan v cl -> pctx v cl -> (v -> pcomp v cl) -> pcomp v cl;
}

(** **The reference semantics**, as data. *)
let ref_ops (#v #cl: Type) : ctx_ops v cl = {
  o_enter = enter_C;
  o_enter_ctx = enter_ctx_C;
  o_extend = extend_C;
  o_extend_ctx = extend_ctx_C;
  o_resume = resume_C;
}

(**
 * **Wrong implementation 1: the plan is ignored.** Every operation runs under
 * the owner alone, so the intervening layers are never re-entered and every
 * context behaves as though it held exactly one value -- the machine-level
 * rendering of `weave (map (\x -> [x]) body)`.
 *
 * It typechecks, which is the point: nothing in the SIGNATURES rules it out.
 *
 * **And nothing PURELY ALGEBRAIC rules it out either, which is worth more than
 * the counterexample.** This algebra is wrong UNIFORMLY -- it ignores the plan
 * in all five fields at once -- so it satisfies every equation that relates its
 * own operations to each other: left identity, right identity and the algebraic
 * half of associativity all hold of it, because both sides of each are equally
 * plan-free. An algebra can be internally coherent and mean nothing.
 *
 * What catches it is a law with an INDEPENDENT right-hand side, one written in
 * terms of the plan rather than in terms of the operations:
 * `law_resume_matches_continuation`, and the anchored half of `law_assoc`. That
 * is why exactly those two are anchored and the other two are left purely
 * algebraic -- anchoring all four would collapse "these are the laws" into
 * "`ops == ref_ops`", which no alternative implementation could ever satisfy and
 * which would therefore constrain nothing that mattered.
 *)
let flat_ops (#v #cl: Type) : ctx_ops v cl =
  let owner_only (pl: plan v cl) : list (pframe v cl) = [owner_frame (Plan?.owner pl)] in
  {
    o_enter = (fun pl c -> PSplice (owner_only pl) c);
    o_enter_ctx = (fun _ c -> PCtx c);
    o_extend = (fun pl cx g -> PSplice (owner_only pl) (pbind (PCtx?.pending cx) g));
    o_extend_ctx = (fun _ cx g -> PCtx (pbind (PCtx?.pending cx) g));
    o_resume = (fun pl cx k -> PSplice (owner_only pl) (pbind (PCtx?.pending cx) k));
  }

(**
 * **Wrong implementation 2: the layers are re-entered per value.** Each leaf
 * gets a FRESH context instead of sharing the one the layers have already
 * established. This is the OTHER reading of the same counterexample `flat_ops`
 * renders: "inject each value into a singleton" says both that a context is not
 * re-entered (`flat_ops`) and that each value gets a context of its own, which
 * is this.
 *
 * It typechecks too, and unlike `flat_ops` it is refused by every one of the
 * four laws, `law_assoc`'s algebraic half included: the two bracketings of an
 * extension differ by where the layers' return clauses fall, so the second
 * function receives a rebuilt context where it should have received a value.
 *)
let pointwise_ops (#v #cl: Type) : ctx_ops v cl = {
  o_enter = enter_C;
  o_enter_ctx = enter_ctx_C;
  o_extend =
    (fun pl cx g -> PSplice (plan_enter_frames pl)
                     (pbind (PCtx?.pending cx) (fun x -> PSplice (plan_enter_frames pl) (g x))));
  o_extend_ctx =
    (fun pl cx g -> PCtx (pbind (PCtx?.pending cx)
                                (fun x -> PSplice (plan_enter_frames pl) (g x))));
  o_resume =
    (fun pl cx k -> PSplice (plan_resume_frames pl)
                     (pbind (PCtx?.pending cx) (fun x -> PSplice (plan_resume_frames pl) (k x))));
}

(* ------------------------------------------------------------------ *)
(*  The machine                                                        *)
(* ------------------------------------------------------------------ *)

type pstack (v: Type) (cl: Type) = list (pframe v cl)

(** The clause interpreter, monomorphized to the prototype's AST. The prototype
    has no scoped dispatch (see the module header), so there is one interpreter
    and not two. *)
let papply_t (v cl: Type) = cl -> list v -> (v -> pcomp v cl) -> pcomp v cl

noeq
type pstate (v: Type) (cl: Type) =
  | PDone: value:v -> pstate v cl
  | PStep: c:pcomp v cl -> k:pstack v cl -> pstate v cl
  | PStuck: eff:string -> op:string -> pstate v cl
  // The SHIPPED rejection type. It is flat and independent of `v` and `cl`, so
  // there is nothing to translate: a plan refused here is refused with the very
  // constructor `Hoop.Runtime.Semantics.step` produces, which is what makes
  // "the caller can produce the existing `UnborrowableScope` rejection" a fact
  // about a type rather than a resemblance between two enumerations.
  | PRejected: rejection -> pstate v cl

(** The prompt holding the handler for this action, and the stack split there:
    `(captured, found, below)`, captured including the prompt. The shipped
    `find_prompt` carries a refinement tying it to `handled_in`; this one does
    not, because nothing in B1 proves progress and a refinement nobody spends is
    a refinement that has to be maintained. *)
let rec pfind_prompt (#v #cl: Type) (eff op: string) (k: pstack v cl)
  : Tot (option (pstack v cl & found_clause cl & pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | PPromptF hs ret prov :: rest ->
      (match lookup_handler hs eff op with
        | Some c -> Some ([PPromptF hs ret prov], c, rest)
        | None ->
          (match pfind_prompt eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PPromptF hs ret prov :: cap, c, below)))
    | f :: rest ->
      (match pfind_prompt eff op rest with
        | None -> None
        | Some (cap, c, below) -> Some (f :: cap, c, below))

(** `read`: the contents of the nearest cell with this label. *)
let rec pfind_param (#v #cl: Type) (l: string) (k: pstack v cl)
  : Tot (option v) (decreases k)
  = match k with
    | [] -> None
    | PParamF l' x :: rest -> if l' = l then Some x else pfind_param l rest
    | _ :: rest -> pfind_param l rest

(** `write`: the stack with the nearest such cell set. Frames above it are
    rebuilt, frames below are shared -- there is no mutable cell and no
    identity, so a captured continuation keeps the value it was captured with. *)
let rec pset_param (#v #cl: Type) (l: string) (x: v) (k: pstack v cl)
  : Tot (option (pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | PParamF l' y :: rest ->
      if l' = l then Some (PParamF l x :: rest)
      else (match pset_param l x rest with
            | None -> None
            | Some rest' -> Some (PParamF l' y :: rest'))
    | f :: rest ->
      (match pset_param l x rest with
        | None -> None
        | Some rest' -> Some (f :: rest'))

(** The delimited continuation handed to a clause, named for the reason
    `Hoop.Runtime.Semantics.kont_of` is named: a top-level symbol, so that facts
    about it are facts about one function rather than about whatever lambda a
    transition happened to build. *)
let pkont_of (#v #cl: Type) (captured: pstack v cl) (x: v) : pcomp v cl
  = PSplice captured (PVar x)

(**
 * **The small-step semantics.**
 *
 * Written PLAINLY. The transparent case is part of the general path here: a
 * transparent layer is re-entered like any other, as a frame contributing no
 * context. Turning it into a fast path -- and proving the two agree -- is B3,
 * and doing it here would mean the reference semantics and the optimisation were
 * never two things that could be compared.
 *
 * The three context operations get one rule each, and each rule is a single
 * appeal to the operation. That is deliberate: a transition that inlined
 * `plan_enter_frames` would be a second definition of what a tactic MEANS, and the
 * whole point of B1 is that there is exactly one.
 *)
let pstep (#v #cl: Type) (apply: papply_t v cl) (s: pstate v cl)
  : Tot (pstate v cl)
  = match s with
    | PDone _ -> s
    | PStuck _ _ -> s
    | PRejected _ -> s
    | PStep c k ->
      match c with
      | POp comp fn -> PStep comp (PBindF fn :: k)
      | PHandle hs ret prov body -> PStep body (PPromptF hs ret prov :: k)
      | PPerform eff op payload ->
        (match pfind_prompt eff op k with
          | None -> PStuck eff op
          | Some (captured, found, below) ->
            (match found.kind with
              | KScoped -> PRejected (ClauseKindMismatch eff op KOrdinaryOperation KScoped)
              | _ -> PStep (apply found.body payload (pkont_of captured)) below))
      // **Entering a scope**: build the plan, then run the body under it. The
      // plan is what can fail, and it fails into the rejection the shipped
      // machine already produces -- the origin naming the scope, the labels
      // naming what stood in its way.
      | PWeave oeff oop ints own body ->
        (match plan_of ints own with
          | Inl (MonomorphicLayer bs) -> PRejected (UnborrowableScope oeff oop bs)
          | Inr pl -> PStep (enter_C pl body) k)
      | PExtendC pl cx g -> PStep (extend_C pl cx g) k
      | PResumeC pl cx kk -> PStep (resume_C pl cx kk) k
      | PVar value ->
        (match k with
          | [] -> PDone value
          | PBindF fn :: rest -> PStep (fn value) rest
          | PParamF _ _ :: rest -> PStep (PVar value) rest
          | PPromptF _ ret _ :: rest ->
            (match ret with
              | Some fn -> PStep (fn value) rest
              | None -> PStep (PVar value) rest))
      | PSplice fs body -> PStep body (fs @ k)
      | PNewP l init body -> PStep body (PParamF l init :: k)
      | PReadP l ->
        (match pfind_param l k with
          | None -> PStuck var_eff l
          | Some x -> PStep (PVar x) k)
      | PWriteP l x ->
        (match pset_param l x k with
          | None -> PStuck var_eff l
          | Some k' -> PStep (PVar x) k')

(** The iteration of `pstep`, cut off at `fuel` transitions -- the shape of
    `Hoop.Runtime.Semantics.steps`, so that the laws below can be stated in the
    same idiom the shipped monad laws are stated in. *)
let rec psteps (#v #cl: Type) (apply: papply_t v cl) (fuel: nat) (s: pstate v cl)
  : Tot (pstate v cl) (decreases fuel)
  = if fuel = 0 then s
    else
      match s with
      | PDone _ -> s
      | PStuck _ _ -> s
      | PRejected _ -> s
      | PStep _ _ -> psteps apply (fuel - 1) (pstep apply s)

(** **Loading a program.** *)
let pload (#v #cl: Type) (c: pcomp v cl) : pstate v cl = PStep c []

(* ------------------------------------------------------------------ *)
(*  Observation                                                        *)
(*                                                                     *)
(*  The same notion `Hoop.Runtime.Laws` uses, at the prototype's AST:   *)
(*  plugged into any continuation, the two computations converge to the *)
(*  same value. The quantification over the stack is the whole point --  *)
(*  a stack is where handlers live, so ranging over every `k` is        *)
(*  ranging over every handler context, INCLUDING the ones a plan       *)
(*  re-enters.                                                          *)
(* ------------------------------------------------------------------ *)

let pconverges (#v #cl: Type) (apply: papply_t v cl) (s: pstate v cl) (x: v) : GTot prop =
  exists (n: nat). psteps apply n s == PDone x

let pobs_le (#v #cl: Type) (apply: papply_t v cl) (c1 c2: pcomp v cl) : GTot prop =
  forall (k: pstack v cl) (x: v).
    pconverges apply (PStep c1 k) x ==> pconverges apply (PStep c2 k) x

let pobs_eq (#v #cl: Type) (apply: papply_t v cl) (c1 c2: pcomp v cl) : GTot prop =
  pobs_le apply c1 c2 /\ pobs_le apply c2 c1

(* ------------------------------------------------------------------ *)
(*  The laws -- DEFINED, not proved                                    *)
(*                                                                     *)
(*  Each is a DEFINITION whose type is `prop`. None is a `val` without  *)
(*  a proof, none is assumed, and NOTHING IN THIS MODULE DEPENDS ON ANY *)
(*  OF THEM HOLDING: no operation, no transition and no other           *)
(*  definition mentions them. Proving them is B2's job. B1's job is to  *)
(*  make them STATABLE, which is itself the check that the              *)
(*  representation is right -- a representation that cannot express     *)
(*  associativity has already failed, and one that can express it only  *)
(*  of a fixed implementation cannot be used to rule a wrong one out.   *)
(*                                                                     *)
(*  They are stated over `ctx_ops`, so `law_X ops ...` is a proposition *)
(*  about an implementation. The intended readings are                  *)
(*                                                                     *)
(*    law_X apply ref_ops ...          -- B2 proves these               *)
(*    ~(law_X apply pointwise_ops ...) -- refused by all four           *)
(*    ~(law_X apply flat_ops ...)      -- refused by the two ANCHORED   *)
(*                                       laws only: `law_assoc`'s       *)
(*                                       second conjunct and            *)
(*                                       `law_resume_matches_continuation` *)
(*                                                                     *)
(*  That asymmetry is a finding and not an oversight; the note on       *)
(*  `flat_ops` records it. A purely algebraic law cannot see an algebra *)
(*  that is wrong uniformly, so at least one law must have a right-hand *)
(*  side written in terms of the PLAN rather than in terms of the       *)
(*  operations -- and not all four may, or the laws would say no more   *)
(*  than `ops == ref_ops`.                                             *)
(*                                                                     *)
(*  Two further laws belong to B3 and are deliberately NOT stated here, *)
(*  because both need the optimized machine that does not exist yet:    *)
(*  plan composition matching handler nesting, and a transparent plan   *)
(*  being observationally equal to the existing                          *)
(*  `Hoop.Runtime.Semantics.borrow`. The second is the one that ties    *)
(*  the classification back to what ships, and the note on `pctx` says  *)
(*  why it will not come for free.                                      *)
(* ------------------------------------------------------------------ *)

(**
 * **Left identity, at a point.** A context holding just the value `x`, extended
 * by `g`, is entering `g x`.
 *
 * **What it rules out is a second re-entry.** Under `pointwise_ops` the
 * left-hand side enters the plan twice -- once for the context, once more around
 * `g x` -- while the right-hand side enters it once, and for a layer that
 * transforms its answer those differ observably. A point is exactly where that
 * shows up most sharply: there is one value, so any difference between the two
 * sides is a difference in how many times the layers were crossed.
 *
 * It is PURELY ALGEBRAIC -- both sides are built from `ops` alone -- and so it
 * does NOT rule out `flat_ops`, which ignores the plan on both sides equally.
 * That separation is deliberate; see the note on `flat_ops` for why not every
 * law should be anchored.
 *)
let law_left_identity
    (#v #cl: Type)
    (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: v)
    (g: v -> pcomp v cl)
  : GTot prop
  = pobs_eq apply
      (ops.o_extend pl (ops.o_enter_ctx pl (PVar x)) g)
      (ops.o_enter pl (g x))

(**
 * **Right identity.** Extending by the inner monad's `pure` changes nothing: the
 * layers are re-entered exactly as entering would have re-entered them, and no
 * layer is crossed a second time on the way.
 *
 * Stated of a context REACHED FROM THE PLAN -- `o_enter_ctx pl c` -- rather than
 * of an arbitrary one, so that the statement stays independent of what a `pctx`
 * is made of. An implementation free to choose its own context representation is
 * still bound by this.
 *)
let law_right_identity
    (#v #cl: Type)
    (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pobs_eq apply
      (ops.o_extend pl (ops.o_enter_ctx pl c) (PVar #v #cl))
      (ops.o_enter pl c)

(**
 * **Associativity of extension.** Two conjuncts, and the second is there because
 * the first was checked against the counterexample and found insufficient.
 *
 * *The algebraic half* quantifies over an ARBITRARY context and compares the
 * CONTEXT PRODUCED by the first extension (`o_extend_ctx`) against the composite
 * function -- not two computations that happen to be built the same way. It is
 * what refuses `pointwise_ops`, the implementation that gives each leaf a fresh
 * context instead of sharing the one the layers have already established: its
 * left-hand side re-enters the layers around `g`'s results and then again around
 * `h`'s, so `h` is applied to values that have already been through the layers'
 * return clauses, while its right-hand side applies `h` to `g`'s values inside a
 * single re-entry. For a nondeterministic layer those are `f (f y)` and `f y` --
 * different branch structure, observably. This is also why `o_extend_ctx` is a
 * field of `ctx_ops` at all: an implementation cannot even state the law without
 * saying what context its extension produced.
 *
 * *The anchored half* was forced by the sanity check the design asks for. An
 * operation that injects a value into a singleton context instead of re-entering
 * the layer is, at the machine level, one that never enters the layers at all --
 * `flat_ops` -- and **the algebraic half alone does NOT rule that out**, because
 * a uniformly plan-free algebra satisfies every equation between its own
 * operations. The statement was therefore strengthened rather than left as it
 * was: one side is pinned to an INDEPENDENT description of what associativity is
 * associativity OF -- the plan's frames, in nesting order, entered EXACTLY ONCE,
 * around the composite inner computation. `flat_ops` fails it at the first plan
 * with a layer; `pointwise_ops` fails it by entering more than once.
 *
 * The anchor is stated at a context reached from the plan, since that is the
 * only shape in which the composite inner computation can be named without
 * asking what a `pctx` is made of. Every context is reached from the plan by
 * `o_enter_ctx` and `o_extend_ctx`, so nothing escapes through the gap between
 * the two halves.
 *)
let law_assoc
    (#v #cl: Type)
    (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (cx: pctx v cl)
    (c: pcomp v cl)
    (g h: v -> pcomp v cl)
  : GTot prop
  = // the algebraic half -- any context, both sides built from `ops` alone
    pobs_eq apply
      (ops.o_extend pl (ops.o_extend_ctx pl cx g) h)
      (ops.o_extend pl cx (fun x -> pbind (g x) h))
    /\ // the anchored half -- one re-entry of THIS plan, and no other
    pobs_eq apply
      (ops.o_extend pl (ops.o_extend_ctx pl (ops.o_enter_ctx pl c) g) h)
      (PSplice (plan_enter_frames pl) (pbind (pbind c g) h))

(**
 * **Resume agrees with the preserved continuation.**
 *
 * At a context holding exactly one value, resuming IS the shipped resumption:
 * push the plan's segment back and hand the value to the continuation, which is
 * `Hoop.Runtime.Semantics.kont_of` at the prototype's AST. This is the law that
 * ties the general operation to the machine that ships -- everything the shipped
 * machine does today is the one-value case of it -- and it is the reason
 * `resume_C` may not be an application: an implementation that handed the
 * context to the continuation would satisfy nothing here, since there is no
 * segment in it to push.
 *
 * The right-hand side is written with `plan_resume_frames` rather than with the
 * operations, on purpose: it is an INDEPENDENT description of what resumption
 * means, so the law relates the algebra to the machine instead of relating the
 * algebra to itself.
 *)
let law_resume_matches_continuation
    (#v #cl: Type)
    (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: v)
    (k: v -> pcomp v cl)
  : GTot prop
  = pobs_eq apply
      (ops.o_resume pl (ops.o_enter_ctx pl (PVar x)) k)
      (PSplice (plan_resume_frames pl) (k x))
