(**
 * **B1.5 -- the general weave, over a RESIDUAL CONFIGURATION.**
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
 * *What B1.5 changed, and why B1 was withdrawn.* B1 made a context a
 * SUSPENSION -- `PCtx (pending: pcomp v cl)`, the inner computation, not yet
 * run. Every operation over it re-ran `pending`, so re-entering a context
 * REPLAYED the protected computation: a clause that produces a context and then
 * consumes it twice -- `runScope try` and then `resumeScope cx k`, which is what
 * `catch` is -- ran `try` once per consumption. B1 documented the cost honestly
 * and it was judged fatal. The full withdrawal note, including the part of B1's
 * reasoning that is still true, is at `pctx` below.
 *
 * What replaces it is a RESIDUAL MACHINE CONFIGURATION and an interaction
 * protocol. `PCtxRequests x residual post` says: the scope's inner computation
 * reached the scope boundary carrying `x`, and the layer and owner handlers
 * around it have not been given anything to continue with. Hand them a real
 * answer and they continue *from exactly there*; the prefix is not re-run. If
 * they resume their own continuations, the inner computation runs on and may
 * reach the boundary again, asking again. If they finish, the protocol ends in
 * `PCtxDone`. It is a coroutine -- an interaction whose next shape is decided by
 * the answer it receives -- and not a precomputed tree of leaves. (A precomputed
 * leaf list was the other candidate and was rejected before B1.5 started: it
 * cannot express a resumption whose EXISTENCE depends on an earlier
 * resumption's real answer. Fixture 3 below is that program, and it runs.)
 *
 * *The projection tension, and how it was resolved.* A residual has already been
 * run under some projection of the plan, but the two consumers want different
 * ones: `resume_C` returns to the perform site and needs the recorded bind
 * frames back, interleaved with the prompts exactly as they stood
 * (`plan_resume_frames`); `extend_C` stays inside the scope and must not have
 * them (`plan_enter_frames`). Under the suspension this was free -- each
 * operation re-ran under its own projection. Under a residual the choice looks
 * like it must be made once, at production.
 *
 * B1.5 takes option (d) of the four that were on the table: **the choice is
 * deferred into the residual and taken at consumption**. Production runs under a
 * THIRD projection, `plan_protocol_frames`, which renders a recorded bind frame
 * as `PSiteF` -- a frame that is neither applied nor dropped but *asks what mode
 * it is in*. `extend_C` and `resume_C` install a `PModeF` marker directly under
 * the residual they drive; a `PSiteF` reached in `MResume` behaves as `PBindF`,
 * and in `MExtend` as nothing. Because the marker is dynamically scoped, the
 * bind frames a layer has carried into its own captured continuations -- the
 * ones at the second and later boundary hits, where the residual is no longer
 * literally `plan_enter_frames pl` -- get the same treatment without anyone
 * having to locate them. Fixtures 5 and 7 are the evidence that the two
 * operations stayed observably different: the same context, consumed both ways,
 * yields `own(site2(aborted))` against `own(aborted)`, and
 * `own(site2([site1 ...]))` against `own([...])`.
 *
 * *What this module is.* A small machine, not a copy of the production one. It
 * holds only what the general weave needs: prompt provenance, the classification
 * derived from it, the scope PLAN a captured segment is turned into, the three
 * context operations over that plan, a step relation that covers them, the laws
 * they owe -- **stated, not proved** -- and, new in B1.5, executable fixtures for
 * the nine conditions the gate asks about. Clarity over efficiency throughout,
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
 *
 * *The nine gate conditions, as this file leaves them.* Each is a fixture at the
 * bottom, run with `psteps` at a definite fuel, and checked by `assert_norm` --
 * never by a comment claiming a result.
 *
 *   1. prefix runs exactly once -- **PASSED AS A COST STATEMENT, and NOT as an
 *      extensional one.** The machine here is pure, and fixture 1 checks that
 *      the residual and the suspension reach the SAME value; replay is therefore
 *      invisible to `pobs_eq`. What is checked is the work: lengthening the
 *      protected prefix costs the residual one copy and the suspension exactly
 *      two. See `fixture_1_prefix_runs_once`, which states the slope, and the
 *      finding recorded there.
 *   2. two resume requests, in order -- PASSED (`fixture_2_two_requests`).
 *   3. the second resume exists only because of the first's REAL answer --
 *      PASSED (`fixture_3_retry_on_failure`, two runs that differ only in the
 *      answer and differ in how many resumptions happen).
 *   4. effects between two resumes keep their order -- PASSED
 *      (`fixture_4_effect_between_resumes`).
 *   5. a clause that never resumes terminates correctly -- PASSED, at both plan
 *      shapes (`fixture_5_never_resumes`, `fixture_5b_never_resumes_with_bind`).
 *   6. a transparent plan agrees with the borrow -- **PASSED AT AN INSTANCE, NOT
 *      IN GENERAL.** `fixture_6_transparent` checks the frames the transparent
 *      projection produces against the frames `Hoop.Runtime.Semantics.borrow`
 *      produces, and checks that `enter_C` and the residual-driven `extend_C`
 *      converge to the same value on a concrete program. The quantified
 *      statement is `law_transparent_agrees` and it is B3's, unproved.
 *   7. a mixed plan preserves prompt / cell / bind ORDER -- PASSED
 *      (`fixture_7_mixed_order`, structurally on all three projections and then
 *      observably on a run).
 *   8. multi-shot FROM THE SAVED POINT -- PASSED (`fixture_8_multi_shot`).
 *   9. no clause-inspecting mechanism, no assumption about `apply` -- a property
 *      of the design; where it is respected is stated at `pstep` and at
 *      `enter_ctx_C`.
 *
 * *Three things B1.5 had to state rather than prove, listed here so that no
 * reader has to find them.*
 *
 *   - The four laws are unproved, as in B1. They are `prop` definitions
 *     parameterised by a `ctx_ops`; B2 proves them of `ref_ops`.
 *   - Production is a DETACHED run: the residual is built with an empty stack
 *     below the plan, so an operation the inner computation performs that no
 *     plan prompt handles is `PStuck` here where the real machine would carry it
 *     outward. The laws are therefore stated under a `settles` hypothesis, which
 *     is exactly this condition and nothing more; the note on `enter_ctx_C`
 *     explains why the obvious repair is not well defined.
 *   - `pfind_mode` finds the NEAREST enclosing `PModeF`, with no label to match
 *     on. The discipline that makes this right -- a mode marker is installed
 *     immediately below the residual it drives, so no other residual's marker
 *     can come between a marker frame and its own -- is argued at `pfind_mode`
 *     and is NOT proved.
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
 * **Where a prompt came from**, and the ONLY new thing a prompt frame carries.
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

(**
 * **Which of the two consumers is driving a residual.**
 *
 * This is the whole of the projection decision, moved out of plan construction
 * and into a frame the machine can read while the residual runs. `MExtend` is
 * `bindScope` -- the extension stays inside the scope, so the perform site's
 * recorded bind frames must not fire. `MResume` is `resumeScope` -- control is
 * returning to the perform site, so they must.
 *
 * It is a two-constructor type rather than a boolean for the reason `plan_item`
 * has one constructor per mechanism: a boolean field would put the reader of
 * every `PSiteF` rule in the position of remembering which way round it went.
 *)
type weave_mode =
  | MExtend
  | MResume

(* ------------------------------------------------------------------ *)
(*  The prototype AST                                                  *)
(*                                                                     *)
(*  `Hoop.Runtime.Syntax.comp_tree` / `frame` with provenance on the    *)
(*  prompt, with the three context operations given nodes of their own, *)
(*  and -- new in B1.5 -- with the three frames the residual protocol   *)
(*  is made of. Every constructor is renamed (`P...`) so that nothing   *)
(*  here shadows the production type: a prototype that could be         *)
(*  confused for the shipped AST at a call site is a prototype that     *)
(*  will be, and `--print_full_names` is not something a reader runs by *)
(*  default.                                                            *)
(*                                                                     *)
(*  The block is mutually recursive and cannot be split: `plan_item`    *)
(*  holds return clauses (`v -> pcomp`), the extend/resume nodes hold a *)
(*  `plan` and a `pctx`, a `pctx` holds a residual STACK and a `pstate`,*)
(*  and a `pstate` holds a `pcomp`. `pstate` joining the block is new:  *)
(*  a context that fails to settle carries the state it failed in, and  *)
(*  a diagnostic that had to be re-encoded as a string would be a       *)
(*  diagnostic nobody could act on.                                     *)
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

(**
 * **The frames.** Three of the six are new in B1.5 and all three exist for the
 * residual protocol; nothing else in the file changed shape.
 *
 *   - `PBoundaryF` is THE SCOPE BOUNDARY, and the reason the protocol is a
 *     protocol. Production pushes it UNDER the inner computation and OVER the
 *     plan's frames, so a value leaving the scope meets it FIRST and the layers
 *     only afterwards. With no mode installed it stops the machine
 *     (`PPaused`); with one installed it hands the value to that mode's
 *     responder. It carries nothing: everything it would have carried is either
 *     in the stack below it or in the marker it finds there.
 *
 *     Because it sits on the stack like any other frame, a layer clause that
 *     captures a continuation captures it too -- which is exactly what makes the
 *     second and later boundary hits happen at all. Nothing has to arrange for
 *     them; the layer's own algebra does.
 *
 *   - `PSiteF` is a RECORDED PERFORM-SITE BIND FRAME whose firing is deferred.
 *     It is the resolution of the enter/resume tension: `plan_protocol_frames`
 *     turns each `PIBind` into one of these, and the frame asks the nearest
 *     `PModeF` whether it is a `PBindF` (under `MResume`) or nothing at all
 *     (under `MExtend`). Under the suspension the same difference was one
 *     function call wide because each operation re-ran the suspension under its
 *     own projection; here the projection has to survive INSIDE a configuration
 *     that was produced before either consumer existed, and this frame is how.
 *
 *   - `PModeF` is what a consumer installs directly beneath the residual it is
 *     driving. It carries the mode and the RESPONDER -- the function to run at
 *     each boundary hit, which is the accumulated extension chain followed by
 *     the consumer's own function. It is inert to values passing through, like
 *     `PParamF`, so a residual that drains past it is unaffected by it.
 *)
and pframe (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PBindF: fn:(v -> pcomp v cl) -> pframe v cl
  | PParamF: label:string -> value:v -> pframe v cl
  | PPromptF:
      hs:handlers cl ->
      ret:option (v -> pcomp v cl) ->
      prov:prompt_provenance ->
      pframe v cl
  | PBoundaryF: pframe v cl
  | PSiteF: fn:(v -> pcomp v cl) -> pframe v cl
  | PModeF: mode:weave_mode -> respond:(v -> pcomp v cl) -> pframe v cl

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
 *     later ones in the wrong place. Fixture 7 exhibits exactly that stack and
 *     shows the inner bind firing once per leaf and the outer one once, on the
 *     layer's assembled answer.
 *
 *     What survives of `borrow`'s decision is the same decision, moved TWO steps
 *     later. In B1 it moved from plan construction to the projection --
 *     `plan_enter_frames` dropped these and `plan_resume_frames` kept them. In
 *     B1.5 it moves again, from the projection to the mode marker the consumer
 *     installs, because a residual is produced before either consumer exists.
 *     The three projections below are what is left of it as syntax.
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
 * projections instead.
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
 * **A context value: a RESIDUAL MACHINE CONFIGURATION.**
 *
 * `C x` of the design note, at F*'s single value type. It is not a `v`, and that
 * is deliberate -- a machine-side datum the surface receives as an opaque token,
 * which is what the design's stop condition "the FFI passing anything but a
 * context plan or an opaque context value" already anticipates.
 *
 * ---------------------------------------------------------------------------
 * **WITHDRAWN: the suspension.** B1 defined
 *
 * ```fstar
 * and pctx (v cl: Type) = | PCtx: pending:pcomp v cl -> pctx v cl
 * ```
 *
 * -- the inner computation, kept unrun, with each of the three operations
 * splicing its own projection of the plan around it. That representation
 * VERIFIED, and every law below was statable over it; it is withdrawn on a cost
 * argument and not a soundness one. Re-entering such a context re-runs the inner
 * computation, so a clause that produces a context and consumes it twice -- the
 * `runScope try` / `resumeScope cx k` shape of `catch` -- runs `try` once per
 * consumption. The design note recorded the same effect from the other side
 * ("two `bindScope` calls on the same context re-enter the intervening context
 * twice, which for a nondeterministic `ctx` duplicates branches"). The shipped
 * runtime demonstrably runs the protected computation once, so the prototype's
 * reference semantics may not be a machine that runs it twice.
 *
 * `susp_extend` / `susp_resume` at the bottom of this file are B1's two
 * operations, kept as executable evidence and nothing else: fixture 1 runs the
 * withdrawn representation beside the present one and checks the cost claim
 * rather than asserting it.
 *
 * **What of B1's reasoning survives, unchanged.** B1 rejected letting a context
 * be THE LAYER'S OWN ANSWER -- `Array x` for a nondeterministic layer -- and
 * that argument still stands and still rules out a per-layer distributive law.
 * The machine cannot take `Array x` apart. It could therefore not run a
 * continuation at each value such a context holds, and nothing short of a
 * per-layer law `f (m x) -> n (f x)` would give it one -- which is evidence
 * about a handler's BEHAVIOUR, not about its provenance, and provenance is the
 * only evidence this design is willing to carry. The residual keeps that
 * property: nothing below ever decomposes a context, and the "no values" case
 * does not arise, because a layer that produced no leaves simply never reaches
 * the boundary and its own algebra says what that means (fixture 5).
 * ---------------------------------------------------------------------------
 *
 * **The three shapes, and what each means.**
 *
 *   - `PCtxDone y` -- the layers and the owner produced `y` without ever asking
 *     the scope for anything, and there was no recorded bind frame left in the
 *     path either. A `Full` clause that discards its continuation gets here.
 *
 *   - `PCtxRequests x residual post` -- the machine is paused at
 *     `PStep (PVar x) residual`, whose head is a `PBoundaryF` or a `PSiteF`:
 *     the head frame is the one whose meaning depends on the consumer, and
 *     `residual` is everything the layer and owner handlers have grown up to
 *     this point. `post` is the EXTENSION CHAIN accumulated by `extend_ctx_C`,
 *     not yet applied, and it is a field rather than something already run into
 *     the residual so that extending a context re-runs nothing at all.
 *
 *   - `PCtxLost st` -- production did not settle: it ran out of fuel, or got
 *     stuck, or was rejected. `st` is the state it stopped in, kept whole. The
 *     laws below are conditioned on this constructor not arising; see `settles`.
 *
 * A context does NOT carry the plan it belongs to. The plan is what the machine
 * holds at the transition, and a context carrying its own copy would be a second
 * plan that can disagree with it. The operations take both -- although, and this
 * is the price of the representation, only `enter_ctx_C` now READS the plan it
 * is given; see the note on `resume_C`.
 *)
and pctx (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PCtxDone: value:v -> pctx v cl
  | PCtxRequests:
      value:v ->
      residual:list (pframe v cl) ->
      post:(v -> pcomp v cl) ->
      pctx v cl
  | PCtxLost: st:pstate v cl -> pctx v cl

(**
 * **The machine states.**
 *
 * `PPaused` is new and is the only state a context is built from. It is not
 * `PStep`: `psteps` must STOP at it, or production would spin on a boundary it
 * has no answer for, and a fuel-exhausted `PStep` must stay distinguishable from
 * a deliberate pause or `PCtxLost` would swallow the difference.
 *
 * `PRejected` carries the SHIPPED rejection type. It is flat and independent of
 * `v` and `cl`, so there is nothing to translate: a plan refused here is refused
 * with the very constructor `Hoop.Runtime.Semantics.step` produces, which is
 * what makes "the caller can produce the existing `UnborrowableScope` rejection"
 * a fact about a type rather than a resemblance between two enumerations.
 *)
and pstate (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PDone: value:v -> pstate v cl
  | PStep: c:pcomp v cl -> k:list (pframe v cl) -> pstate v cl
  | PPaused: value:v -> residual:list (pframe v cl) -> pstate v cl
  | PStuck: eff:string -> op:string -> pstate v cl
  | PRejected: rejection -> pstate v cl

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
 * Nothing here consults a flag. `fixture_6_transparent` checks the arm on a real
 * `mk_handlers` table rather than on a hand-built `PITransparent`.
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
 *   - `PBindF` is RECORDED, in place. Whether and how it fires is decided by the
 *     consumer and not here -- see `PIBind`, where the reason the plan cannot
 *     simply drop it is set out.
 *
 *   - `PParamF` is KEPT ENTIRE, label and value, exactly as in `borrow`.
 *
 *   - A prompt is CLASSIFIED, and each class becomes its own plan item.
 *
 * The protocol frames -- `PBoundaryF`, `PSiteF`, `PModeF` -- fall through the
 * final clause and contribute nothing. They cannot appear in a captured segment
 * of a well-formed program in the first place (a scope's segment runs from the
 * perform site out to its owner, and a boundary is never between the two), so
 * the clause is a totality obligation and not a rule; giving them an item would
 * have been inventing a meaning for a stack that cannot occur.
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
    | _ :: rest -> plan_layers rest

(** **The plan**: the classified intervening segment, and the owner beside it,
    unclassified and unborrowed. *)
let plan_of (#v #cl: Type) (ints: list (pframe v cl)) (own: powner v cl)
  : either plan_failure (plan v cl)
  = match plan_layers ints with
    | Inl e -> Inl e
    | Inr ls -> Inr (Plan ls own)

(* ------------------------------------------------------------------ *)
(*  Reading the plan back out as frames                                *)
(*                                                                     *)
(*  THREE projections now, and the third is the point of B1.5. The      *)
(*  first two are unchanged from B1 and survive because the laws speak  *)
(*  of them: `plan_enter_frames` is what entering a scope means and     *)
(*  `plan_resume_frames` is what returning to a perform site means, and *)
(*  both appear on the right-hand side of an ANCHORED law, where they   *)
(*  are descriptions independent of the operations. The third,          *)
(*  `plan_protocol_frames`, is what a residual is actually built under, *)
(*  and it is the other two held apart until a consumer says which one  *)
(*  it wanted.                                                          *)
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
 * `borrow`'s first clause, unchanged in effect.
 *
 * A transparent item comes back as `PPromptF hs None PMono`, which is the
 * borrowed frame today's `borrow` produces; since a transparent prompt had no
 * return clause to begin with, this rewrites nothing.
 * `fixture_6_transparent` checks that equality on a concrete plan; the
 * quantified version is B3's.
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
 *
 * In B1.5 this function is no longer what a resumption is BUILT from -- a
 * residual is -- but it is still what a resumption MEANS, and that is why it
 * survives: it is the right-hand side of `law_resume_matches_continuation`, an
 * independent description of resumption that the algebra is measured against.
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
 * **The layers, as the frames a RESIDUAL is produced under** -- the third
 * projection, and the resolution of the enter/resume tension.
 *
 * It is `resume_layer_frames` with `PBindF` replaced by `PSiteF`: the recorded
 * bind frames are PRESENT, in their original interleaving with the prompts, but
 * DORMANT. Under `MResume` a `PSiteF` fires exactly as the `PBindF` it stands
 * for; under `MExtend` it is skipped exactly as `enter_layer_frames` would have
 * dropped it. So this one list is both of the other two, and which one it is
 * gets decided by the consumer rather than by the producer.
 *
 * **Why not option (b) or (c), which were the obvious two.** Building under
 * `plan_enter_frames` and having `resume_C` re-insert the binds afterwards is
 * well defined at the FIRST boundary, where the residual is literally
 * `plan_enter_frames pl` and the correspondence with `layers` is positional. It
 * is not well defined at the second: by then a layer clause has captured the
 * segment and re-spliced it on top of its own frames, so the residual is
 * `layer :: (clause frames) ++ (rest of the plan) ++ ...` and there is no
 * position left at which "the bind that stood between this layer and the owner"
 * could be put back. Building under `plan_resume_frames` and having `extend_C`
 * skip the binds is the mirror image and fails the same way. Under this
 * projection neither consumer has to FIND anything: the frames the layer carried
 * into its captured continuation are `PSiteF`s already, and they ask.
 *
 * **And this is where the two operations stay two.** A representation that had
 * dropped the bind frames at construction, as
 * `Hoop.Runtime.Semantics.borrow` does, would have made `resume_C` and
 * `extend_C` literally the same definition and nothing in the file would have
 * said which of them was wrong. Under this one they differ by a constructor --
 * `MResume` against `MExtend` -- and `fixture_5b_never_resumes_with_bind` and
 * `fixture_7_mixed_order` check that the difference is observable, on ONE
 * residual consumed both ways.
 *)
let rec protocol_layer_frames (#v #cl: Type) (ls: list (plan_item v cl))
  : Tot (list (pframe v cl)) (decreases ls)
  = match ls with
    | [] -> []
    | PIBind fn :: rest -> PSiteF fn :: protocol_layer_frames rest
    | PICell l x :: rest -> PParamF l x :: protocol_layer_frames rest
    | PITransparent hs :: rest -> PPromptF hs None PMono :: protocol_layer_frames rest
    | PIReenter hs ret :: rest -> PPromptF hs ret PFamily :: protocol_layer_frames rest

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
 * an accumulating walk with one `rev`). This is a prototype and is never
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

(** **The segment a residual is produced under.** The owner is last here too, so
    a protocol that drains without ever asking the scope for anything still
    applies the owner's answer former exactly once -- which is the `PCtxDone`
    case, and is what `fixture_5_never_resumes` checks. *)
let plan_protocol_frames (#v #cl: Type) (pl: plan v cl) : list (pframe v cl)
  = protocol_layer_frames (Plan?.layers pl) @ [owner_frame (Plan?.owner pl)]

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

(** **The operation a lost context degenerates to.** A `PCtxLost` cannot be
    driven, and the operations must still return a computation, so they return
    one that no plan prompt handles and that the machine therefore reports as
    `PStuck`. It is deliberately an ordinary `PPerform` under a reserved label,
    in the style of `Hoop.Runtime.Semantics.var_eff`, rather than a new state: a
    prototype that grew a constructor for its own bookkeeping failure would be
    reporting the failure in a way the shipped machine has no counterpart for. *)
let pctx_lost_eff : string = "%hoop.ctx"
let pctx_lost_op : string = "lost"

(**
 * **Entering a scope**: run the inner computation under the plan. UNCHANGED from
 * B1, in definition and in meaning.
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
 * reinstalled: the scope runs instead of the rest of the enclosing block. This
 * is the one operation that is still plain syntax and still reads the plan
 * directly, and `fixture_6_transparent` checks it against the residual-driven
 * route on a concrete program.
 *)
let enter_C (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) : pcomp v cl
  = PSplice (plan_enter_frames pl) c

(**
 * **Driving a residual**, which is what both consuming operations are.
 *
 * Splice the residual back on, install the mode marker DIRECTLY BENEATH IT, and
 * hand the paused value to the frame that was waiting for it. The marker's
 * responder is the accumulated extension chain followed by the consumer's own
 * function, so a boundary hit runs `post` and then `f`, in that order, and every
 * later boundary hit -- the ones the layer's own algebra produces by resuming
 * its captured continuations -- finds the same marker and runs the same thing.
 * That is the whole of the coroutine: no loop is written here, because the loop
 * is the machine's.
 *
 * **The marker goes under the residual and nowhere else.** `PSplice` pushes its
 * frames above the current stack, so `resid @ [marker]` puts the marker between
 * the residual and whatever the consumer's own continuation is. That placement
 * is what `pfind_mode`'s nearest-enclosing search relies on.
 *
 * **`PCtxDone` needs no marker.** There is no boundary and no site frame left to
 * ask, so both consumers agree on it and both return the value -- which is
 * correct and is checked by `fixture_5_never_resumes`: a layer that produced no
 * leaves runs the continuation nowhere, and its own algebra has already said
 * what that means.
 *)
let ctx_drive (#v #cl: Type) (m: weave_mode) (cx: pctx v cl) (f: v -> pcomp v cl)
  : pcomp v cl
  = match cx with
    | PCtxDone y -> PVar y
    | PCtxRequests x resid post ->
      PSplice (resid @ [PModeF m (fun z -> pbind (post z) f)]) (PVar x)
    | PCtxLost _ -> PPerform pctx_lost_eff pctx_lost_op []

(**
 * **Extending a context**: continue, at each value the context holds, with an
 * INNER computation.
 *
 * The layers are already entered -- that happened when the residual was produced
 * -- so what this does is put `g` at the leaves and let the layer's own algebra
 * rebuild the context around the results. Nothing decomposes a context; nothing
 * injects into one. This is `bindScope`, whose function argument is
 * `x -> Hoop inner y`, over the VALUE rather than over `ctx x`: the clause never
 * sees inside, and the machine is what re-enters the intervening prompts and
 * applies the function there.
 *
 * `g` runs UNDER the residual, which is to say under the layer prompts, so an
 * extension may perform the effects the scope could perform. That is not a
 * convenience: `Hoop inner y` is the type the surface gives it, and a `g` that
 * ran outside the layers would be at the wrong row.
 *
 * **`MExtend`, and that is the entire difference from `resume_C`.** An extension
 * stays inside the scope -- its answer is another `f (ctx y)`, to be extended or
 * resumed again -- so the perform site's recorded bind frames must not fire, and
 * under this mode the `PSiteF`s they became do not.
 *)
let extend_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: v -> pcomp v cl)
  : pcomp v cl
  = ctx_drive MExtend cx g

(**
 * **The context extending produces**, and it RUNS NOTHING.
 *
 * The extension is recorded in `post` and applied when the context is next
 * driven. That is the one place the residual representation is *lazier* than the
 * suspension rather than eager, and it is deliberate: an `extend_ctx_C` that
 * drove the protocol forward would have to stop somewhere, and the only place to
 * stop is the next boundary -- which means running the layers' work for the
 * first leaf before anyone has asked for it, and doing it again for every
 * further extension. Composing at the leaves costs one closure and re-runs
 * nothing.
 *
 * It also keeps `law_assoc`'s algebraic half a statement about `pbind`:
 * extending by `g` and then by `h` builds `fun z -> pbind (pbind (post z) g) h`
 * where extending by `fun x -> pbind (g x) h` builds
 * `fun z -> pbind (post z) (fun x -> pbind (g x) h)`, and the two sides of the
 * law are two bracketings of one chain.
 *
 * `PCtxDone` absorbs an extension, and must: a context that never reached the
 * boundary holds no values, so there is nothing for `g` to be applied to. This
 * is `[] >>= g == []` and not a special case.
 *)
let extend_ctx_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: v -> pcomp v cl)
  : pctx v cl
  = match cx with
    | PCtxDone y -> PCtxDone y
    | PCtxRequests x resid post -> PCtxRequests x resid (fun z -> pbind (post z) g)
    | PCtxLost s -> PCtxLost s

(**
 * **Resuming a context onto the continuation** -- the important one.
 *
 * **It is NOT "hand the context value to the continuation".** It is: hand the
 * layer and owner handlers a real answer at the point they stopped, run the
 * continuation at each value the context holds, and let each handler's own
 * algebra rebuild the context. The one Gate A exhibits --
 *
 * ```purescript
 * resumeScopeAtArray _weave = \cx k -> case Array.head cx of
 *   Just x -> continue k x
 *   Nothing -> ?noValueToReturn
 * ```
 *
 * -- takes one value out of the context and has nothing to return when the
 * context holds none. Here the context is never taken apart and the "none" case
 * does not arise.
 *
 * **A change of posture that has to be stated.** B1's comment here said that an
 * implementation of `resume_C` which could be written WITHOUT TOUCHING THE PLAN
 * is wrong. Under the residual representation that is no longer true, and the
 * `pl` parameter below is genuinely unused. The plan is read exactly once, by
 * `enter_ctx_C`, when the residual is produced; by the time a consumer sees the
 * context the segment is IN it. That is the price of the representation, and it
 * moves the discriminating power of the laws rather than removing it: what used
 * to catch a plan-ignoring implementation at `o_resume` now catches it at
 * `o_enter_ctx`, which is where `flat_ops` is wrong below.
 *
 * The parameter is kept, and kept in `ctx_ops`, because the LAWS need it -- both
 * anchored right-hand sides are written in terms of the plan -- and because an
 * alternative implementation is entitled to a representation that does need it
 * (`pointwise_ops` is one, and uses it).
 *
 * **`MResume`, and that is the entire difference from `extend_C`.** A resumption
 * returns to the perform site, so the recorded bind frames fire, in their
 * original interleaving with the prompts: the innermost one at every leaf,
 * inside the layer, and an outer one once, on the layer's assembled answer.
 * `fixture_7_mixed_order` is that sentence as a value.
 *)
let resume_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (k: v -> pcomp v cl)
  : pcomp v cl
  = ctx_drive MResume cx k

(**
 * **B1's two consuming operations, withdrawn, kept executable.**
 *
 * These are the suspension representation exactly as it stood: the context was
 * the unrun inner computation, so it needed no type of its own, and each
 * operation spliced its own projection of the plan around it. They are here for
 * one reason -- `fixture_1_prefix_runs_once` runs them beside the residual and
 * MEASURES the difference, rather than asserting it in prose -- and nothing else
 * in the file refers to them. They are not a `ctx_ops`: they cannot be, because
 * `o_enter_ctx` must return a `pctx` and the withdrawn representation has no
 * constructor to return.
 *)
let susp_extend (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) (g: v -> pcomp v cl)
  : pcomp v cl
  = PSplice (plan_enter_frames pl) (pbind c g)

let susp_resume (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) (k: v -> pcomp v cl)
  : pcomp v cl
  = PSplice (plan_resume_frames pl) (pbind c k)

(* ------------------------------------------------------------------ *)
(*  The machine                                                        *)
(* ------------------------------------------------------------------ *)

type pstack (v: Type) (cl: Type) = list (pframe v cl)

(** The clause interpreter, monomorphized to the prototype's AST. The prototype
    has no scoped dispatch (see the module header), so there is one interpreter
    and not two.

    **Condition 9 lives here.** A clause is a `cl`, an opaque parameter, and the
    only thing the machine may do with one is hand it to `apply` together with a
    payload and a continuation. Nothing below inspects a clause, matches on one,
    or assumes anything about what `apply` returns -- the residual protocol is
    built entirely out of frames the machine itself pushed, and a layer clause
    reaches the boundary only by resuming the continuation it was given, through
    the ordinary `PSplice` rule. The fixtures instantiate `apply` with clauses
    that resume twice, resume conditionally, and never resume, and the protocol
    is the same protocol in all three cases. *)
let papply_t (v cl: Type) = cl -> list v -> (v -> pcomp v cl) -> pcomp v cl

(**
 * **The table lookup, as a parameter** -- new in B1.5, and it is a concession to
 * checkability rather than a design change.
 *
 * `pref_lookup` below is `Hoop.Runtime.Handlers.lookup_handler`, and that is the
 * reference instantiation; the classification still reads the REAL table through
 * `borrowable` and `blocking_effects`, so nothing about which prompts a scope may
 * cross has been parameterised away.
 *
 * *Why it had to become a parameter.* `handlers` is abstract in
 * `Hoop.Runtime.Handlers.fsti`, so `lookup_handler` does not reduce, so an
 * `assert_norm` over a program that dispatches gets stuck at the first
 * `PPerform` and the fixtures below could not be CHECKED -- only claimed.
 * `Hoop.Runtime.Test` solves this with `friend Hoop.Runtime.Handlers`, and F*
 * permits `friend` only in a module that has an interface. This prototype does
 * not have one and is not getting one, so the lookup is threaded instead, and
 * the fixtures pass a table they can compute with.
 *
 * *What that costs, stated plainly.* The fixtures exercise the machine's
 * dispatch DISCIPLINE against a table of their own and not against the shipped
 * table's realisation. That is the same trade `apply` has always made -- clauses
 * are opaque closures and every fixture supplies its own -- and it is a smaller
 * trade than leaving the nine conditions unchecked. The laws quantify over the
 * lookup, so they are strictly stronger than they were.
 *)
let plookup_t (cl: Type) = handlers cl -> string -> string -> option (found_clause cl)

(** **The reference lookup**: the table as it ships. *)
let pref_lookup (#cl: Type) : plookup_t cl = fun hs eff op -> lookup_handler hs eff op

(** The prompt holding the handler for this action, and the stack split there:
    `(captured, found, below)`, captured including the prompt. The shipped
    `find_prompt` carries a refinement tying it to `handled_in`; this one does
    not, because nothing here proves progress and a refinement nobody spends is
    a refinement that has to be maintained.

    The three protocol frames fall through the catch-all, and must: a boundary
    that stopped the search would delimit effects it has no business delimiting
    -- the scope's operations are meant to reach the layer handlers, which is the
    whole point of weaving -- and a captured segment that stopped short of the
    boundary would not put the boundary back on resumption, which is what makes
    the second and later requests happen. *)
let rec pfind_prompt (#v #cl: Type) (lk: plookup_t cl) (eff op: string) (k: pstack v cl)
  : Tot (option (pstack v cl & found_clause cl & pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | PPromptF hs ret prov :: rest ->
      (match lk hs eff op with
        | Some c -> Some ([PPromptF hs ret prov], c, rest)
        | None ->
          (match pfind_prompt lk eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PPromptF hs ret prov :: cap, c, below)))
    | f :: rest ->
      (match pfind_prompt lk eff op rest with
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

(**
 * **Which consumer, if any, is driving this residual** -- the nearest enclosing
 * `PModeF`, searched exactly as `pfind_param` searches for a cell and
 * `pfind_prompt` for a prompt.
 *
 * **There is no label, and the discipline that makes that safe is stated here
 * and NOT PROVED.** The invariant is: a mode marker is installed by `ctx_drive`
 * immediately beneath the residual it drives, and a residual is produced by
 * `enter_ctx_C` on a stack whose bottom is empty. Under that invariant no other
 * residual's marker can lie between a marker frame and its own, because a marker
 * belonging to some other context is either above the frame in question -- in
 * which case it has been popped before the frame is reached -- or below that
 * context's own residual, which the frame in question is not inside.
 *
 * Labels would settle it rather than argue it, and the file already has the
 * idiom: `PNewP` takes a label the surface supplies, and
 * `Hoop.Runtime.Syntax.NewP` does the same. What stopped B1.5 from taking that
 * route is that a label would have to be generated per scope entry, which means
 * either a counter in the machine or a `string` argument on `o_enter_ctx`, and
 * the second puts a name in the statement of all four laws for the sake of a
 * case no fixture reaches. If B2 finds a program that breaks the invariant, the
 * repair is a label and it is local to three frames and one search.
 *)
let rec pfind_mode (#v #cl: Type) (k: pstack v cl)
  : Tot (option (weave_mode & (v -> pcomp v cl))) (decreases k)
  = match k with
    | [] -> None
    | PModeF m r :: _ -> Some (m, r)
    | _ :: rest -> pfind_mode rest

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
 * The two consuming context operations get one rule each, and each rule is a
 * single appeal to the operation. That is deliberate: a transition that inlined
 * `plan_enter_frames` would be a second definition of what a tactic MEANS, and
 * the whole point is that there is exactly one.
 *
 * **The three new value rules are the protocol**, and they are the only rules in
 * the machine that consult something other than the frame in front of them:
 *
 *   - `PModeF` is inert. A value passing a marker is a protocol that has
 *     finished; the marker is popped like a cell.
 *   - `PBoundaryF` with no mode in scope PAUSES -- this is where a context comes
 *     from. With a mode in scope it hands the value to that mode's responder and
 *     CONTINUES UNDER THE REST OF THE STACK, marker included, so the next
 *     boundary hit finds the same marker.
 *   - `PSiteF` with no mode in scope pauses too, and for the same reason: the
 *     layers have finished, a recorded perform-site frame is next, and whether
 *     it fires is not yet known. With a mode in scope it is a `PBindF` under
 *     `MResume` and a no-op under `MExtend`.
 *
 * Nothing here looks inside a clause and nothing here assumes what `apply`
 * returns; see the note at `papply_t`.
 *)
let pstep (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (s: pstate v cl)
  : Tot (pstate v cl)
  = match s with
    | PDone _ -> s
    | PPaused _ _ -> s
    | PStuck _ _ -> s
    | PRejected _ -> s
    | PStep c k ->
      match c with
      | POp comp fn -> PStep comp (PBindF fn :: k)
      | PHandle hs ret prov body -> PStep body (PPromptF hs ret prov :: k)
      | PPerform eff op payload ->
        (match pfind_prompt lk eff op k with
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
          | PModeF _ _ :: rest -> PStep (PVar value) rest
          | PBoundaryF :: rest ->
            (match pfind_mode rest with
              | None -> PPaused value k
              | Some (_, respond) -> PStep (respond value) rest)
          | PSiteF fn :: rest ->
            (match pfind_mode rest with
              | None -> PPaused value k
              | Some (MResume, _) -> PStep (fn value) rest
              | Some (MExtend, _) -> PStep (PVar value) rest)
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
    same idiom the shipped monad laws are stated in. `PPaused` is terminal, or
    production would never return a context. *)
let rec psteps (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (fuel: nat) (s: pstate v cl)
  : Tot (pstate v cl) (decreases fuel)
  = if fuel = 0 then s
    else
      match s with
      | PDone _ -> s
      | PPaused _ _ -> s
      | PStuck _ _ -> s
      | PRejected _ -> s
      | PStep _ _ -> psteps lk apply (fuel - 1) (pstep lk apply s)

(** **Loading a program.** *)
let pload (#v #cl: Type) (c: pcomp v cl) : pstate v cl = PStep c []

(** **The number of transitions to a settled state**, or `None` if the machine
    got stuck, was rejected, or did not settle within `fuel`. It exists for
    `fixture_1_prefix_runs_once`, which is a claim about WORK and can therefore
    not be made with `pobs_eq`; see the finding recorded there. *)
let rec pcost (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
              (fuel: nat) (s: pstate v cl)
  : Tot (option nat) (decreases fuel)
  = match s with
    | PDone _ -> Some 0
    | PPaused _ _ -> Some 0
    | PStuck _ _ -> None
    | PRejected _ -> None
    | PStep _ _ ->
      if fuel = 0 then None
      else (match pcost lk apply (fuel - 1) (pstep lk apply s) with
            | None -> None
            | Some n -> Some (n + 1))

(* ------------------------------------------------------------------ *)
(*  Producing a context                                                *)
(* ------------------------------------------------------------------ *)

(** **A settled machine state, read as a context.** The one place the three
    shapes of `pctx` are decided, so that no operation has to re-decide it. *)
let pctx_of_state (#v #cl: Type) (post: v -> pcomp v cl) (s: pstate v cl) : pctx v cl
  = match s with
    | PDone y -> PCtxDone y
    | PPaused x resid -> PCtxRequests x resid post
    | _ -> PCtxLost s

(**
 * **The context that entering produces**, and the only operation that RUNS
 * anything.
 *
 * The inner computation is loaded with the boundary marker beneath it and the
 * plan's protocol frames beneath that, so a value leaving the scope meets the
 * boundary FIRST and the layers only afterwards. The machine is then run until
 * it settles, and whatever it settled as is the context. Nothing is built as
 * syntax: the residual is a machine configuration because a machine produced it,
 * which is the entire difference from the withdrawn suspension.
 *
 * `post` starts as `PVar`, the inner monad's `pure`. Extensions compose onto it;
 * see `extend_ctx_C`.
 *
 * **Condition 9, again.** The plan's frames and the boundary marker are all the
 * machine's own; the inner computation is run, not read; and no clause is
 * examined on the way. The only new obligation on the surface is the one the
 * design already anticipated -- that the FFI receive an opaque token.
 *
 * **The limitation this operation has, stated rather than discovered.**
 * Production runs with an EMPTY stack beneath the plan. So an operation the
 * inner computation performs before the first pause, which no plan prompt
 * handles, is `PStuck` here -- and hence `PCtxLost` -- where the real machine
 * would have carried it outward to a handler beyond the owner. After the first
 * pause the question does not arise: a consumer splices the residual into the
 * live stack, and everything outward is visible again.
 *
 * The obvious repair -- run production on top of the ambient stack and truncate
 * the residual at a marker -- is NOT well defined, and it is worth writing down
 * why rather than leaving it to be re-derived. If production dispatches to an
 * ambient handler that is tail-resumptive, the stack it resumes onto is the
 * stack it captured from, the marker is back where it was, and truncation is
 * exact. If that handler is not tail-resumptive, its own pending frames sit
 * BELOW the marker, and truncating discards them -- the ambient handler's
 * unfinished work would silently vanish. So the repair is correct exactly when
 * every ambient handler reached during production is tail-resumptive, which is
 * a condition on a stack the plan deliberately does not classify.
 *
 * `settles` below is exactly this restriction, and the four laws carry it as a
 * hypothesis rather than pretending it is not there.
 *)
let enter_ctx_C
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (pl: plan v cl) (c: pcomp v cl)
  : pctx v cl
  = pctx_of_state (PVar #v #cl)
      (psteps lk apply fuel (PStep c (PBoundaryF :: plan_protocol_frames pl)))

(* ------------------------------------------------------------------ *)
(*  The operations as data                                             *)
(*                                                                     *)
(*  The laws are stated over this record rather than over the five      *)
(*  definitions above, and that is what gives them their discriminating *)
(*  power: a law over a fixed implementation is a proposition about one  *)
(*  program, while a law over the record is a proposition an ALTERNATIVE *)
(*  implementation can be plugged into and fail. Two wrong ones are      *)
(*  supplied below for exactly that purpose.                            *)
(*                                                                     *)
(*  `o_enter_ctx` takes the lookup, the clause interpreter and a fuel    *)
(*  bound, and the other four take none of them. That asymmetry is the   *)
(*  representation showing through and is worth keeping rather than      *)
(*  smoothing over: exactly one of the five operations runs the machine, *)
(*  and it is the one that reads the plan. Carrying `apply` as a FIELD   *)
(*  was the alternative and was rejected -- the laws already take an     *)
(*  `apply` for `pobs_eq`, and two of them could then disagree, which is *)
(*  a way for a law to be vacuously true that no reader would notice.    *)
(* ------------------------------------------------------------------ *)

noeq
type ctx_ops (v: Type) (cl: Type) = {
  o_enter: plan v cl -> pcomp v cl -> pcomp v cl;
  o_enter_ctx: plookup_t cl -> papply_t v cl -> nat -> plan v cl -> pcomp v cl -> pctx v cl;
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
 * **Wrong implementation 1: the plan is ignored.** Entering runs the body under
 * the owner alone, and so does production, so the intervening layers are never
 * re-entered and every context behaves as though it held exactly one value --
 * the machine-level rendering of `weave (map (\x -> [x]) body)`.
 *
 * It typechecks, which is the point: nothing in the SIGNATURES rules it out.
 *
 * **What changed in B1.5, and it is worth saying rather than leaving to be
 * noticed.** Under the suspension this algebra was wrong in all five fields at
 * once, because all five spliced a projection of the plan. Under the residual
 * only two fields can be wrong -- `o_enter` and `o_enter_ctx` -- because the
 * other three no longer read a plan at all; its `o_extend`, `o_extend_ctx` and
 * `o_resume` are literally the reference ones. It is the SAME algebra and it is
 * wrong for the SAME reason: a context of its is a residual that never entered a
 * layer, so every later operation, however correct in itself, operates on a
 * configuration that is missing the handlers.
 *
 * **And nothing PURELY ALGEBRAIC rules it out, which is worth more than the
 * counterexample.** This algebra is wrong UNIFORMLY -- every context it produces
 * is plan-free and every operation over one is the reference operation -- so it
 * satisfies every equation that relates its own operations to each other: left
 * identity, right identity and the algebraic half of associativity all hold of
 * it, because both sides of each are equally plan-free. An algebra can be
 * internally coherent and mean nothing.
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
    o_enter_ctx =
      (fun lk apply fuel pl c ->
         pctx_of_state (PVar #v #cl)
           (psteps lk apply fuel (PStep c (PBoundaryF :: owner_only pl))));
    o_extend = (fun pl cx g -> ctx_drive MExtend cx g);
    o_extend_ctx = extend_ctx_C;
    o_resume = (fun pl cx k -> ctx_drive MResume cx k);
  }

(**
 * **Wrong implementation 2: the layers are re-entered per value.** Each leaf
 * gets a FRESH re-entry of the plan instead of sharing the one the residual has
 * already established. This is the OTHER reading of the same counterexample
 * `flat_ops` renders: "inject each value into a singleton" says both that a
 * context is not re-entered (`flat_ops`) and that each value gets a context of
 * its own, which is this.
 *
 * Under the residual representation it is, if anything, more starkly wrong than
 * it was: the responder it installs splices `plan_enter_frames pl` around the
 * result of every boundary hit, so the layers are crossed once by the residual
 * and then again, from the outside, for each leaf the residual offers.
 *
 * It typechecks too, and unlike `flat_ops` it is refused by every one of the
 * four laws, `law_assoc`'s algebraic half included: the two bracketings of an
 * extension differ by where the extra re-entries fall, so the second function
 * receives a rebuilt context where it should have received a value.
 *)
let pointwise_ops (#v #cl: Type) : ctx_ops v cl = {
  o_enter = enter_C;
  o_enter_ctx = enter_ctx_C;
  o_extend =
    (fun pl cx g -> ctx_drive MExtend cx (fun x -> PSplice (plan_enter_frames pl) (g x)));
  o_extend_ctx =
    (fun pl cx g ->
       match cx with
       | PCtxDone y -> PCtxDone y
       | PCtxRequests x resid post ->
         PCtxRequests x resid (fun z -> PSplice (plan_enter_frames pl) (pbind (post z) g))
       | PCtxLost s -> PCtxLost s);
  o_resume =
    (fun pl cx k -> ctx_drive MResume cx (fun x -> PSplice (plan_resume_frames pl) (k x)));
}

(* ------------------------------------------------------------------ *)
(*  Observation                                                        *)
(*                                                                     *)
(*  The same notion `Hoop.Runtime.Laws` uses, at the prototype's AST:   *)
(*  plugged into any continuation, the two computations converge to the *)
(*  same value. The quantification over the stack is the whole point --  *)
(*  a stack is where handlers live, so ranging over every `k` is        *)
(*  ranging over every handler context, INCLUDING the ones a plan       *)
(*  re-enters.                                                          *)
(*                                                                     *)
(*  A NOTE THE NEXT MILESTONE NEEDS. This relation cannot see the       *)
(*  defect B1 was withdrawn for. The machine is pure: a residual is an  *)
(*  immutable value, so consuming one twice and re-running a suspension *)
(*  twice produce the same answers, and `fixture_1_prefix_runs_once`    *)
(*  checks that they do. Replay is a COST here and becomes an           *)
(*  observation only where effects escape the plan -- which in the      *)
(*  shipped runtime is every JS effect, and in this machine is nothing. *)
(*  That is why fixture 1 is stated with `pcost` and not with           *)
(*  `pobs_eq`, and why it would be wrong to claim `pobs_eq` separates   *)
(*  the two representations.                                            *)
(* ------------------------------------------------------------------ *)

let pconverges (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (s: pstate v cl) (x: v) : GTot prop =
  exists (n: nat). psteps lk apply n s == PDone x

let pobs_le (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
            (c1 c2: pcomp v cl) : GTot prop =
  forall (k: pstack v cl) (x: v).
    pconverges lk apply (PStep c1 k) x ==> pconverges lk apply (PStep c2 k) x

let pobs_eq (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
            (c1 c2: pcomp v cl) : GTot prop =
  pobs_le lk apply c1 c2 /\ pobs_le lk apply c2 c1

(* ------------------------------------------------------------------ *)
(*  The laws -- DEFINED, not proved                                    *)
(*                                                                     *)
(*  Each is a DEFINITION whose type is `prop`. None is a `val` without  *)
(*  a proof, none is assumed, and NOTHING IN THIS MODULE DEPENDS ON ANY *)
(*  OF THEM HOLDING: no operation, no transition, no fixture and no     *)
(*  other definition mentions them. Proving them is B2's job. B1.5's    *)
(*  job is to keep them STATABLE over the new representation, which is  *)
(*  itself the check that the representation is right -- a              *)
(*  representation that cannot express associativity has already        *)
(*  failed, and one that can express it only of a fixed implementation  *)
(*  cannot be used to rule a wrong one out.                             *)
(*                                                                     *)
(*  They are stated over `ctx_ops`, so `law_X ops ...` is a proposition *)
(*  about an implementation. The intended readings are                  *)
(*                                                                     *)
(*    law_X lk apply fuel ref_ops ...       -- B2 proves these          *)
(*    ~(law_X lk apply fuel pointwise_ops ...) -- refused by all four   *)
(*    ~(law_X lk apply fuel flat_ops ...)   -- refused by the two       *)
(*                                       ANCHORED laws only:            *)
(*                                       `law_assoc`'s second conjunct  *)
(*                                       and                            *)
(*                                       `law_resume_matches_continuation` *)
(*                                                                     *)
(*  That asymmetry is a finding and not an oversight; the note on       *)
(*  `flat_ops` records it. A purely algebraic law cannot see an algebra *)
(*  that is wrong uniformly, so at least one law must have a right-hand *)
(*  side written in terms of the PLAN rather than in terms of the       *)
(*  operations -- and not all four may, or the laws would say no more   *)
(*  than `ops == ref_ops`.                                             *)
(*                                                                     *)
(*  NEW IN B1.5: every law carries a `settles` hypothesis, and it is    *)
(*  not decoration. Production is a detached run (see `enter_ctx_C`),   *)
(*  so a law about a context built from an arbitrary `c` is false when  *)
(*  `c` performs, before its first pause, an operation the plan does    *)
(*  not handle. `settles` is exactly that condition and nothing wider:  *)
(*  after the first pause the residual is spliced into a live stack and *)
(*  every outward handler is visible again.                             *)
(*                                                                     *)
(*  Two further laws belong to B3. `law_transparent_agrees` below is    *)
(*  one of them and is stated, unproved, because gate condition 6 asks  *)
(*  for it; the other -- plan composition matching handler nesting --   *)
(*  needs the optimized machine that does not exist yet and is not      *)
(*  stated at all.                                                      *)
(* ------------------------------------------------------------------ *)

(** **The side condition every law carries**: production settled. It fails
    exactly when the detached production run got stuck, was rejected, or ran out
    of fuel -- see `enter_ctx_C` for why the restriction exists and why the
    obvious repair is not well defined. Written through `ops` rather than through
    `enter_ctx_C` so that an alternative implementation is judged against its own
    production. *)
let settles
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl) (pl: plan v cl) (c: pcomp v cl)
  : GTot prop
  = ~(PCtxLost? (ops.o_enter_ctx lk apply fuel pl c))

(**
 * **Left identity, at a point.** A context holding just the value `x`, extended
 * by `g`, is entering `g x`.
 *
 * **What it rules out is a second re-entry.** Under `pointwise_ops` the
 * left-hand side crosses the plan twice -- once in the residual, once more
 * around `g x` -- while the right-hand side crosses it once, and for a layer
 * that transforms its answer those differ observably. A point is exactly where
 * that shows up most sharply: there is one value, so any difference between the
 * two sides is a difference in how many times the layers were crossed.
 *
 * It is PURELY ALGEBRAIC -- both sides are built from `ops` alone -- and so it
 * does NOT rule out `flat_ops`, which ignores the plan on both sides equally.
 * That separation is deliberate; see the note on `flat_ops` for why not every
 * law should be anchored.
 *)
let law_left_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: v)
    (g: v -> pcomp v cl)
  : GTot prop
  = settles lk apply fuel ops pl (PVar x) ==>
    pobs_eq lk apply
      (ops.o_extend pl (ops.o_enter_ctx lk apply fuel pl (PVar x)) g)
      (ops.o_enter pl (g x))

(**
 * **Right identity.** Extending by the inner monad's `pure` changes nothing: the
 * layers are crossed exactly as entering would have crossed them, and no layer
 * is crossed a second time on the way.
 *
 * Stated of a context REACHED FROM THE PLAN -- `o_enter_ctx pl c` -- rather than
 * of an arbitrary one, so that the statement stays independent of what a `pctx`
 * is made of. An implementation free to choose its own context representation is
 * still bound by this.
 *
 * It is also the law that will make B2 prove the bridging fact of the whole
 * B1.5 design: the left-hand side runs `c` under `plan_protocol_frames pl` in
 * `MExtend`, the right-hand side under `plan_enter_frames pl`, and the two agree
 * exactly because a `PSiteF` under `MExtend` is nothing at all.
 *)
let law_right_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = settles lk apply fuel ops pl c ==>
    pobs_eq lk apply
      (ops.o_extend pl (ops.o_enter_ctx lk apply fuel pl c) (PVar #v #cl))
      (ops.o_enter pl c)

(**
 * **Associativity of extension.** Two conjuncts, and the second is there because
 * the first was checked against the counterexample and found insufficient.
 *
 * *The algebraic half* quantifies over an ARBITRARY context and compares the
 * CONTEXT PRODUCED by the first extension (`o_extend_ctx`) against the composite
 * function -- not two computations that happen to be built the same way. It is
 * what refuses `pointwise_ops`, the implementation that gives each leaf a fresh
 * crossing of the layers instead of sharing the one the residual has already
 * established: its left-hand side re-enters the layers around `g`'s results and
 * then again around `h`'s, so `h` is applied to values that have already been
 * through the layers' return clauses, while its right-hand side applies `h` to
 * `g`'s values inside a single crossing. For a nondeterministic layer those are
 * `f (f y)` and `f y` -- different branch structure, observably. This is also
 * why `o_extend_ctx` is a field of `ctx_ops` at all: an implementation cannot
 * even state the law without saying what context its extension produced.
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
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (cx: pctx v cl)
    (c: pcomp v cl)
    (g h: v -> pcomp v cl)
  : GTot prop
  = settles lk apply fuel ops pl c ==>
    ( // the algebraic half -- any context, both sides built from `ops` alone
      pobs_eq lk apply
        (ops.o_extend pl (ops.o_extend_ctx pl cx g) h)
        (ops.o_extend pl cx (fun x -> pbind (g x) h))
      /\ // the anchored half -- one crossing of THIS plan, and no other
      pobs_eq lk apply
        (ops.o_extend pl
          (ops.o_extend_ctx pl (ops.o_enter_ctx lk apply fuel pl c) g) h)
        (PSplice (plan_enter_frames pl) (pbind (pbind c g) h)))

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
 *
 * It is also the other half of the bridging fact `law_right_identity` sets up:
 * here the left-hand side runs under `plan_protocol_frames pl` in `MResume` and
 * the right-hand side under `plan_resume_frames pl`, and they agree exactly
 * because a `PSiteF` under `MResume` is the `PBindF` it was recorded from. The
 * two laws together are what forces `plan_protocol_frames` to be both of the
 * other projections and neither of them by itself.
 *)
let law_resume_matches_continuation
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: v)
    (k: v -> pcomp v cl)
  : GTot prop
  = settles lk apply fuel ops pl (PVar x) ==>
    pobs_eq lk apply
      (ops.o_resume pl (ops.o_enter_ctx lk apply fuel pl (PVar x)) k)
      (PSplice (plan_resume_frames pl) (k x))

(**
 * **B3's transparency law, stated here because gate condition 6 asks for it, and
 * UNPROVED.**
 *
 * At a plan whose every layer is transparent, going through the residual is the
 * same computation as entering directly: a transparent layer contributes no
 * context, so there is nothing for the protocol to carry and nothing for the
 * extension to rebuild. This is the statement that ties the classification back
 * to what ships -- `plan_enter_frames` at such a plan is frame-for-frame what
 * `Hoop.Runtime.Semantics.borrow` produces -- and it is exactly the obligation
 * B1's note on the withdrawn `pctx` warned would not come for free.
 *
 * It comes closer to free under the residual than it did under the suspension:
 * the suspension re-ran the inner computation at every operation, so even a
 * transparent plan paid a replay, whereas here the residual is produced once and
 * the extension merely drains it. `fixture_6_transparent` checks the instance;
 * the quantified statement is B3's and nothing in this file depends on it.
 *)
let law_transparent_agrees
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl) (fuel: nat)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = settles lk apply fuel ops pl c ==>
    pobs_eq lk apply
      (ops.o_extend pl (ops.o_enter_ctx lk apply fuel pl c) (PVar #v #cl))
      (PSplice (plan_enter_frames pl) c)

(* ------------------------------------------------------------------ *)
(*  FIXTURES -- the nine gate conditions, CHECKED                      *)
(*                                                                     *)
(*  Every claim below is an `assert_norm` over a concrete run, not a    *)
(*  comment. The value and clause types are the prototype's `v` and     *)
(*  `cl` instantiated at something computable, exactly as               *)
(*  `Hoop.Runtime.Test` does for the shipped machine.                   *)
(*                                                                     *)
(*  ONE FIXTURE-SIDE RESTRICTION, recorded so that nobody reads more    *)
(*  into these runs than they say. `flook` ignores its `handlers`       *)
(*  argument -- it cannot do otherwise, since `handlers` is abstract    *)
(*  and there is no way to tell two of them apart from outside          *)
(*  `Hoop.Runtime.Handlers`. So every prompt in a fixture dispatches    *)
(*  the same operations, and a fixture that needs a particular prompt   *)
(*  to handle a particular operation arranges for that prompt to be the *)
(*  innermost one at the point of the perform. That is a property of    *)
(*  the fixtures, not of the machine.                                   *)
(* ------------------------------------------------------------------ *)

type fv =
  | FU
  | FI: int -> fv
  | FS: string -> fv
  | FL: list fv -> fv

(** The clause language the fixtures run with. Real clauses are opaque
    PureScript closures; these are the four shapes the nine conditions need --
    tail-resumptive, multi-shot, discarding, and the two that make a decision
    AFTER a round trip. *)
noeq
type fcl =
  | FEcho                        (* resume with payload[0] -- tail-resumptive   *)
  | FTwice: fv -> fv -> fcl      (* resume twice, collect both answers          *)
  | FAbort: fv -> fcl            (* never resume -- the `Full` shape            *)
  | FRetry                       (* resume again only if the first answer says  *)
  | FBetween                     (* resume, perform, resume                     *)

let fneeds_retry (x: fv) : bool = match x with | FS "retry" -> true | _ -> false

let fapply : papply_t fv fcl = fun c payload k ->
  match c with
  | FEcho -> (match payload with | x :: _ -> k x | [] -> k FU)
  | FTwice a b -> POp (k a) (fun r1 -> POp (k b) (fun r2 -> PVar (FL [r1; r2])))
  | FAbort z -> PVar z
  | FRetry ->
    POp (k (FS "go1")) (fun r1 ->
      if fneeds_retry r1
      then POp (k (FS "go2")) (fun r2 -> PVar (FL [FS "twice"; r1; r2]))
      else PVar (FL [FS "once"; r1]))
  | FBetween ->
    POp (k (FS "b1")) (fun r1 ->
      POp (PPerform "T" "mark" [FS "mid"]) (fun m ->
        POp (k (FS "b2")) (fun r2 -> PVar (FL [r1; m; r2]))))

let fclause (c: fcl) : found_clause fcl = { body = c; kind = KFull }

let flook : plookup_t fcl = fun _ eff _ ->
  match eff with
  | "Two" -> Some (fclause (FTwice (FS "a") (FS "b")))
  | "Abort" -> Some (fclause (FAbort (FS "aborted")))
  | "Retry" -> Some (fclause FRetry)
  | "Betw" -> Some (fclause FBetween)
  | "Echo" -> Some (fclause FEcho)
  | "T" -> Some (fclause FEcho)
  | _ -> None

(** A REAL table, built through `Hoop.Runtime.Handlers.mk_handlers` with the real
    classifier, so that the classification fixture below is a statement about the
    shipped table and not about a stand-in. It is empty, which is the cheapest
    table that is genuinely borrowable. *)
let fhs : handlers fcl = mk_handlers #fcl (fun _ -> KFast) []

let fown_ret : option (fv -> pcomp fv fcl) = Some (fun x -> PVar (FL [FS "own"; x]))
let fowner : powner fv fcl = POwner fhs fown_ret PFamily
let fowner_plain : powner fv fcl = POwner fhs None PFamily
let fsite (x: fv) : pcomp fv fcl = PVar (FL [FS "site1"; x])
let fsite2 (x: fv) : pcomp fv fcl = PVar (FL [FS "site2"; x])
let fk (x: fv) : pcomp fv fcl = PVar (FL [FS "k"; x])

(* The plan shapes. `plan_LB` is the one that matters most: its recorded bind
   frame sits BETWEEN the layer and the owner, which is the interleaving that
   makes the two projections differ and that no post-hoc re-insertion could
   reconstruct. *)
let plan_L : plan fv fcl = Plan [PIReenter fhs None] fowner
let plan_L0 : plan fv fcl = Plan [PIReenter fhs None] fowner_plain
let plan_LB : plan fv fcl = Plan [PIReenter fhs None; PIBind fsite2] fowner
let plan_T : plan fv fcl = Plan [PITransparent fhs] fowner_plain
let plan_M : plan fv fcl =
  Plan [PIBind fsite; PICell "c" (FI 7); PIReenter fhs None; PIBind fsite2; PITransparent fhs]
       fowner

let frun (fuel: nat) (c: pcomp fv fcl) : pstate fv fcl = psteps flook fapply fuel (pload c)
let fresult (s: pstate fv fcl) : option fv = match s with | PDone x -> Some x | _ -> None
let fmk (pl: plan fv fcl) (c: pcomp fv fcl) : pctx fv fcl = enter_ctx_C flook fapply 400 pl c

(* ---- 1 / 8. The protected prefix runs once, and the context is multi-shot
   FROM THE SAVED POINT.

   THE FINDING THIS FIXTURE RECORDS, and it is the reason the condition is not
   checked the way it was posed. This machine is pure. A residual is an immutable
   value, so consuming one twice is not distinguishable, BY ANY OBSERVATION THIS
   FILE CAN MAKE, from re-running a suspension twice: `fixture_1_same_answer`
   below checks that the two representations return the SAME value. Replay
   becomes observable only where an effect escapes the plan, which in the shipped
   JS runtime is every effect and in this machine is none.

   So the claim is made about WORK, and `pcost` is what makes it checkable.
   `body1 n` is a prefix of `n` trivial binds in front of the operation the layer
   handles. Lengthening the prefix by four units costs the residual eight
   transitions -- one copy -- and costs the suspension sixteen -- two. The slope
   is the claim; the intercepts are not, and are not equal (the residual pays a
   small constant for the boundary and mode frames, and at n = 1 it is in fact
   two transitions dearer overall). Reporting the intercept as if it were the
   result would be rounding the answer in the wrong direction. ---- *)

let rec pchain (n: nat) (c: pcomp fv fcl) : Tot (pcomp fv fcl) (decreases n)
  = if n = 0 then c else POp (PVar FU) (fun _ -> pchain (n - 1) c)

let body1 (n: nat) : pcomp fv fcl =
  pchain n (POp (PPerform "Two" "flip" []) (fun x -> PVar (FL [FS "leaf"; x])))

(* The residual route: ONE production, then two consumptions of the SAME
   context -- an extension whose answer the program observes, and then a
   resumption. This is `runScope` followed by `resumeScope`. *)
let prog1new (n: nat) : pcomp fv fcl =
  let cx = fmk plan_L (body1 n) in
  POp (extend_C plan_L cx (PVar #fv #fcl)) (fun _ -> resume_C plan_L cx fk)

(* The withdrawn route: the same two consumptions of the same unrun computation,
   which is what B1's `PCtx` made them. *)
let prog1old (n: nat) : pcomp fv fcl =
  POp (susp_extend plan_L (body1 n) (PVar #fv #fcl))
      (fun _ -> susp_resume plan_L (body1 n) fk)

let prod1 (n: nat) : pstate fv fcl =
  PStep (body1 n) (PBoundaryF :: plan_protocol_frames plan_L)

(* Production is part of the residual route's bill and is counted with it. *)
let cost_new (n: nat) : option nat =
  match pcost flook fapply 4000 (prod1 n), pcost flook fapply 4000 (pload (prog1new n)) with
  | Some a, Some b -> Some (a + b)
  | _ -> None

let cost_old (n: nat) : option nat = pcost flook fapply 4000 (pload (prog1old n))

let fixture_1_same_answer () : Lemma
  (ensures fresult (frun 4000 (prog1new 1)) == fresult (frun 4000 (prog1old 1)))
  = assert_norm (fresult (frun 4000 (prog1new 1))
                 == Some (FL [FS "own";
                              FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                  FL [FS "k"; FL [FS "leaf"; FS "b"]]]]));
    assert_norm (fresult (frun 4000 (prog1old 1))
                 == Some (FL [FS "own";
                              FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                  FL [FS "k"; FL [FS "leaf"; FS "b"]]]]))

let fixture_1_prefix_runs_once () : Lemma
  (ensures (match cost_new 1, cost_new 5, cost_old 1, cost_old 5 with
            | Some a, Some b, Some c, Some d ->
              b - a == 8 /\ d - c == 16 /\ d - c == 2 * (b - a)
            | _ -> False))
  = assert_norm (cost_new 1 == Some 43);
    assert_norm (cost_new 5 == Some 51);
    assert_norm (cost_old 1 == Some 41);
    assert_norm (cost_old 5 == Some 57)

(* ---- 2. `firstOfTwo`: a clause that resumes twice produces two requests, in
   order. The first request is what production paused on; the second happens
   because the layer resumed its own captured continuation, which carries the
   boundary frame with it. The consumer's `fk` runs at each, and the layer
   assembles them in the order they arrived. ---- *)

let body2 : pcomp fv fcl =
  POp (PPerform "Two" "flip" []) (fun x -> PVar (FL [FS "leaf"; x]))

let cx2 : pctx fv fcl = fmk plan_L body2
let prog2 : pcomp fv fcl = resume_C plan_L cx2 fk

let fixture_2_two_requests () : Lemma
  (ensures fresult (frun 400 prog2)
           == Some (FL [FS "own";
                        FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                            FL [FS "k"; FL [FS "leaf"; FS "b"]]]]))
  = assert_norm (PCtxRequests? cx2);
    assert_norm (fresult (frun 400 prog2)
                 == Some (FL [FS "own";
                              FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                  FL [FS "k"; FL [FS "leaf"; FS "b"]]]]))

(* ---- 3. `retryOnFailure`: the second resume exists only because of the first
   resume's REAL answer.

   `FRetry` resumes once, INSPECTS what came back, and resumes a second time only
   if it was `"retry"`. What comes back is a full round trip: the scope reached
   the boundary, the consumer's function ran, and the value returned through the
   layer prompt. The two runs below differ in nothing but that answer, and they
   differ in how many resumptions happened -- which is the property a precomputed
   list of leaves cannot have, and the reason that representation was rejected
   before B1.5 began. ---- *)

let body3 : pcomp fv fcl = POp (PPerform "Retry" "step" []) (fun x -> PVar x)
let prog3a : pcomp fv fcl = resume_C plan_L (fmk plan_L body3) (fun _ -> PVar (FS "retry"))
let prog3b : pcomp fv fcl = resume_C plan_L (fmk plan_L body3) (fun _ -> PVar (FS "stop"))

let fixture_3_retry_on_failure () : Lemma
  (ensures fresult (frun 400 prog3a)
             == Some (FL [FS "own"; FL [FS "twice"; FS "retry"; FS "retry"]])
        /\ fresult (frun 400 prog3b)
             == Some (FL [FS "own"; FL [FS "once"; FS "stop"]]))
  = assert_norm (fresult (frun 400 prog3a)
                 == Some (FL [FS "own"; FL [FS "twice"; FS "retry"; FS "retry"]]));
    assert_norm (fresult (frun 400 prog3b)
                 == Some (FL [FS "own"; FL [FS "once"; FS "stop"]]))

(* ---- 4. Effects performed BETWEEN two resumes keep their order.

   `FBetween` resumes, then performs `T.mark` from inside its own body -- below
   the layer prompt, so the owner dispatches it -- then resumes again, and
   assembles the three results positionally. The assembled list is the trace, and
   `"mid"` sits between the two answers rather than before or after both. ---- *)

let body4 : pcomp fv fcl = POp (PPerform "Betw" "go" []) (fun x -> PVar (FL [FS "leaf"; x]))
let prog4 : pcomp fv fcl = resume_C plan_L0 (fmk plan_L0 body4) fk

let fixture_4_effect_between_resumes () : Lemma
  (ensures fresult (frun 400 prog4)
           == Some (FL [FL [FS "k"; FL [FS "leaf"; FS "b1"]];
                        FS "mid";
                        FL [FS "k"; FL [FS "leaf"; FS "b2"]]]))
  = assert_norm (fresult (frun 400 prog4)
                 == Some (FL [FL [FS "k"; FL [FS "leaf"; FS "b1"]];
                              FS "mid";
                              FL [FS "k"; FL [FS "leaf"; FS "b2"]]]))

(* ---- 5. A `Full`-style clause that never calls its continuation terminates
   correctly.

   `FAbort` discards the continuation, so the scope never reaches the boundary
   and the protocol never asks for anything. At `plan_L` the layer's answer
   drains through the owner and the context is `PCtxDone`; consuming it returns
   that answer and applies nothing. This is the case B1's note said would
   otherwise have needed a "no values to return" branch, and there is none. ---- *)

let body5 : pcomp fv fcl = POp (PPerform "Abort" "x" []) (fun x -> PVar (FL [FS "leaf"; x]))
let cx5 : pctx fv fcl = fmk plan_L body5
let prog5 : pcomp fv fcl = resume_C plan_L cx5 fk

let fixture_5_never_resumes () : Lemma
  (ensures fresult (frun 400 prog5) == Some (FL [FS "own"; FS "aborted"]))
  = assert_norm (PCtxDone? cx5);
    assert_norm (fresult (frun 400 prog5) == Some (FL [FS "own"; FS "aborted"]))

(* ---- 5b. THE SAME CLAUSE, at a plan whose recorded bind frame lies between the
   layer and the owner -- and the fixture that shows the two consuming operations
   are still two.

   Production drains as before, but now it meets a `PSiteF` on the way out and
   PAUSES there, because whether a perform-site bind fires is not production's
   question. ONE residual is then consumed both ways: `resume_C` fires the site
   frame and `extend_C` does not, so the answers differ. Under any representation
   that had committed to a projection at production time, one of these two would
   have been unavailable. ---- *)

let cx5b : pctx fv fcl = fmk plan_LB body5
let prog5b_resume : pcomp fv fcl = resume_C plan_LB cx5b fk
let prog5b_extend : pcomp fv fcl = extend_C plan_LB cx5b fk

let fixture_5b_never_resumes_with_bind () : Lemma
  (ensures fresult (frun 400 prog5b_resume)
             == Some (FL [FS "own"; FL [FS "site2"; FS "aborted"]])
        /\ fresult (frun 400 prog5b_extend)
             == Some (FL [FS "own"; FS "aborted"])
        /\ fresult (frun 400 prog5b_resume) =!= fresult (frun 400 prog5b_extend))
  = assert_norm (PCtxRequests? cx5b);
    assert_norm (fresult (frun 400 prog5b_resume)
                 == Some (FL [FS "own"; FL [FS "site2"; FS "aborted"]]));
    assert_norm (fresult (frun 400 prog5b_extend)
                 == Some (FL [FS "own"; FS "aborted"]))

(* ---- 6. A transparent plan agrees with the borrow.

   Two checks, and neither is the quantified statement -- that is
   `law_transparent_agrees`, and it is B3's.

   The first is structural: the frames a transparent item contributes are
   `PPromptF hs None PMono`, which is frame for frame what
   `Hoop.Runtime.Semantics.borrow` produces for a borrowable prompt, and the same
   in all three projections -- a transparent layer has no bind frame to defer, so
   the three agree. The equality across the two ASTs cannot be written here
   (`borrow` is over `comp_tree`, this is over `pcomp`) and is B3's to state.

   The second is observational at an instance: `enter_C` on a concrete program
   and the residual-driven extension of the same program converge to the same
   value.

   The classification is checked on a REAL table rather than on a hand-built
   `PITransparent`: `fhs` goes through `mk_handlers` with the real classifier,
   and `classify_prompt PMono fhs None` really is `ContextTransparent`. ---- *)

let body6 : pcomp fv fcl =
  POp (PPerform "Echo" "e" [FS "v"]) (fun x -> PVar (FL [FS "leaf"; x]))
let prog6_enter : pcomp fv fcl = enter_C plan_T body6
let prog6_residual : pcomp fv fcl = extend_C plan_T (fmk plan_T body6) (PVar #fv #fcl)

let fixture_6_transparent_classification () : Lemma
  (ensures classify_prompt #fv #fcl PMono fhs None == ContextTransparent)
  = assert (Nil? (blocking_effects fhs))

let fixture_6_transparent () : Lemma
  (ensures plan_enter_frames plan_T
             == [PPromptF fhs None PMono; PPromptF fhs None PFamily]
        /\ plan_resume_frames plan_T == plan_enter_frames plan_T
        /\ plan_protocol_frames plan_T == plan_enter_frames plan_T
        /\ fresult (frun 400 prog6_enter) == fresult (frun 400 prog6_residual))
  = assert_norm (plan_enter_frames plan_T
                 == [PPromptF fhs None PMono; PPromptF fhs None PFamily]);
    assert_norm (plan_resume_frames plan_T
                 == [PPromptF fhs None PMono; PPromptF fhs None PFamily]);
    assert_norm (plan_protocol_frames plan_T
                 == [PPromptF fhs None PMono; PPromptF fhs None PFamily]);
    assert_norm (fresult (frun 400 prog6_enter) == Some (FL [FS "leaf"; FS "v"]));
    assert_norm (fresult (frun 400 prog6_residual) == Some (FL [FS "leaf"; FS "v"]))

(* ---- 7. A mixed plan preserves prompt / cell / bind ORDER.

   `plan_M` is `[bind, cell, family, bind, transparent]` over an owner, which is
   an ordinary stack and is deliberately not uniform in any of the three
   dimensions. Structurally, each of the three projections is the plan in place,
   with the bind frames dropped, kept, or deferred; nothing is reordered, and no
   projection could reorder without naming `rev`.

   Observably, the resumed answer is
   `own(site2([site1(k(7, a)); site1(k(7, b))]))`. Read it outwards: the cell was
   readable inside the scope and held 7, the INNER bind fired once per leaf and
   inside the layer, the layer assembled the two, the OUTER bind fired once on
   the assembled answer, and the owner's answer former ran last and exactly once.
   That is the interleaving, and it is why a residual that had dropped the binds
   could not have had them put back: there is no position in the layer's own
   captured continuation at which `site2` could have been reinserted after the
   fact.

   The same context extended instead of resumed is `own([k(7, a); k(7, b)])` --
   no site frames at all, and the layer and owner untouched. ---- *)

let body7 : pcomp fv fcl =
  POp (PReadP "c") (fun cv -> POp (PPerform "Two" "flip" []) (fun x -> PVar (FL [cv; x])))
let cx7 : pctx fv fcl = fmk plan_M body7
let prog7_resume : pcomp fv fcl = resume_C plan_M cx7 fk
let prog7_extend : pcomp fv fcl = extend_C plan_M cx7 fk

let fixture_7_mixed_order_frames () : Lemma
  (ensures plan_enter_frames plan_M
             == [PParamF "c" (FI 7);
                 PPromptF fhs None PFamily;
                 PPromptF fhs None PMono;
                 PPromptF fhs fown_ret PFamily]
        /\ plan_resume_frames plan_M
             == [PBindF fsite;
                 PParamF "c" (FI 7);
                 PPromptF fhs None PFamily;
                 PBindF fsite2;
                 PPromptF fhs None PMono;
                 PPromptF fhs fown_ret PFamily]
        /\ plan_protocol_frames plan_M
             == [PSiteF fsite;
                 PParamF "c" (FI 7);
                 PPromptF fhs None PFamily;
                 PSiteF fsite2;
                 PPromptF fhs None PMono;
                 PPromptF fhs fown_ret PFamily])
  = assert_norm (plan_enter_frames plan_M
                 == [PParamF "c" (FI 7);
                     PPromptF fhs None PFamily;
                     PPromptF fhs None PMono;
                     PPromptF fhs fown_ret PFamily]);
    assert_norm (plan_resume_frames plan_M
                 == [PBindF fsite;
                     PParamF "c" (FI 7);
                     PPromptF fhs None PFamily;
                     PBindF fsite2;
                     PPromptF fhs None PMono;
                     PPromptF fhs fown_ret PFamily]);
    assert_norm (plan_protocol_frames plan_M
                 == [PSiteF fsite;
                     PParamF "c" (FI 7);
                     PPromptF fhs None PFamily;
                     PSiteF fsite2;
                     PPromptF fhs None PMono;
                     PPromptF fhs fown_ret PFamily])

let fixture_7_mixed_order () : Lemma
  (ensures fresult (frun 400 prog7_resume)
             == Some (FL [FS "own";
                          FL [FS "site2";
                              FL [FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "a"]]];
                                  FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "b"]]]]]])
        /\ fresult (frun 400 prog7_extend)
             == Some (FL [FS "own";
                          FL [FL [FS "k"; FL [FI 7; FS "a"]];
                              FL [FS "k"; FL [FI 7; FS "b"]]]]))
  = assert_norm (fresult (frun 400 prog7_resume)
                 == Some (FL [FS "own";
                              FL [FS "site2";
                                  FL [FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "a"]]];
                                      FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "b"]]]]]]));
    assert_norm (fresult (frun 400 prog7_extend)
                 == Some (FL [FS "own";
                              FL [FL [FS "k"; FL [FI 7; FS "a"]];
                                  FL [FS "k"; FL [FI 7; FS "b"]]]]))

(* ---- 8. A context resumed more than once is multi-shot FROM THE SAVED POINT.

   `cx8` is produced once. The program below drives it twice -- once as an
   extension and once as a resumption -- and pairs the answers. Both consumptions
   see the layer's two branches; the resumption additionally fires the recorded
   bind frame and the extension does not. The prefix was run by production alone:
   that half of the claim is `fixture_1_prefix_runs_once`, whose `prog1new` is
   this same shape, and it is a claim about cost for the reason recorded
   there. ---- *)

let body8 : pcomp fv fcl =
  POp (PPerform "Two" "flip" []) (fun x -> PVar (FL [FS "leaf"; x]))
let cx8 : pctx fv fcl = fmk plan_LB body8
let prog8 : pcomp fv fcl =
  POp (extend_C plan_LB cx8 fk) (fun a ->
    POp (resume_C plan_LB cx8 fk) (fun b -> PVar (FL [a; b])))

let fixture_8_multi_shot () : Lemma
  (ensures fresult (frun 800 prog8)
           == Some (FL [FL [FS "own";
                            FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                FL [FS "k"; FL [FS "leaf"; FS "b"]]]];
                        FL [FS "own";
                            FL [FS "site2";
                                FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                    FL [FS "k"; FL [FS "leaf"; FS "b"]]]]]]))
  = assert_norm (fresult (frun 800 prog8)
                 == Some (FL [FL [FS "own";
                                  FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                      FL [FS "k"; FL [FS "leaf"; FS "b"]]]];
                              FL [FS "own";
                                  FL [FS "site2";
                                      FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                                          FL [FS "k"; FL [FS "leaf"; FS "b"]]]]]]))

(* ---- 9. No clause-inspecting mechanism, and no assumption about `apply`.

   This one is a property of the design and not a run, so it is stated where it
   is respected rather than fabricated as a fixture:

     - `papply_t` and its note: a clause is opaque, and the machine's only
       interaction with one is to hand it a payload and a continuation.
     - `pstep`: no rule matches on a clause, and the protocol is built entirely
       from frames the machine pushed -- `PBoundaryF`, `PSiteF`, `PModeF` -- so a
       layer reaches the boundary only by resuming, through the ordinary
       `PSplice` rule, the continuation it was given.
     - `enter_ctx_C`: production RUNS the inner computation and never reads it.

   The fixtures above are the evidence that this is not vacuous: `FEcho`,
   `FTwice`, `FAbort`, `FRetry` and `FBetween` resume once, twice, never, and
   conditionally, and the protocol is the same protocol in every case, with no
   rule anywhere asking which of them it is looking at. ---- *)
