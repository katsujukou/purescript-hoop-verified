(**
 * **B1.7 -- the general weave, over a RESIDUAL CONFIGURATION, with production as
 * a MACHINE TRANSITION and the context as a FIRST-CLASS PERSISTENT HANDLE.**
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
 * ===========================================================================
 * **WHAT B1.6 CHANGED: PRODUCTION IS A TRANSITION.**
 *
 * B1.5 produced a context with a meta-level function:
 *
 * ```fstar
 * enter_ctx_C lk apply fuel pl c
 *   = pctx_of_state PVar (psteps lk apply fuel (PStep c (PBoundaryF :: plan_protocol_frames pl)))
 * ```
 *
 * -- a lookup, a clause interpreter and a fuel bound in, a finished `pctx` out,
 * the whole run on an EMPTY ambient stack. The gate's stop condition names that
 * shape and refuses it, on a reading of the TYPE and before any behaviour is
 * considered: an operation that has to be handed the interpreter is an operation
 * that runs the program, which makes it a test-harness partial evaluator exposed
 * through the interface rather than a semantic operation. Everything that
 * followed from it followed from that: an operation the prefix performed that no
 * plan prompt handled became `PStuck` where the real machine would have carried
 * it outward to an enclosing handler, and every law therefore carried a
 * `settles` hypothesis saying that this had not happened.
 *
 * **The stop condition did not fire.** Production is now the node `PEnterCtx`,
 * whose rule pushes four things onto the LIVE stack -- the boundary marker, the
 * plan's protocol frames, a new frame `PScopeF` (the SCOPE FLOOR), and then
 * whatever was already there, untouched. The token is formed by a value rule,
 * which cuts the stack at the floor: everything above is the residual,
 * everything below is where the machine goes on running. Neither the production
 * primitive nor any of the four consuming operations mentions `psteps`, `pcost`,
 * `papply_t`, `plookup_t` or a fuel; every field of `ctx_ops` is a single
 * constructor application, and `ctx_ops` no longer mentions `pctx` at all.
 *
 * **What the live stack buys, and it is the substance of the gate.** An
 * operation the prefix performs that no plan prompt handles is found by the
 * ordinary `pfind_prompt` walk, which continues past the owner and PAST THE
 * FLOOR into the ambient stack. The segment an ambient handler captures
 * therefore contains the whole scope, so when it resumes -- even if it is not
 * tail-resumptive, even if it has pending frames of its own -- the scope is
 * re-installed ABOVE that handler's unfinished work, and the token, when it is
 * finally produced, is handed to a continuation running on top of it.
 * `fixture_10_outer_handler` computes `wrap(outer-ret(own(k(outer-ans, v))))`:
 * the ambient clause's pending bind and the ambient prompt's answer
 * transformation both survive, wrapped around the scope's own answer.
 * `fixture_10_detached_gets_stuck` is the control -- B1.5's production, kept
 * executable, gets `PStuck "Out" "o"` on the same body. That is exactly what
 * `settles` was hiding, and `settles` is gone.
 *
 * **The design obstacle, and the finding it produced.** A token has to reach the
 * continuation. It cannot be a `v` -- `v` is abstract. The two candidates were a
 * continuation `kf: pctx v cl -> pcomp v cl` on the production node, and the
 * larger restructure that makes the machine's value position a sum,
 * `pvalue v cl = PV of v | PCtxV of pctx v cl`. **NEITHER IS WELL FORMED.** A
 * `pctx` holds a residual of frames and an extension chain `v -> pcomp v cl`, so
 * it contains a NEGATIVE occurrence of the value type (as well as positive
 * ones). Embedding it directly into the value language closes a negative
 * recursive cycle, and F* answers "does not satisfy the strict positivity
 * condition" for both shapes. That DIRECT recursive sum cannot be written; B1.7
 * tests the stratified handle-and-store representation that avoids the cycle.
 *
 * B1.6 answered this by DEFUNCTIONALISING the token: production installed it in
 * a `PTokenF` frame beneath the continuation and the consuming nodes read the
 * nearest one, exactly as `PReadP` reads the nearest cell. A produced context
 * was therefore DYNAMICALLY SCOPED, which is not adequate for the published
 * `ScopeTactics` -- their explicit `ctx x` argument lets a clause select among
 * several live contexts, and the nearest-token reading would run such a program
 * with a different meaning.
 *
 * **B1.7 replaces that last step, and the whole of it is a STRATIFICATION.**
 * The value language becomes
 *
 *     pval v = PV of v | PCtxKey of nat
 *
 * -- and a `nat` is not recursive, so `pval` needs no mention of `pctx`, so it
 * leaves the mutual block, so `pctx` (which holds `pval v -> pcomp v cl`) can
 * sit OUTSIDE the block, so a store `list (nat & pctx v cl)` can be given a
 * type. The negative occurrence is still there and is still fatal to a DIRECT
 * embedding; what the key buys is that the cycle is never closed. Condition 6 is
 * satisfied in this precise sense, and in no wider one.
 *
 * The store and an allocation counter live beside the machine state in a
 * `pconf`. `PTokenF` and `pfind_token` are DELETED: no function in this module
 * takes a stack and returns a context. Production allocates and evaluates to
 * `PCtxKey i`; the three consuming nodes each take a `pval v` and RESOLVE it
 * against the store, failing if it does not resolve. Several contexts can now be
 * alive at once and be named separately, which is what B1.6's dynamic token
 * could not do: `fixture_16` returns a handle as a program's own answer,
 * `fixture_17` keeps two alive at once, and `fixture_18` selects the outer one
 * while the inner is live.
 *
 * **What is NOT checked**, and the boundary is the model's rather than the
 * design's: whether a REAL handle can be put into a container and taken out
 * again. `fixture_17` renders each handle with `fseen` before it builds a list,
 * because the shallow `pval = PV v | PCtxKey nat` has no way to say what it
 * means to combine two things that might be handles. Establishing container
 * storage of live handles needs a different value model.
 *
 * **Exact-once stopped being a claim about transition counts.** B1.5 could only
 * state it as work, because the machine is pure and `pobs_eq` observes values: a
 * replayed prefix returns what it returned before. B1.6 adds `PEmit` and a
 * driver `prun` that accumulates a trace OUTSIDE the value language, so
 * `fixture_11_prefix_event_once` checks that one production and two consumptions
 * emit `["prefix"]` when the consumers are silent and `["prefix"; "c1"; "c2"]`
 * when they are not, while `fixture_12_suspension_emits_twice` checks that the
 * withdrawn suspension emits `["prefix"; "c1"; "prefix"; "c2"]` on the same body.
 * The trace is the driver's second result and is not part of a state, a frame or
 * a `pctx`, so "not preserved into the residual" holds by the type of a residual
 * and not by an inspection of one. `fixture_1_prefix_runs_once` survives, demoted
 * to a performance and structure regression test; requirement 3 is the semantic
 * statement.
 * ===========================================================================
 *
 * *What this module is.* A small machine, not a copy of the production one. It
 * holds only what the general weave needs: prompt provenance, the classification
 * derived from it, the scope PLAN a captured segment is turned into, the context
 * operations over that plan, a step relation that covers them, the laws they owe
 * -- **stated, not proved** -- and executable fixtures for the conditions the
 * gates ask about. Clarity over efficiency throughout, and no optimization pass
 * at all: the transparent case here is part of the general path and is NOT yet a
 * fast path. Making it one, and proving the two agree, is B3.
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
 * *B1.5's nine conditions, as this file leaves them.* Each is a fixture at the
 * bottom, run at a definite fuel and checked by `assert_norm` -- never by a
 * comment claiming a result. Every production in them is IN THE OBJECT LANGUAGE:
 * B1.5 wrote `let cx = fmk pl body` and used `cx` twice, which asks F*'s
 * normaliser what the answer should be rather than asking the machine, and there
 * is no `fmk` any more because there cannot be one.
 *
 *   1. prefix runs exactly once -- **PASSED, and now as an OBSERVATION**; see
 *      requirement 3 below. `fixture_1_prefix_runs_once` remains as a
 *      performance / structure regression test that prefix work is shared.
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
 *      produces, and checks that `enter_C` and the residual-driven extension
 *      converge to the same value on a concrete program. The quantified
 *      statement is `law_transparent_agrees` and it is B3's, unproved.
 *   7. a mixed plan preserves prompt / cell / bind ORDER -- PASSED
 *      (`fixture_7_mixed_order`, structurally on all three projections and then
 *      observably on a run).
 *   8. multi-shot FROM THE SAVED POINT -- PASSED (`fixture_8_multi_shot`,
 *      `fixture_8b_extend_then_resume`).
 *   9. no clause-inspecting mechanism, no assumption about `apply` -- a property
 *      of the design; where it is respected is stated at `pstep` and at
 *      `enter_ctx_C`, and `fixture_9_paused_is_unreachable` /
 *      `fixture_9_consumer_without_token` are the two parts of it that are runs.
 *
 * *B1.6's own eight, in the same form.*
 *
 *   1. a trace not preserved into the residual -- PASSED, by the TYPE of `prun`
 *      (the trace is the driver's second result) and exhibited by
 *      `fixture_11_prefix_event_once`'s silent run, whose whole trace after two
 *      consumptions is `["prefix"]`.
 *   2. one observation event in the protected prefix -- PASSED (`body_e`).
 *   3. consuming the residual twice yields it ONCE -- PASSED
 *      (`fixture_11_prefix_event_once`, and `fixture_13_multi_shot_trace` for a
 *      layer that resumes twice).
 *   4. the suspension yields it TWICE -- PASSED
 *      (`fixture_12_suspension_emits_twice`, the control).
 *   5. an operation the plan does not handle is handled outside the owner --
 *      PASSED (`fixture_10_outer_handler`, with
 *      `fixture_10_detached_gets_stuck` as the B1.5 control).
 *   6. that handler's pending binds and answer transformation are not lost --
 *      PASSED (same fixture; both appear in the answer, outside the scope's).
 *   7. `settles` off the laws -- DONE. It is deleted, not weakened; the argument
 *      that it may go is at the laws' preamble and is STATED, NOT PROVED.
 *   8. production initiated by an object-language transition -- PASSED; the
 *      check is mechanical and is described at `enter_ctx_C`.
 *
 * *B1.7's eight, which are about IDENTITY rather than about production.*
 *
 *   1. production returns an opaque handle as an object-language value, once --
 *      PASSED (`fixture_16_handle_is_a_value`: the handle IS the program's
 *      answer, the store holds one entry, `next` is 1).
 *   2. two contexts alive at the same time -- PASSED
 *      (`fixture_17_two_contexts_alive`: both alive at once and different --
 *      but RENDERED with `fseen`, so container storage of live handles is not
 *      what this checks; see the fixture).
 *   3. an outer context selected explicitly while an inner one is live -- PASSED
 *      (`fixture_18_handle_not_nearness`).
 *   4. what is consumed is decided by the HANDLE PASSED, not by nearness --
 *      PASSED (`fixture_18_handle_not_nearness`: two programs differing in one
 *      variable at the same point in the same stack, with different answers).
 *   5. B1.6's fixtures still hold -- PASSED; fixtures 1 to 15 are unchanged in
 *      intent and rewritten only into the handle shape, which made several of
 *      them STRONGER: `fixture_1`, `fixture_5b`, `fixture_7` and `fixture_8` now
 *      name ONE handle twice, where B1.6 could only consume "the context in
 *      scope" twice and argue that both found the same token.
 *   6. strict positivity WITHOUT a direct recursive embedding -- PASSED; see the
 *      stratification above. F* checks it by accepting these declarations, and
 *      the rejection of the direct shapes was re-confirmed in a scratch module.
 *   7. store integrity -- PASSED (`fixture_19_forged_handle_fails`: a forged
 *      handle and a non-handle value both get `PStuck`, and the store holds a
 *      real, resolvable context at the time, so the refusal is not for want of
 *      something to fall back on). `presolve` is not GIVEN a stack, so the
 *      fallback is impossible by type and not only by behaviour.
 *   8. persistence and aliasing -- PASSED
 *      (`fixture_20_persistence_and_aliasing`: `cy1 <- bindScope cx g;
 *      cy2 <- bindScope cx h` gives three independent contexts, `cx` carries
 *      neither extension, and consuming the three in either order agrees).
 *
 * *The multi-shot allocation hazard*, which none of the eight names and which no
 * single-path fixture would catch: `next` lives in the `pconf`, and a `pconf` is
 * not a frame, so nothing about it is captured by `PSplice` or restored by a
 * resumption. `fixture_21_multi_shot_alloc` produces a context inside a
 * TWICE-RESUMED continuation, checks that the two branches got different keys,
 * and consumes both afterwards to check each resolves to its own branch's body.
 * The store is GLOBAL and MONOTONE across capture and resumption. The scheme
 * this rules out is the NAIVE snapshot -- one taken per continuation and
 * restored on resumption -- which would make an extension performed in one
 * resumption invisible to its sibling, and which solves neither collision
 * between independent allocators nor lost updates. It is not a claim that no
 * snapshot scheme could work; a scheme that solved those two is not excluded by
 * anything checked here. Global-and-monotone is the REFERENCE choice, adopted so
 * that handles created in sibling resumptions resolve together afterwards.
 *
 * *What this file states rather than proves, listed here so that no reader has
 * to find them.*
 *
 *   - The four laws, plus `law_transparent_agrees`, are unproved. They are
 *     `prop` definitions parameterised by a `ctx_ops`; B2b is to prove them of
 *     `ref_ops`. Nothing in this module depends on any of them holding.
 *   - `settles` is DELETED, and what that establishes is that the laws can be
 *     STATED without it -- together with `fixture_10_outer_handler`, which runs
 *     the program `settles` used to exclude. Whether the propositions so stated
 *     HOLD of `ref_ops` is the same B2b obligation as the line above, not a
 *     separate open question about the hypothesis.
 *   - ~~`pfind_mode`'s and `pcut_scope`'s nearness are CHOSEN, not checked.~~
 *     **B2a strand 1 closed both, and they move out of this list.** The
 *     invariant is `presid_wf`; `lemma_pyield_residual_wf` proves production
 *     establishes it and `lemma_ctx_drive_answers_head` proves consumption
 *     depends on it, and the farthest cut makes the second FALSE rather than
 *     merely unproved (`guard_far_drive_reyields` runs both and they disagree
 *     about the answer). Proximity is a SEMANTIC REQUIREMENT here. What is NOT
 *     proved, and is handed to strand 2, is the configuration-wide statement
 *     that every stack the machine can reach from `pload` is well bracketed;
 *     nothing above needs it, because the hypotheses used are branch conditions
 *     of `pstep` rather than facts about reachable stacks.
 *   - `PCtxRequests y [] PVar` for `PCtxDone y` is likewise still ACCEPTED,
 *     re-tested in B1.7. The two are operationally equal -- driving a request
 *     with an empty residual pushes a `PModeF` that the value then passes
 *     straight through, so the extension chain is never applied -- and the
 *     constructors are kept apart for the reader.
 *   - **The store is never reclaimed.** `palloc` only conses and nothing removes
 *     an entry, so a handle stays resolvable for the whole run. That is what
 *     makes condition 8 hold; whether a real implementation may reclaim is an
 *     optimisation with an obligation, and is not addressed here.
 *   - **`fseen` breaks handle opacity, and only for the fixtures.** No transition
 *     applies it. Condition 1's "opaque" is a statement about the SEMANTICS, and
 *     the fixtures are entitled to look because their job is to report what the
 *     machine did.
 *   - `ptable.binds` is supplied by the fixtures rather than derived from the
 *     shipped table, which is abstract. No transition and no law reads it.
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

(**
 * **A prompt's table, as the prototype carries it** -- new in B1.6, and it is
 * the second and last concession to CHECKABILITY that this file makes.
 *
 * `hs` is the shipped table, unchanged, and it is what the CLASSIFICATION reads:
 * `borrowable` and `blocking_effects` below are applied to this field and to
 * nothing else, so which prompts a scope may cross is still decided by the real
 * table.
 *
 * `binds` is a list of effect labels, and it exists because of a hole B1.5
 * recorded and B1.6 could not work around. `handlers` is abstract in
 * `Hoop.Runtime.Handlers.fsti`; `keys` answers membership through an abstract
 * `keyset`; neither reduces. So a fixture's lookup cannot tell two tables apart,
 * and B1.5 said so plainly: "`flook` ignores its `handlers` argument -- it cannot
 * do otherwise". Under a detached production that was a restriction on how
 * fixtures were written. Under B1.6 it is fatal to requirement 5, whose whole
 * content is that a prompt INSIDE the plan does not handle an operation and a
 * prompt OUTSIDE the owner does: with a table-blind lookup the innermost plan
 * prompt handles everything, and the operation can never reach past the owner.
 *
 * **What this field is and is not.** It is not consulted by the machine. It is
 * not consulted by `pref_lookup`, which is `lookup_handler hs` and ignores it
 * entirely -- so the reference semantics is exactly what it was, and no
 * transition, no projection and no law reads `binds`. It is read by ONE thing:
 * the fixtures' own lookup, which needs to be able to say "this table does not
 * bind that effect" in a form `assert_norm` can compute. The alternative was to
 * model "not handled here" with a FORWARDING clause -- a clause that re-performs
 * the operation below its own prompt -- which exercises the same machine path
 * but is a fiction of a different kind: it makes the plan's prompts handle the
 * operation and hand it on, which is not what requirement 5 asks about. A field
 * the reference ignores was judged the smaller lie than a clause that does
 * something the real one would not.
 *
 * A realisation on the shipping path has no counterpart to `binds` and needs
 * none: `Hoop.Runtime.Machine`'s dispatch reads `lookup_clause` off the real
 * table, which answers exactly this question and answers it correctly.
 *)
noeq
type ptable (cl: Type u#a) : Type u#a = {
  hs: handlers cl;
  binds: list string;
}

(* ------------------------------------------------------------------ *)
(*  The value language -- NEW IN B1.7, AND THE WHOLE OF THE RESTRUCTURE *)
(* ------------------------------------------------------------------ *)

(**
 * **The machine's value position, as a two-case sum**, and the reason B1.7 is a
 * different module from B1.6 rather than an addition to it.
 *
 * B1.6's machine had ONE value type, the abstract parameter `v`, and no way to
 * put a context into it. The two direct repairs -- a field
 * `kf: pctx v cl -> pcomp v cl` on the production node, and a value type
 * `pvalue v cl = PV of v | PCtxV of pctx v cl` -- are both REJECTED BY F*, and
 * the rejection is real rather than conservative: a `pctx` holds an extension
 * chain `pval v -> pcomp v cl`, so it contains a NEGATIVE occurrence of the
 * value type, and embedding it into the value language closes a negative
 * recursive cycle. `[@@strictly_positive]` has nothing to say about it -- that
 * attribute declares that an ABSTRACT parameter is used positively; it cannot
 * make a real negative occurrence acceptable.
 *
 * **What this type does instead is stratify.** The thing that enters the value
 * language is a `nat` -- a KEY, with no recursive structure at all -- and the
 * residual it names lives in a store beside the machine state. Three
 * consequences, and each of them is load-bearing:
 *
 *   - `pval` mentions neither `pcomp` nor `pctx`, so it is NOT part of the
 *     mutual block below. It is defined before it and depends on nothing in it.
 *   - `pframe` therefore no longer has to hold a `pctx` (B1.6's `PTokenF` is
 *     deleted, not weakened), so `pctx` drops out of the mutual block too and is
 *     defined AFTER it. It is the last of the three stratification steps and the
 *     one that makes the store's type expressible.
 *   - a handle is an ordinary value. It can be bound by `POp`, held in a
 *     `PParamF` cell, put in a payload, returned from a scope, and -- the point
 *     of the gate -- SELECTED between. Which context an operation consumes is an
 *     argument, not a position on the stack.
 *
 * **`PCtxKey` is opaque TO THE MACHINE, which is the sense that matters.** No
 * transition below matches on the `nat`, compares two of them, or does
 * arithmetic on one; the only thing any rule does with a `PCtxKey` is hand it to
 * `presolve`, and the only thing that MAKES one is the allocator. The fixtures'
 * own value type can render a key (see `fd`), because a fixture has to be able
 * to write down a FORGED handle in order to check that forging fails -- but the
 * machine has no rule that could act on the difference.
 *
 * The key is a `nat` and not a `string`: a name supplied from the surface could
 * collide, and the freshness argument below (`lemma_alloc_fresh`) would have
 * nothing to be about.
 *)
noeq
type pval (v: Type u#a) : Type u#a =
  | PV: value:v -> pval v
  | PCtxKey: id:nat -> pval v

(* ------------------------------------------------------------------ *)
(*  The prototype AST                                                  *)
(*                                                                     *)
(*  `Hoop.Runtime.Syntax.comp_tree` / `frame` with provenance on the    *)
(*  prompt, with the context operations given nodes of their own, with  *)
(*  the three frames B1.5's residual protocol is made of, and -- new in *)
(*  B1.6 -- with production's node and the frame it needs. Every        *)
(*  constructor is renamed (`P...`) so that nothing here shadows the    *)
(*  production type: a prototype that could be confused for the shipped *)
(*  AST at a call site is a prototype that will be, and                 *)
(*  `--print_full_names` is not something a reader runs by default.     *)
(*                                                                     *)
(*  The block is mutually recursive and cannot be split: `plan_item`    *)
(*  holds return clauses (`pval v -> pcomp`), the production node holds *)
(*  a `plan`, and a `pframe` holds continuations into `pcomp`.          *)
(*                                                                     *)
(*  `pstate` LEFT the block in B1.6, and `pctx` LEAVES IT IN B1.7. The  *)
(*  second is not a tidy-up: it is the condition under which the store  *)
(*  can be given a type at all. `pframe` held a `pctx` only because     *)
(*  B1.6 defunctionalised the token into a `PTokenF` frame, and that    *)
(*  frame is what nearness-based resolution read. Deleting it removes   *)
(*  the nearness AND frees `pctx` from the block, in one step.          *)
(*                                                                     *)
(*  EVERY VALUE POSITION IS NOW `pval v` RATHER THAN `v`. That is a     *)
(*  mechanical change with one semantic consequence, and it is the      *)
(*  gate's: the thing a `POp` binds, a `PBindF` receives, a `PParamF`   *)
(*  holds and a payload carries may be a context handle.                *)
(* ------------------------------------------------------------------ *)

noeq
type pcomp (v: Type u#a) (cl: Type u#a) : Type u#a =
  | POp: c:pcomp v cl -> fn:(pval v -> pcomp v cl) -> pcomp v cl
  | PVar: value:pval v -> pcomp v cl
  | PPerform: eff:string -> op:string -> payload:list (pval v) -> pcomp v cl
  // `PromptF` installation, WITH provenance. This is the surface's `with`
  // (`PMono`) and `withF` (`PFamily`) at one node: they differ in the evidence
  // they attach and in nothing else, which is the reframing made syntax.
  | PHandle:
      tbl:ptable cl ->
      ret:option (pval v -> pcomp v cl) ->
      prov:prompt_provenance ->
      body:pcomp v cl ->
      pcomp v cl
  | PSplice: frames:list (pframe v cl) -> body:pcomp v cl -> pcomp v cl
  // **An observation.** `PEmit ev c` appends `ev` to the machine's trace and
  // continues as `c`; nothing else in the machine reads or produces one.
  //
  // It is new in B1.6 and it is the INSTRUMENT, not the result. B1.5 could say
  // that the residual did less work than the suspension (`pcost`, and
  // `fixture_1_prefix_runs_once` still says it) but not that the protected
  // prefix RAN ONCE, because this machine is pure and `pobs_eq` observes only
  // values: a replayed prefix returns what it returned before. An emission is
  // the smallest thing that breaks that -- an effect the plan does not contain
  // and cannot undo -- and it is exactly what every JS effect is in the shipped
  // runtime.
  //
  // It carries its continuation rather than producing a value, because `v` is
  // abstract and the prototype has no unit to hand back. That also keeps the
  // trace out of the value language entirely: no computation can read the trace,
  // so no fixture can accidentally check exact-once by observing a counter the
  // program itself maintained.
  | PEmit: ev:string -> body:pcomp v cl -> pcomp v cl
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
  // **Producing a context.** THE node of B1.6, and in B1.7 it loses an argument.
  //
  // B1.5 produced a context with a meta-level function -- `enter_ctx_C lk apply
  // fuel pl c`, which ran `psteps` to completion on an EMPTY ambient stack and
  // returned a `pctx`. Taking a lookup, an interpreter and a fuel and returning
  // a pure context IS detached evaluation written down: a test-harness partial
  // evaluator exposed through the interface. Everything that followed from it --
  // an operation the plan did not handle becoming `PStuck` where the real
  // machine would have carried it outward, and hence the `settles` hypothesis on
  // every law -- followed from that one shape.
  //
  // Here production is a NODE. It steps on the live stack: the boundary marker,
  // then the plan's protocol frames, then `PScopeF kf`, then whatever was
  // already there. Consequences, in the order they matter:
  //
  //   - an operation the prefix performs that no plan prompt handles is found by
  //     the ordinary `pfind_prompt` walk, which continues PAST the owner and
  //     past the scope floor into the ambient stack;
  //   - if an ambient handler is not tail-resumptive, its pending frames sit
  //     below the point it dispatched from, and when it resumes, the scope --
  //     boundary, plan frames and floor together, since they were all inside the
  //     segment it captured -- is re-installed ABOVE them. The token, when it is
  //     finally produced, is handed to `kf` on a stack that still has that
  //     handler's unfinished work in it. That is the exact case B1.5 argued no
  //     meta-level truncation could get right, and it is right here for the
  //     reason the argument identified: nothing is truncated, because nothing is
  //     returned.
  //
  // **B1.6's `kbody` field is GONE, and its absence is condition 1.**
  //
  // B1.6 could not put the token in the value position -- see `pval` above for
  // why the two direct embeddings are rejected -- so production carried the
  // continuation the token was produced FOR, installed the token in a `PTokenF`
  // frame beneath it, and let the consuming nodes read the nearest one. A
  // context was therefore DYNAMICALLY SCOPED, and the published `ScopeTactics`,
  // which take an explicit `ctx x`, would have run a well-typed program with a
  // different meaning: given two live contexts, the nearest wins whichever was
  // passed.
  //
  // Under the stratification the token IS a value, so production needs no
  // continuation of its own. `PEnterCtx pl body` runs `body` under the plan and
  // then EVALUATES TO A HANDLE, in the ordinary way a node evaluates to a value:
  // the enclosing `PBindF` receives it. The surface's
  //
  //     cx <- t.runScope p
  //
  // is therefore literally `POp (PEnterCtx pl p) (fun cx -> ...)`, with no
  // node-level continuation and nothing installed on the stack for a later
  // search to find. `pfind_token` -- B1.6's nearest-token search -- is deleted;
  // there is no function in this module that resolves a context by position.
  //
  // The rule is otherwise B1.6's, unchanged, and it is still four frames on the
  // LIVE stack: the boundary marker, the plan's protocol frames, the scope floor
  // `PScopeF`, and the ambient stack untouched beneath. Consequences, in the
  // order they matter:
  //
  //   - an operation the prefix performs that no plan prompt handles is found by
  //     the ordinary `pfind_prompt` walk, which continues PAST the owner and
  //     past the scope floor into the ambient stack;
  //   - if an ambient handler is not tail-resumptive, its pending frames sit
  //     below the point it dispatched from, and when it resumes, the scope --
  //     boundary, plan frames and floor together, since they were all inside the
  //     segment it captured -- is re-installed ABOVE them. The handle, when it
  //     is finally produced, is delivered to a continuation running on a stack
  //     that still has that handler's unfinished work in it. That is the exact
  //     case B1.5 argued no meta-level truncation could get right, and it is
  //     right here for the reason the argument identified: nothing is truncated,
  //     because nothing is returned.
  | PEnterCtx:
      pl:plan v cl ->
      body:pcomp v cl ->
      pcomp v cl
  // **The three consuming operations, each taking THE HANDLE IT IS TO CONSUME.**
  // `enter_C` needs no node of its own: it is what `PWeave` steps to.
  //
  // The `h:pval v` field is condition 4 made syntax. In B1.6 these nodes had no
  // such field and the rule read the nearest `PTokenF`; here the rule resolves
  // `h` against the store and FAILS if it does not resolve (condition 7). There
  // is no fallback: `pstep` has no arm that reaches for a context it was not
  // given.
  //
  // `PExtendCtxC` is `bindScope` in its full shape. In B1.6 it had to carry a
  // `kbody`, because the context it produced could only be installed on the
  // stack for the rest of the clause to find. Here it evaluates to a FRESH
  // HANDLE, exactly as production does, so `cy <- bindScope cx g` is an ordinary
  // bind -- and `cx` is untouched, which is condition 8.
  | PExtendC: pl:plan v cl -> h:pval v -> g:(pval v -> pcomp v cl) -> pcomp v cl
  | PExtendCtxC: pl:plan v cl -> h:pval v -> g:(pval v -> pcomp v cl) -> pcomp v cl
  | PResumeC: pl:plan v cl -> h:pval v -> k:(pval v -> pcomp v cl) -> pcomp v cl
  | PNewP: label:string -> init:pval v -> body:pcomp v cl -> pcomp v cl
  | PReadP: label:string -> pcomp v cl
  | PWriteP: label:string -> value:pval v -> pcomp v cl

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
 *
 *   - `PScopeF` is THE SCOPE FLOOR, new in B1.6 and the frame that makes
 *     production a transition. `PEnterCtx` installs it BENEATH the plan's
 *     frames, so it separates what belongs to the scope from what was on the
 *     ambient stack already. Two rules read it and they are the whole of
 *     production's other half: a value that reaches it directly has drained the
 *     whole scope without ever asking for anything, so the context is
 *     `PCtxDone`; and a boundary or site frame with no mode above it CUTS the
 *     stack here, taking everything above as the residual and continuing on
 *     everything below. In both cases the context is ALLOCATED and the machine
 *     continues with its handle as the value.
 *
 *     **In B1.7 it carries nothing at all**, and losing its field is worth
 *     noticing. B1.6's floor held `kbody`, the continuation the token was
 *     produced for, because there was no value position to deliver a token to.
 *     Now there is: production evaluates to a handle, so the floor's whole job
 *     is to say WHERE the scope's frames end. The frame is a marker and its
 *     content is its position.
 *
 *     It is a frame and not a field of the boundary marker because the two are
 *     at different depths and get separated: the boundary rides up into every
 *     continuation a layer captures, and the floor stays where the ambient stack
 *     begins.
 *
 *     It is also what delimits the mode search; see `pfind_mode`.
 *
 *   - **`PTokenF` IS DELETED.** B1.6's produced context lived in this frame and
 *     the consuming nodes read the NEAREST one, exactly as `PReadP` reads a
 *     cell. That is the single step B1.7 rejects: it makes a context dynamically
 *     scoped, so a program holding two `ctx x` values and passing one of them
 *     gets the other. Deleting the frame does two things at once -- it removes
 *     every nearness-based path to a context, and it takes `pctx` out of this
 *     mutual block, which is what lets the store be given a type.
 *)
and pframe (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PBindF: fn:(pval v -> pcomp v cl) -> pframe v cl
  | PParamF: label:string -> value:pval v -> pframe v cl
  | PPromptF:
      tbl:ptable cl ->
      ret:option (pval v -> pcomp v cl) ->
      prov:prompt_provenance ->
      pframe v cl
  | PBoundaryF: pframe v cl
  | PSiteF: fn:(pval v -> pcomp v cl) -> pframe v cl
  | PModeF: mode:weave_mode -> respond:(pval v -> pcomp v cl) -> pframe v cl
  | PScopeF: pframe v cl

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
      tbl:ptable cl ->
      ret:option (pval v -> pcomp v cl) ->
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
  | PIBind: fn:(pval v -> pcomp v cl) -> plan_item v cl
  | PICell: label:string -> value:pval v -> plan_item v cl
  | PITransparent: tbl:ptable cl -> plan_item v cl
  | PIReenter: tbl:ptable cl -> ret:option (pval v -> pcomp v cl) -> plan_item v cl

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
 * **A context value: a RESIDUAL MACHINE CONFIGURATION** -- and in B1.7 it is
 * OUTSIDE the mutual block above, which is the third and last step of the
 * stratification.
 *
 * It could not be outside in B1.6, because `pframe` held one (`PTokenF`). It can
 * be now because nothing in the AST mentions it: a program names a context by a
 * `PCtxKey`, and the `pctx` itself lives only in the store beside the machine
 * state. Read the dependency order and the positivity argument comes out by
 * inspection -- `pval` depends on nothing, the AST depends on `pval`, `pctx`
 * depends on both, and the store depends on `pctx`. There is no cycle to check.
 *
 * `C x` of the design note. It is not a `pval`, and that is deliberate -- a
 * machine-side datum the surface receives only as an opaque handle, which is
 * what the design's stop condition "the FFI passing anything but a context plan
 * or an opaque context value" already anticipates. The handle is the opaque
 * value; this is what it names.
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
 * **The two shapes, and what each means.**
 *
 *   - `PCtxDone y` -- the layers and the owner produced `y` without ever asking
 *     the scope for anything, and there was no recorded bind frame left in the
 *     path either. A `Full` clause that discards its continuation gets here. The
 *     machine reaches it when a value arrives at the scope floor directly.
 *
 *   - `PCtxRequests x residual post` -- a value reached a `PBoundaryF` or a
 *     `PSiteF` with no consumer above it, and the stack was cut at the scope
 *     floor: `residual` is that frame together with everything the layer and
 *     owner handlers have grown between it and the floor, and it begins with the
 *     frame whose meaning depends on the consumer. `post` is the EXTENSION CHAIN
 *     accumulated by `extend_ctx_C`, not yet applied, and it is a field rather
 *     than something already run into the residual so that extending a context
 *     re-runs nothing at all.
 *
 * **WITHDRAWN IN B1.6: `PCtxLost st`.** B1.5 had a third shape, carrying the
 * `pstate` a detached production had failed in -- out of fuel, stuck, or
 * rejected. All three were artefacts of production being a meta-level run that
 * had to RETURN something whatever happened. A transition returns nothing: a
 * prefix that gets stuck makes the machine stuck, a prefix that diverges makes
 * the machine diverge, and there is no fuel to run out of because the fuel
 * belonged to the harness and not to the operation. Two things follow that are
 * worth more than the constructor: the `settles` hypothesis on the four laws is
 * gone, and `pstate` is no longer part of the AST's mutual block -- a context is
 * no longer a snapshot of a failed run, so the state type does not have to be
 * defined before the syntax that mentions it.
 *
 * A context does NOT carry the plan it belongs to. The plan is what the machine
 * holds at the transition, and a context carrying its own copy would be a second
 * plan that can disagree with it. Every operation still takes a plan -- although,
 * and this is the price of the representation, only production READS the one it
 * is given; see the note on `resume_C`.
 *
 * Nor does it carry a TRACE. Whatever the prefix emitted was emitted by the
 * transitions that produced this value, and the driver has it; there is nowhere
 * in these two constructors for an observation to hide, which is B1.6's
 * requirement 1 answered by the type rather than by a check.
 *
 * *A small fact found by trying to break it.* `PCtxDone y` and
 * `PCtxRequests y [] (PVar)` are OPERATIONALLY THE SAME: `ctx_drive` splices a
 * lone mode marker in the second case, the value meets it, the marker is inert,
 * and the consumer's function goes unapplied exactly as in the first. Replacing
 * the `PScopeF` value rule so that it builds the second was tried and no fixture
 * noticed. The two constructors are kept apart anyway, because "the scope
 * drained without ever asking" and "the scope asked, with nothing left between
 * the question and the floor" are different things to a reader even where they
 * are the same thing to the machine.
 *)
noeq
type pctx (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PCtxDone: value:pval v -> pctx v cl
  | PCtxRequests:
      value:pval v ->
      residual:list (pframe v cl) ->
      post:(pval v -> pcomp v cl) ->
      pctx v cl

(**
 * **The machine states**, and in B1.6 they are OUTSIDE the AST's mutual block:
 * see the withdrawal of `PCtxLost` above.
 *
 * `PPaused` survives, demoted. In B1.5 it was where every context came from --
 * production stopped there and read the state off. Here a boundary reached with
 * no consumer above it and no scope floor below it is a stack that no transition
 * of this machine can build, and `PPaused` is what the value rule answers in
 * that case: a totality obligation, kept as a distinct state rather than folded
 * into `PStuck` so that a well-bracketing failure would be visible as itself.
 * `fixture_9_paused_is_unreachable` is the check that the fixtures never produce
 * one.
 *
 * `PRejected` carries the SHIPPED rejection type. It is flat and independent of
 * `v` and `cl`, so there is nothing to translate: a plan refused here is refused
 * with the very constructor `Hoop.Runtime.Semantics.step` produces, which is
 * what makes "the caller can produce the existing `UnborrowableScope` rejection"
 * a fact about a type rather than a resemblance between two enumerations.
 *)
noeq
type pstate (v: Type u#a) (cl: Type u#a) : Type u#a =
  | PDone: value:pval v -> pstate v cl
  | PStep: c:pcomp v cl -> k:list (pframe v cl) -> pstate v cl
  | PPaused: value:pval v -> residual:list (pframe v cl) -> pstate v cl
  | PStuck: eff:string -> op:string -> pstate v cl
  | PRejected: rejection -> pstate v cl

(* ------------------------------------------------------------------ *)
(*  The store, and the configuration it lives in                       *)
(* ------------------------------------------------------------------ *)

(**
 * **The context store: an APPEND-ONLY association list**, keyed by the `nat` a
 * `PCtxKey` carries.
 *
 * *Why a list and not `nat -> option (pctx v cl)`.* A function store is the
 * shape the design note's scratch check used and it typechecks equally well, but
 * every write to one is `fun i -> if i = n then Some cx else old i`, and
 * "nothing was overwritten" is then a property of a chain of closures that no
 * `assert_norm` can look at. With a list, allocation is a `::` and the two
 * obligations of condition 8 are properties an `assert_norm` and a short
 * induction can both reach: `palloc` only ever CONSES, and `pstore_lookup`
 * returns the first match.
 *
 * *Why first-match rather than last-match.* First-match makes a later entry
 * shadow an earlier one with the same key. That is not how the machine uses it
 * -- `lemma_alloc_fresh` below is PROVED, and says the key allocated is strictly
 * greater than every key already present, so the machine never creates a
 * duplicate -- but it is the safe direction if one ever arose, because it is the
 * ALLOCATING branch that would win rather than a stale entry from elsewhere.
 *
 * *What is deliberately absent: a free, a clear, and an update.* There is no
 * function in this module that removes an entry or replaces one in place. That
 * is condition 8 at the level of the API rather than of a proof, and it is the
 * reason the `cy1 <- bindScope cx g; cy2 <- bindScope cx h` program has three
 * independent contexts rather than one overwritten three times. A real
 * implementation would want to reclaim; the point of the prototype is that
 * reclamation is then an optimisation with an obligation, not the semantics.
 *)
type pstore (v: Type u#a) (cl: Type u#a) : Type u#a = list (nat & pctx v cl)

let rec pstore_lookup (#v #cl: Type) (id: nat) (sto: pstore v cl)
  : Tot (option (pctx v cl)) (decreases sto)
  = match sto with
    | [] -> None
    | (i, cx) :: rest -> if i = id then Some cx else pstore_lookup id rest

(**
 * **Resolving a handle**, and it is the ONLY way any transition of this machine
 * reaches a context.
 *
 * Two ways to fail, and both must fail rather than degrade:
 *
 *   - `PV _` -- an ordinary value used where a handle was wanted. The surface's
 *     types make this unreachable; the machine still has to answer, and the
 *     answer is a refusal.
 *   - `PCtxKey id` with `id` not in the store -- a FORGED or STALE handle.
 *
 * **Neither arm consults the stack.** That is condition 7, and it is a property
 * of this function's TYPE before it is a property of its body: `presolve` is not
 * given a stack, so it could not fall back to the nearest context even if its
 * author wanted to. B1.6's `pfind_token` took a `pstack` and returned the
 * nearest `PTokenF`; it is deleted, and there is nothing in this module that
 * takes its place.
 *)
let presolve (#v #cl: Type) (sto: pstore v cl) (h: pval v) : option (pctx v cl)
  = match h with
    | PV _ -> None
    | PCtxKey id -> pstore_lookup id sto

(**
 * **The machine configuration**: a state, the store, and the next key.
 *
 * **`next` is in the CONFIGURATION and in nothing else, and that is the answer
 * to the gate's flagged hazard.** This machine has multi-shot continuations: a
 * captured segment is a list of FRAMES, and resuming it is `PSplice`, which
 * pushes those frames back. Neither the store nor the counter is a frame, so
 * neither is captured and neither is restored. A continuation captured before an
 * allocation and resumed twice therefore sees a counter that the first
 * resumption has already advanced, and the second resumption allocates a
 * DIFFERENT key. `fixture_21_multi_shot_alloc` is the program that would catch
 * the alternative, and `lemma_alloc_monotone` is the proof that the counter is
 * monotone.
 *
 * Had `next` been carried on a frame -- or derived from anything branch-local,
 * stack depth being the tempting one -- two resumptions of one continuation
 * would allocate the same key and then disagree about what it names. That is not
 * a hypothetical: the mutation was made and the fixture rejected it.
 *
 * The alternative considered and rejected is the NAIVE per-continuation
 * snapshot -- taken at capture and restored on resumption, with nothing
 * reconciling the branches. It would make `bindScope` inside a resumed
 * continuation invisible to the sibling resumption, which is a coherent design
 * for a LINEAR context and not for a multi-shot one, since the published API
 * admits consuming the same `ctx x` from two branches and the two branches must
 * agree about what it is. That naive scheme also solves neither collision
 * between the branches' independent allocators nor lost updates.
 *
 * **This is not a claim that no snapshot representation could work.** A scheme
 * that reconciled sibling updates and kept allocators from colliding is not
 * excluded by anything checked here. Global-and-monotone is the REFERENCE
 * choice, adopted because it makes "the handle passed" have a meaning that does
 * not depend on where it is read, and a shipping form is free to differ if it
 * can be shown to agree.
 *)
noeq
type pconf (v: Type u#a) (cl: Type u#a) : Type u#a = {
  st: pstate v cl;
  store: pstore v cl;
  next: nat;
}

(**
 * **Allocation, and it is the ONLY writer of the store.**
 *
 * A `::` and an increment. There is no other function in this module that
 * constructs a `pstore` other than the empty one in `pload`, which is what makes
 * "append-only" a statement about a two-line definition rather than about a
 * discipline someone has to keep.
 *
 * The three obligations it discharges, and which of them are CHECKED below:
 *
 *   - the returned handle is `PCtxKey cf.next`, and `cf.next` is not a key of
 *     `cf.store` provided the configuration is well formed -- `pconf_wf` states
 *     this and `lemma_alloc_wf` PROVES it is preserved;
 *   - the old store is a SUFFIX of the new one, so every handle that resolved
 *     before resolves to the same context after (`lemma_alloc_preserves`,
 *     proved);
 *   - `next` strictly increases (`lemma_alloc_monotone`, proved), which is what
 *     makes two allocations on two resumptions of one continuation get two
 *     different keys.
 *)
let palloc (#v #cl: Type) (cx: pctx v cl) (cf: pconf v cl)
  : (pval v & pconf v cl)
  = (PCtxKey cf.next,
     { cf with store = (cf.next, cx) :: cf.store; next = cf.next + 1 })

(** Every key in the store is strictly below `next`. This is the invariant that
    makes a freshly allocated key fresh, and it is the ONLY thing standing
    between the machine and the multi-shot id collision the gate flags. *)
let pconf_wf (#v #cl: Type) (cf: pconf v cl) : prop
  = forall (i: nat) (cx: pctx v cl). memP (i, cx) cf.store ==> i < cf.next

(** A key at or above `next` is absent -- the form the freshness invariant is
    actually used in. *)
let rec lemma_wf_absent (#v #cl: Type) (i: nat) (sto: pstore v cl) (n: nat)
  : Lemma (requires (forall (j: nat) (cx: pctx v cl). memP (j, cx) sto ==> j < n) /\ i >= n)
          (ensures pstore_lookup i sto == None)
          (decreases sto)
  = match sto with
    | [] -> ()
    | (j, cx) :: rest -> lemma_wf_absent i rest n

(** Allocation preserves well-formedness. PROVED. *)
let lemma_alloc_wf (#v #cl: Type) (cx: pctx v cl) (cf: pconf v cl)
  : Lemma (requires pconf_wf cf) (ensures pconf_wf (snd (palloc cx cf)))
  = ()

(** `next` strictly increases. PROVED, and it is condition 8's freshness across
    multi-shot resumption: a counter that only ever goes up cannot hand the same
    key to two branches. *)
let lemma_alloc_monotone (#v #cl: Type) (cx: pctx v cl) (cf: pconf v cl)
  : Lemma (ensures (snd (palloc cx cf)).next > cf.next)
  = ()

(** **The new key is genuinely fresh**: it resolved to nothing before. PROVED. *)
let lemma_alloc_fresh (#v #cl: Type) (cx: pctx v cl) (cf: pconf v cl)
  : Lemma (requires pconf_wf cf)
          (ensures pstore_lookup cf.next cf.store == None)
  = lemma_wf_absent cf.next cf.store cf.next

(** **Allocation disturbs nothing already allocated.** PROVED, and this is
    condition 8's other half: `extend` writes a new entry, so the handle it was
    given still resolves to exactly the context it resolved to before. *)
let lemma_alloc_preserves (#v #cl: Type) (cx: pctx v cl) (cf: pconf v cl) (i: nat)
  : Lemma (requires pconf_wf cf /\ Some? (pstore_lookup i cf.store))
          (ensures pstore_lookup i (snd (palloc cx cf)).store
                   == pstore_lookup i cf.store)
  = lemma_alloc_fresh cx cf

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
    (tbl: ptable cl)
    (ret: option (pval v -> pcomp v cl))
  : prompt_class
  = match prov with
    | PFamily -> Family
    | PMono ->
      match ret with
      | Some _ -> Monomorphic
      | None -> if borrowable tbl.hs then ContextTransparent else Monomorphic

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
    | PPromptF tbl ret prov :: rest ->
      (match classify_prompt prov tbl ret with
        | Monomorphic -> Inl (MonomorphicLayer (blocking_effects tbl.hs))
        | ContextTransparent ->
          (match plan_layers rest with
            | Inl e -> Inl e
            | Inr ls -> Inr (PITransparent tbl :: ls))
        | Family ->
          (match plan_layers rest with
            | Inl e -> Inl e
            | Inr ls -> Inr (PIReenter tbl ret :: ls)))
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
  = PPromptF (POwner?.tbl own) (POwner?.ret own) (POwner?.prov own)

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
    | PITransparent tbl :: rest -> PPromptF tbl None PMono :: enter_layer_frames rest
    | PIReenter tbl ret :: rest -> PPromptF tbl ret PFamily :: enter_layer_frames rest

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
    | PITransparent tbl :: rest -> PPromptF tbl None PMono :: resume_layer_frames rest
    | PIReenter tbl ret :: rest -> PPromptF tbl ret PFamily :: resume_layer_frames rest

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
    | PITransparent tbl :: rest -> PPromptF tbl None PMono :: protocol_layer_frames rest
    | PIReenter tbl ret :: rest -> PPromptF tbl ret PFamily :: protocol_layer_frames rest

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
(*  The context operations                                             *)
(*                                                                     *)
(*  The reference MEANING of the scope tactics. Gate A established      *)
(*  that their types do not force these implementations -- a            *)
(*  `runScope` that injects each value into a singleton typechecks and  *)
(*  is wrong -- which is exactly why they are defined here, in a        *)
(*  machine with a reference semantics, rather than on the PureScript   *)
(*  side. The surface's job is to delegate; nothing that can be wrong    *)
(*  should be written there.                                            *)
(*                                                                     *)
(*  They come in two layers in B1.6 and the split is worth knowing      *)
(*  before reading them. `ctx_drive`, `extend_C`, `extend_ctx_C` and    *)
(*  `resume_C` take an EXPLICIT context and are the meanings; the four  *)
(*  builders below them -- `enter_ctx_C`, `extend_at_C`,                *)
(*  `extend_ctx_at_C`, `resume_at_C` -- are single constructors and     *)
(*  are what a program writes. The transitions are what join the two.   *)
(* ------------------------------------------------------------------ *)

(** **The inner monad's bind**, named so that the laws below and the operations
    speak of one SMT symbol rather than of an `POp` a reader has to recognise.
    This is `Hoop.Runtime.Syntax.Op` under the prototype's name. *)
unfold
let pbind (#v #cl: Type) (c: pcomp v cl) (f: pval v -> pcomp v cl) : pcomp v cl
  = POp c f

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
 * **Producing a context**, and in B1.6 it is one line of syntax.
 *
 * Compare what it replaced:
 *
 * ```fstar
 * let enter_ctx_C lk apply fuel pl c =
 *   pctx_of_state PVar (psteps lk apply fuel (PStep c (PBoundaryF :: plan_protocol_frames pl)))
 * ```
 *
 * -- a lookup, a clause interpreter and a fuel bound in, a finished `pctx` out.
 * That is a partial evaluator, and the type said so before any behaviour was
 * examined. What is here instead takes a plan and an inner computation, and
 * BUILDS A NODE. It runs nothing. The machine's `PEnterCtx` rule is what runs,
 * on whatever stack the program is on at the time, and the context is formed and
 * allocated by a value rule.
 *
 * **In B1.7 it takes ONE argument fewer than in B1.6**, and the argument it lost
 * is the gate: B1.6 had to be handed the continuation the token was produced
 * for, because a token could not be a value and had to be installed on the stack
 * beneath something. Production now evaluates to a handle, so `runScope` is an
 * ordinary bind and the caller decides what to do with the result -- including
 * keeping it, pairing it, or consuming it after some other scope has come and
 * gone.
 *
 * **This is the gate's stop condition, and the check that it did not fire is
 * mechanical**: `psteps`, `pcost`, `papply_t`, `plookup_t` and `nat` do not
 * occur in this definition, in the four consuming builders below, or in the
 * `ctx_ops` record they are collected into -- every one of the five is a single
 * constructor application. Nor do they occur in the `pstep` rules for
 * `PEnterCtx`, `PExtendC`, `PExtendCtxC` and `PResumeC`. The scope tactics can
 * therefore be thin delegations to transitions, which is the standing constraint
 * the design note records; under B1.5 the production tactic could not have been,
 * because there was no transition to delegate to.
 *)
let enter_ctx_C
    (#v #cl: Type)
    (pl: plan v cl) (c: pcomp v cl)
  : pcomp v cl
  = PEnterCtx pl c

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
let ctx_drive (#v #cl: Type) (m: weave_mode) (cx: pctx v cl) (f: pval v -> pcomp v cl)
  : pcomp v cl
  = match cx with
    | PCtxDone y -> PVar y
    | PCtxRequests x resid post ->
      PSplice (resid @ [PModeF m (fun z -> pbind (post z) f)]) (PVar x)

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
let extend_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: pval v -> pcomp v cl)
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
let extend_ctx_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: pval v -> pcomp v cl)
  : pctx v cl
  = match cx with
    | PCtxDone y -> PCtxDone y
    | PCtxRequests x resid post -> PCtxRequests x resid (fun z -> pbind (post z) g)

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
let resume_C (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (k: pval v -> pcomp v cl)
  : pcomp v cl
  = ctx_drive MResume cx k

(**
 * **The three consuming operations AS THE PROGRAM WRITES THEM** -- each a single
 * constructor, and each NAMING THE CONTEXT IT CONSUMES.
 *
 * `extend_C`, `extend_ctx_C` and `resume_C` above are the MEANINGS: functions of
 * an explicit `pctx`, which is what the transitions below delegate to once they
 * have RESOLVED one. These three are what a clause builds, and the `h` they take
 * is a `pval v` -- an ordinary object-language value, the thing a `PBindF`
 * received from a production.
 *
 * **The rename from B1.6's `..._here_C` is the gate.** "Here" meant the nearest
 * `PTokenF`, so the operation took no handle and there was no syntax for naming
 * a context; `..._at_C` takes the handle and the transition resolves it against
 * the store. A program holding two contexts now selects, and what it selects is
 * what it gets -- condition 4, and it is visible in these three signatures
 * before any transition is read.
 *
 * That separation is worth having for its own sake and not only because
 * positivity forced it. It puts each tactic in the position the design note
 * demands: `resume_at_C pl h k` IS a node, so the surface's `resumeScope cx k`
 * is a constructor call and cannot be anything else.
 *)
let extend_at_C (#v #cl: Type) (pl: plan v cl) (h: pval v) (g: pval v -> pcomp v cl)
  : pcomp v cl
  = PExtendC pl h g

let extend_ctx_at_C (#v #cl: Type) (pl: plan v cl) (h: pval v) (g: pval v -> pcomp v cl)
  : pcomp v cl
  = PExtendCtxC pl h g

let resume_at_C (#v #cl: Type) (pl: plan v cl) (h: pval v) (k: pval v -> pcomp v cl)
  : pcomp v cl
  = PResumeC pl h k

(**
 * **B1's two consuming operations, withdrawn, kept executable.**
 *
 * These are the suspension representation exactly as it stood: the context was
 * the unrun inner computation, so it needed no type of its own, and each
 * operation spliced its own projection of the plan around it. They are here as
 * CONTROLS and nothing else, and in B1.6 they earn their keep twice over:
 * `fixture_1_prefix_runs_once` measures the work they cost beside the residual's,
 * and `fixture_12_suspension_emits_twice` shows them emitting the protected
 * prefix's observation A SECOND TIME, which is what makes
 * `fixture_11_prefix_event_once` evidence rather than a number.
 *
 * They are not a `ctx_ops`. They cannot be: a `ctx_ops` production takes the
 * continuation the token is produced for and there is no token here, only a
 * computation re-run from the start.
 *)
let susp_extend (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) (g: pval v -> pcomp v cl)
  : pcomp v cl
  = PSplice (plan_enter_frames pl) (pbind c g)

let susp_resume (#v #cl: Type) (pl: plan v cl) (c: pcomp v cl) (k: pval v -> pcomp v cl)
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
let papply_t (v cl: Type) = cl -> list (pval v) -> (pval v -> pcomp v cl) -> pcomp v cl

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
 *
 * *B1.6 widened the argument to a `ptable`*, so that a lookup CAN tell two
 * prompts apart -- see `ptable`, where the reason and the price are set out. The
 * reference lookup below ignores the widening.
 *)
let plookup_t (cl: Type) = ptable cl -> string -> string -> option (found_clause cl)

(** **The reference lookup**: the table as it ships, and only the table as it
    ships. `binds` is not read here and is not read by any transition; it exists
    for the fixtures' own lookup and for nothing else. *)
let pref_lookup (#cl: Type) : plookup_t cl = fun tbl eff op -> lookup_handler tbl.hs eff op

(** The prompt holding the handler for this action, and the stack split there:
    `(captured, found, below)`, captured including the prompt. The shipped
    `find_prompt` carries a refinement tying it to `handled_in`; this one does
    not, because nothing here proves progress and a refinement nobody spends is
    a refinement that has to be maintained.

    The four protocol frames fall through the catch-all, and must: a boundary
    that stopped the search would delimit effects it has no business delimiting
    -- the scope's operations are meant to reach the layer handlers, which is the
    whole point of weaving -- and a captured segment that stopped short of the
    boundary would not put the boundary back on resumption, which is what makes
    the second and later requests happen.

    **`PScopeF` falls through too, and in B1.6 that is the single line that makes
    requirement 5 come out.** An operation the plan does not handle walks past
    the owner, past the scope floor, and on into the AMBIENT stack, where an
    enclosing prompt may take it. Under B1.5 there was nothing below the floor to
    walk into. Because the floor is inside the segment such a handler captures,
    resuming re-installs the whole scope above that handler's own pending frames
    -- which is requirement 6, and it is not arranged anywhere: it is what
    capturing a segment already means. *)
let rec pfind_prompt (#v #cl: Type) (lk: plookup_t cl) (eff op: string) (k: pstack v cl)
  : Tot (option (pstack v cl & found_clause cl & pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | PPromptF tbl ret prov :: rest ->
      (match lk tbl eff op with
        | Some c -> Some ([PPromptF tbl ret prov], c, rest)
        | None ->
          (match pfind_prompt lk eff op rest with
            | None -> None
            | Some (cap, c, below) -> Some (PPromptF tbl ret prov :: cap, c, below)))
    | f :: rest ->
      (match pfind_prompt lk eff op rest with
        | None -> None
        | Some (cap, c, below) -> Some (f :: cap, c, below))

(** `read`: the contents of the nearest cell with this label. *)
let rec pfind_param (#v #cl: Type) (l: string) (k: pstack v cl)
  : Tot (option (pval v)) (decreases k)
  = match k with
    | [] -> None
    | PParamF l' x :: rest -> if l' = l then Some x else pfind_param l rest
    | _ :: rest -> pfind_param l rest

(** `write`: the stack with the nearest such cell set. Frames above it are
    rebuilt, frames below are shared -- there is no mutable cell and no
    identity, so a captured continuation keeps the value it was captured with. *)
let rec pset_param (#v #cl: Type) (l: string) (x: pval v) (k: pstack v cl)
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
 * and, SINCE B2a, PROVED.** The invariant is: a mode marker is installed by
 * `ctx_drive` immediately beneath the residual it drives, so no other residual's
 * marker can lie between a marker frame and its own.
 *
 * `presid_wf` below is that invariant written down, `lemma_pyield_residual_wf`
 * proves that every residual this machine stores satisfies it, and
 * `lemma_ctx_drive_answers_head` proves that under it the search from the
 * residual's head frame returns the mode AND the responder the driving consumer
 * installed. The two together are what the paragraph after next used to promise
 * B2a would have to supply.
 *
 * **B1.6 BOTH endangered this and made it smaller, and it is worth being exact
 * about which.** Endangered: under B1.5 production ran on an EMPTY stack, so
 * during production there was provably no marker anywhere below, and the search
 * could only ever find the marker of the residual currently being driven. Under
 * B1.6 production runs on the LIVE stack, and a scope entered from inside a
 * consumption has that consumption's marker somewhere beneath it -- so an
 * unguarded search would let an inner boundary be answered by an outer
 * consumer's responder, which is a genuine confusion of `MResume` with
 * `MExtend`.
 *
 * Made smaller: the guard is the `PScopeF` arm below. A scope floor terminates
 * the search, and a floor is exactly the frame that separates a scope's own
 * stack from everything it was entered on top of. So what has to be true is now
 * BRACKET-LOCAL -- "between a boundary or site frame and the marker that answers
 * it there is no scope floor" -- rather than a claim about every residual in the
 * program. That is B2a's to prove, and it is a smaller obligation than the one
 * B1.5 left.
 *
 * **B2a proved it, in exactly that form and with one conjunct added.** The
 * predicate is `presid_wf`, and it asks for no floor AND no nearer marker
 * between the head frame and the end of the residual. What discharges it is not
 * an assumption about programs: it is the branch condition
 * `pfind_mode rest == None` that `pstep` calls `pyield` under, composed with
 * `pcut_scope` cutting at the NEAREST floor. `lemma_pstep_yield_guard` is the
 * check that there is no other way to reach `pyield`.
 *
 * Labels would settle it rather than argue it, and the file already has the
 * idiom: `PNewP` takes a label the surface supplies, and
 * `Hoop.Runtime.Syntax.NewP` does the same. What stopped B1.5 from taking that
 * route is that a label would have to be generated per scope entry, which means
 * either a counter in the machine or a `string` argument on production, and the
 * second puts a name in the statement of all four laws for the sake of a case no
 * fixture reaches. **That repair is no longer needed for soundness**: the
 * unlabelled search is proved to answer correctly on every residual the machine
 * stores. It would still be needed if `pcut_scope` were ever changed, because it
 * is nearness and not labelling that currently supplies the guarantee.
 *)
let rec pfind_mode (#v #cl: Type) (k: pstack v cl)
  : Tot (option (weave_mode & (pval v -> pcomp v cl))) (decreases k)
  = match k with
    | [] -> None
    | PModeF m r :: _ -> Some (m, r)
    | PScopeF :: _ -> None
    | _ :: rest -> pfind_mode rest

(**
 * **The scope floor, and the split there** -- the other half of production, and
 * the one that has no counterpart at all in B1.5.
 *
 * `(above, kf, below)`: everything strictly above the nearest floor, the
 * continuation that floor is holding, and everything strictly below it. The
 * floor itself is dropped, because control is leaving the scope through it and a
 * second token would otherwise be produced when the consumer's answer drains
 * past.
 *
 * **`above` is the residual, and `below` is why the truncation objection B1.5
 * raised does not apply.** B1.5 argued that running production on top of the
 * ambient stack and truncating at a marker is not well defined: if an ambient
 * handler reached during production is not tail-resumptive, its pending frames
 * lie BELOW the marker, and a meta-level production -- which must return a
 * `pctx` and has nowhere to put the rest of the machine -- would discard them.
 * The argument is correct and it is an argument against RETURNING, not against
 * cutting. Here nothing is returned: `below` is the stack the machine goes on
 * running on, so those pending frames are not discarded, they are where control
 * resumes. `fixture_10_outer_handler` is that sentence as a value.
 *
 * **A GAP, RECORDED BECAUSE IT WAS LOOKED FOR AND NOT FOUND.** "Nearest" is
 * written here, and NO FIXTURE IN THIS FILE SEPARATES IT FROM "FARTHEST".
 * Rewriting this function to cut at the outermost floor instead was tried and
 * the module still verifies: on `prog_two_floors`, the one program that has two
 * floors alive at once, both versions compute `own(k(m(leaf v)))`. What appears
 * to happen is that cutting too far merely defers the inner cut by one round --
 * the inner floor is still inside the residual, so the inner boundary yields
 * again as soon as the outer consumer drives it -- and on a well-bracketed
 * program the two reconverge. That is AN OBSERVATION ABOUT TWO RUNS and
 * emphatically not a theorem. It is the same shape as B2a's well-bracketing
 * obligation and is recorded here so that B2a knows this discipline is chosen
 * rather than forced by anything this file checks.
 *
 * **RE-TESTED IN B1.7 AND STILL NOT SEPARATED.** The handle representation was
 * the obvious candidate to make the two discriminable -- a wrongly cut residual
 * is now a wrongly STORED one, with an identity a later program can name. It
 * does not. The mutation was applied over the new representation, confirmed not
 * to be a no-op (`pcut_scope [PScopeF; PBoundaryF; PScopeF]` gives
 * `Some ([], [PBoundaryF; PScopeF])` here and `Some ([PScopeF; PBoundaryF], [])`
 * mutated), and all 21 fixtures still passed. The gap is unchanged in size and
 * is now known not to be closed by identity.
 *
 * **CLOSED IN B2a, AND BY A THEOREM RATHER THAN BY A TWENTY-SECOND FIXTURE.**
 * The section beginning at `pno_floor` below settles it, and the verdict is that
 * **proximity is a SEMANTIC REQUIREMENT and not a normal form.** The chain is
 * three steps and each is checked:
 *
 *   - `lemma_cut_no_floor` -- the nearest cut never puts a floor in the
 *     residual, with no hypothesis at all;
 *   - `lemma_cut_no_mode` -- under the branch condition `pyield` is called with,
 *     it never puts a mode marker there either;
 *   - `lemma_ctx_drive_answers_head` -- from those two, driving a residual
 *     reaches the DRIVING consumer's marker at the residual's head frame, runs
 *     its responder, and allocates nothing.
 *
 * The third fails under the farthest cut, and not for want of a proof: the
 * conclusion is FALSE. `guard_far_drive_reyields` runs both machines on the two
 * residuals the two cuts produce from one yield and checks that the nearest one
 * answers `PV 7` with the store untouched while the farthest one yields a second
 * time, allocates, and answers with a handle. A `resumeScope` that does not
 * resume is not a deferred cut.
 *
 * **Why the earlier searches missed it, and it is CHECKED rather than argued.**
 * The separating stack needs a mode marker LIVE BETWEEN two floors. Two floors
 * alone are not enough: with nothing but ordinary frames between them the
 * farthest cut really does merely defer, exactly as the paragraph above guessed.
 * `fixture_22_separating_state_is_reachable` scans the whole run of three
 * programs for a configuration where the two cuts differ in the way that
 * matters, and finds one in `prog_sep` and NONE in `prog_two_floors` or
 * `prog_nested` -- the two programs the earlier gates were looking at. A value
 * passing a `PModeF` pops it, so a scope consumed inside another scope's BODY
 * has no marker left by the time the outer boundary yields; the marker has to be
 * one whose resumption is still running, which means a scope entered from inside
 * a resumption's continuation. That is what `prog_sep` does and what no fixture
 * before it did.
 *)
let rec pcut_scope (#v #cl: Type) (k: pstack v cl)
  : Tot (option (pstack v cl & pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | PScopeF :: rest -> Some ([], rest)
    | f :: rest ->
      (match pcut_scope rest with
        | None -> None
        | Some (above, below) -> Some (f :: above, below))

(* ------------------------------------------------------------------ *)
(*  B2a, strand 1: the association discipline, adjudicated             *)
(* ------------------------------------------------------------------ *)

(**
 * **The vocabulary the proximity question needs, and it is two predicates.**
 *
 * B1.6 and B1.7 both recorded that `pcut_scope`'s "nearest" and `pfind_mode`'s
 * "nearest" were CHOSEN and not forced: the farthest-floor mutation of
 * `pcut_scope` is not a no-op and yet all 21 fixtures accept it. What follows
 * settles that by proof rather than by another fixture, and the settlement turns
 * on a single structural fact -- what the NEAREST cut guarantees about the
 * segment it hands to the store that the FARTHEST cut does not.
 *
 * These two are deliberately about a SEGMENT and not about a configuration.
 * Strand 2's `pconf_wf` will want to say things about the whole stack and the
 * whole store; it should be able to reuse these unchanged, and nothing below
 * mentions `pconf`.
 *)
let rec pno_floor (#v #cl: Type) (k: pstack v cl) : Tot bool (decreases k)
  = match k with
    | [] -> true
    | PScopeF :: _ -> false
    | _ :: rest -> pno_floor rest

let rec pno_mode (#v #cl: Type) (k: pstack v cl) : Tot bool (decreases k)
  = match k with
    | [] -> true
    | PModeF _ _ :: _ -> false
    | _ :: rest -> pno_mode rest

(**
 * **THE INVARIANT, stated once and used everywhere below.**
 *
 * A residual is well formed when it begins with the frame whose meaning the
 * consumer decides -- a boundary or a recorded perform site, which is exactly
 * what `pyield` puts at its head -- and when NO SCOPE FLOOR AND NO MODE MARKER
 * lies between that head frame and the end of the residual.
 *
 * Read it as the association statement the module's prose has been asking for
 * since B1.5: *between a boundary or site frame and the marker that answers it
 * there is no scope floor, and no nearer marker.* `ctx_drive` appends the
 * consumer's marker at exactly the far end of the residual, so `presid_wf resid`
 * says precisely that the search `pfind_mode` runs from the head frame reaches
 * THAT marker: it is not stopped early by a floor, and it is not answered early
 * by somebody else's marker.
 *
 * Both conjuncts are needed and they fail differently. Without `pno_floor` the
 * search returns `None` and the consumer's own residual YIELDS AGAIN in its
 * face, allocating a second context instead of running the consumer's function.
 * Without `pno_mode` the search returns SOMEBODY ELSE'S responder, which is the
 * `MResume`/`MExtend` confusion the header at `pfind_mode` names.
 *)
let presid_wf (#v #cl: Type) (r: pstack v cl) : bool
  = match r with
    | PBoundaryF :: tl -> pno_floor tl && pno_mode tl
    | PSiteF _ :: tl -> pno_floor tl && pno_mode tl
    | _ -> false

(**
 * **Nearest-cut lemma I: the residual above a nearest cut contains no floor.**
 * PROVED, by induction on the stack, and it is a fact about `pcut_scope` ALONE
 * -- no hypothesis about the machine, about reachability, or about which
 * programs the fixtures write. `pcut_scope_far` below fails it, and the failure
 * is exhibited at a concrete stack.
 *)
let rec lemma_cut_no_floor (#v #cl: Type) (k: pstack v cl)
  : Lemma (ensures (match pcut_scope k with
                    | None -> True
                    | Some (above, _) -> pno_floor above))
          (decreases k)
  = match k with
    | [] -> ()
    | PScopeF :: _ -> ()
    | _ :: rest -> lemma_cut_no_floor rest

(**
 * **Nearest-cut lemma II: under the guard `pyield` is actually called with, the
 * residual above a nearest cut contains no mode marker.** PROVED.
 *
 * The hypothesis is not an assumption about well-bracketed programs. It is the
 * literal branch condition of the two `pstep` value rules that call `pyield`:
 * both reach it only in the `None` arm of `pfind_mode rest`. So the hypothesis
 * is DISCHARGED BY THE CODE at the one place the conclusion is wanted, which is
 * `lemma_pyield_residual_wf` below.
 *
 * The reason it works is the interlock between the two searches: `pfind_mode`
 * stops at the first floor, and the nearest cut takes exactly the segment before
 * the first floor. "No marker before the first floor" and "the residual is what
 * lies before the first floor" compose. Cut anywhere else and they do not --
 * `pfind_mode`'s `None` says nothing whatever about what lies BEYOND the first
 * floor, which is precisely the region a farthest cut sweeps into the residual.
 *)
let rec lemma_cut_no_mode (#v #cl: Type) (k: pstack v cl)
  : Lemma (requires pfind_mode k == None)
          (ensures (match pcut_scope k with
                    | None -> True
                    | Some (above, _) -> pno_mode above))
          (decreases k)
  = match k with
    | [] -> ()
    | PScopeF :: _ -> ()
    | PModeF _ _ :: _ -> ()
    | _ :: rest -> lemma_cut_no_mode rest

(**
 * **The reachability lemma: a floor-free, marker-free segment is TRANSPARENT to
 * the mode search.** PROVED, by induction on the segment.
 *
 * This is the half that makes `presid_wf` mean something operational. `ctx_drive`
 * builds `resid @ [PModeF m respond]` and splices it; the head frame is popped
 * by the value rule, which then searches the tail. This says the search lands on
 * the marker `ctx_drive` just installed, with the mode and the responder it
 * installed, whatever ambient stack `t` lies beneath.
 *
 * Note which nearness this one is about: it is `pfind_mode`'s. A variant that
 * returned the FARTHEST marker before the floor would look past `PModeF m r`
 * into `t` and could answer with an outer consumer's responder; see
 * `pfind_mode_far` and the counterexample beneath it.
 *
 * *Stated as transparency rather than as an answer, and the reason is a Z3
 * one worth recording.* The direct form
 * `pfind_mode (a @ (PModeF m r :: t)) == Some (m, r)` is TRUE and is the
 * corollary below, but the induction on it does not go through: the goal names
 * `Some (m, r)`, whose second component is a FUNCTION, and Z3 fails the
 * inductive step with `incomplete quantifiers` even though base case and step
 * are each provable in isolation. Replacing `nat` for the responder in a
 * standalone model of these three definitions makes the same induction succeed,
 * which is what identifies the trigger. The transparency form never names the
 * pair, so the induction is first-order throughout, and the corollary is one
 * instantiation with no induction left in it.
 *)
let rec lemma_find_mode_through (#v #cl: Type) (a: pstack v cl) (t: pstack v cl)
  : Lemma (requires pno_floor a /\ pno_mode a)
          (ensures pfind_mode (a @ t) == pfind_mode t)
          (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_find_mode_through rest t

(** **The corollary that is actually used**: the marker `ctx_drive` appends is
    the one the search finds. PROVED, by one instantiation of the above. *)
let lemma_find_mode_marker
    (#v #cl: Type) (a: pstack v cl)
    (m: weave_mode) (r: pval v -> pcomp v cl) (t: pstack v cl)
  : Lemma (requires pno_floor a /\ pno_mode a)
          (ensures pfind_mode (a @ (PModeF m r :: t)) == Some (m, r))
  = lemma_find_mode_through a (PModeF m r :: t)

(* ---- The farthest-choice variants, as named alternatives ---------- *)

(**
 * **The two mutations, given names and kept in the file.**
 *
 * B1.6 and B1.7 each APPLIED the `pcut_scope` mutation, ran the fixtures, and
 * restored the original -- so what the file recorded afterwards was a sentence
 * about an experiment nobody could re-run. These two definitions are that
 * experiment made permanent: they are ordinary functions, F* checks them, and
 * the guards below check what they do differently. Nothing in the machine calls
 * either of them, exactly as nothing in the machine calls `flat_ops`.
 *
 *   - `pcut_scope_far` cuts at the OUTERMOST floor. It is the mutation the two
 *     earlier gates fired, and it is not a no-op: `pcut_scope_far` on
 *     `[PScopeF; PBoundaryF; PScopeF]` gives `Some ([PScopeF; PBoundaryF], [])`
 *     where `pcut_scope` gives `Some ([], [PBoundaryF; PScopeF])`.
 *
 *   - `pfind_mode_far` answers with the OUTERMOST marker before the floor
 *     rather than the innermost. It is the corresponding mutation of the other
 *     search, which no earlier gate fired.
 *)
let rec pcut_scope_far (#v #cl: Type) (k: pstack v cl)
  : Tot (option (pstack v cl & pstack v cl)) (decreases k)
  = match k with
    | [] -> None
    | f :: rest ->
      (match pcut_scope_far rest with
        | Some (above, below) -> Some (f :: above, below)
        | None -> if PScopeF? f then Some ([], rest) else None)

let rec pfind_mode_far (#v #cl: Type) (k: pstack v cl)
  : Tot (option (weave_mode & (pval v -> pcomp v cl))) (decreases k)
  = match k with
    | [] -> None
    | PScopeF :: _ -> None
    | PModeF m r :: rest ->
      (match pfind_mode_far rest with
        | None -> Some (m, r)
        | Some x -> Some x)
    | _ :: rest -> pfind_mode_far rest

(** Total projections, so that a guard can be an equation between values with
    decidable equality rather than a claim about a pair holding a function. *)
let pcut_above (#v #cl: Type) (o: option (pstack v cl & pstack v cl)) : pstack v cl
  = match o with
    | None -> []
    | Some (a, _) -> a

let pmode_of (#v #cl: Type) (o: option (weave_mode & (pval v -> pcomp v cl)))
  : option weave_mode
  = match o with
    | None -> None
    | Some (m, _) -> Some m

(** Two concrete stacks, at `v = cl = nat`, and a responder to hang on them.
    Both shapes are ones the machine builds: `PEnterCtx` pushes a floor under
    every scope, so a scope entered inside a scope gives two floors, and
    `ctx_drive` appends a marker above whatever stack the consumer was running
    on, so a context consumed inside a scope puts a marker above that scope's
    floor. *)
let gresp : pval nat -> pcomp nat nat = fun _ -> PVar (PV 0)
let gstack_two_floors : pstack nat nat = [PScopeF; PBoundaryF; PScopeF]
let gstack_mode_between : pstack nat nat =
  [PScopeF; PModeF MExtend gresp; PScopeF]

(**
 * **GUARD 1: the farthest cut puts a scope floor inside the residual.**
 *
 * `lemma_cut_no_floor` is PROVED for `pcut_scope` with no hypothesis at all.
 * This is the same property evaluated at a concrete stack for both functions,
 * and it separates them: `true` against `false`. It is what a fixture could not
 * show, because a fixture observes an answer and this is a property of the
 * segment that goes into the store.
 *)
let guard_far_cut_keeps_a_floor () : Lemma
  (ensures pno_floor (pcut_above (pcut_scope gstack_two_floors)) == true /\
           pno_floor (pcut_above (pcut_scope_far gstack_two_floors)) == false)
  = assert_norm (pno_floor (pcut_above (pcut_scope gstack_two_floors)) == true);
    assert_norm (pno_floor (pcut_above (pcut_scope_far gstack_two_floors)) == false)

(**
 * **GUARD 2: the farthest cut puts somebody else's mode marker inside the
 * residual, under the very guard `pyield` is called with.**
 *
 * The first conjunct is the hypothesis of `lemma_cut_no_mode` -- and it is the
 * branch condition of the two `pstep` value rules that call `pyield`, so it is
 * not an extra assumption. Under it the nearest cut yields a marker-free
 * residual and the farthest cut does not.
 *)
let guard_far_cut_keeps_a_mode () : Lemma
  (ensures None? (pfind_mode gstack_mode_between) /\
           pno_mode (pcut_above (pcut_scope gstack_mode_between)) == true /\
           pno_mode (pcut_above (pcut_scope_far gstack_mode_between)) == false)
  = assert_norm (None? (pfind_mode gstack_mode_between));
    assert_norm (pno_mode (pcut_above (pcut_scope gstack_mode_between)) == true);
    assert_norm (pno_mode (pcut_above (pcut_scope_far gstack_mode_between)) == false)

(**
 * **GUARD 3: the farthest mode search answers with the wrong consumer's mode.**
 *
 * The stack is `ctx_drive`'s own shape twice over: a marker-free residual, the
 * marker the inner consumer just appended, and beneath it an outer consumer's
 * marker with the OTHER mode, then that consumer's floor. `pfind_mode` answers
 * `MResume`, which is the mode of the consumer driving this residual;
 * `pfind_mode_far` answers `MExtend`, which is an outer consumer's. A `PSiteF`
 * in the residual therefore fires under one and not under the other, which is
 * the `MResume`/`MExtend` confusion named in the header at `pfind_mode`.
 *
 * `lemma_find_mode_marker` is the proof that `pfind_mode` cannot do this.
 *)
let gstack_nested_markers : pstack nat nat =
  [PModeF MResume gresp; PModeF MExtend gresp; PScopeF]

let guard_far_mode_answers_outer () : Lemma
  (ensures pmode_of (pfind_mode gstack_nested_markers) == Some MResume /\
           pmode_of (pfind_mode_far gstack_nested_markers) == Some MExtend)
  = assert_norm (pmode_of (pfind_mode gstack_nested_markers) == Some MResume);
    assert_norm (pmode_of (pfind_mode_far gstack_nested_markers) == Some MExtend)

(**
 * **`pfind_token` IS DELETED, and its absence is conditions 4 and 7.**
 *
 * B1.6 had, here, a search for the nearest `PTokenF` -- a context found exactly
 * as a cell is found. That is the one step this gate rejects, so what stands in
 * its place is nothing at all: **no function in this module takes a `pstack` and
 * returns a `pctx`.** `presolve` is the only route to a context, it is given a
 * store and a handle and never a stack, and a handle that does not resolve gets
 * `PStuck` rather than a neighbour's context.
 *
 * Stated as a property of the file rather than of a proof: grep the signatures
 * below and no consumer of `pstack v cl` produces a `pctx v cl`. That is a
 * syntactic observation, not a checked theorem, and it is recorded as such.
 *
 * **Re-checked after B2a, because B2a added functions that take stacks.**
 * `pno_floor`, `pno_mode`, `presid_wf`, `pcut_scope_far`, `pfind_mode_far` and
 * `pcut_above` all take a `pstack` and none returns a `pctx`. The one function
 * that both takes a stack and mentions `pctx` is `gdrive`, the harness under
 * `guard_far_drive_reyields`; it BUILDS a `PCtxRequests` from a residual written
 * by hand at concrete types, which is what a harness for the consumption rules
 * has to do, and it is not reachable from any transition. No new resolution path
 * from a stack to a context was added.
 *)

(** **The action a consumer with no context in scope degenerates to.** It is an
    ordinary `PPerform` under a reserved label, in the style of
    `Hoop.Runtime.Semantics.var_eff`, so the machine reports it as `PStuck` with
    a name a reader can act on rather than through a state of its own. It is
    unreachable from a well-formed clause -- a consuming node only occurs in a
    production's continuation -- and `fixture_9_consumer_without_token` is the
    check that it is reported rather than silently mistaken for something else. *)
let pctx_eff : string = "%hoop.ctx"
let pctx_missing_op : string = "no-context-in-scope"

(**
 * **Forming the token at a frame that has no consumer** -- the shared tail of the
 * `PBoundaryF` and `PSiteF` value rules.
 *
 * `hd` is the frame the value arrived at, and it goes into the residual as its
 * head: the residual begins with the frame whose meaning the consumer decides,
 * which is what `ctx_drive` relies on when it splices the residual back and
 * hands the value to it.
 *
 * `post` starts as `PVar`, the inner monad's `pure`; extensions compose onto it
 * (see `extend_ctx_C`).
 *
 * With no floor to cut at there is nowhere for control to go, and the machine
 * answers `PPaused`. No transition of this machine builds such a stack -- a
 * boundary or a site frame is only ever pushed by `PEnterCtx`, which pushes a
 * floor beneath it, or restored by a splice of frames that were pushed that way.
 * This arm is a totality obligation, and `fixture_9_paused_is_unreachable` is
 * the check that the fixtures do not reach it.
 *
 * **What changed in B1.7, and it is condition 1.** B1.6 cut the floor to get the
 * continuation the floor was HOLDING, and pushed the context onto a `PTokenF`
 * frame beneath it. The floor holds nothing now: the residual is ALLOCATED, and
 * the machine goes on with `PVar h` -- an ordinary value step, on `below`, with
 * the handle in the value position. Whatever `PBindF` the program wrote after
 * `runScope` receives it, and can keep it, pass it, or select between it and
 * another. Production yields a value exactly once, at the one point control
 * leaves the scope through the floor.
 *)
let pyield (#v #cl: Type) (x: pval v) (hd: pframe v cl) (rest: pstack v cl)
           (cf: pconf v cl)
  : pconf v cl
  = match pcut_scope rest with
    | None -> { cf with st = PPaused x (hd :: rest) }
    | Some (above, below) ->
      let (h, cf') = palloc (PCtxRequests x (hd :: above) (PVar #v #cl)) cf in
      { cf' with st = PStep (PVar h) below }

(**
 * **THE PRODUCTION-SIDE THEOREM: every residual this machine stores is well
 * formed.** PROVED, and the hypotheses are exactly the two branch conditions
 * `pstep` reaches this function under.
 *
 * The first hypothesis, `pfind_mode rest == None`, is not a well-bracketing
 * assumption smuggled in: it is the guard on the `None` arm of the `PBoundaryF`
 * and `PSiteF` value rules, and those two arms are the only callers. The second
 * says the head frame is one of those two, which is likewise what the callers
 * pass. Nothing here assumes anything about how the stack was built.
 *
 * The conclusion is `presid_wf` on the segment that is HANDED TO THE STORE,
 * together with where it is stored and what the machine goes on with. Read
 * together with `lemma_ctx_drive_answers_head` below, the two make the
 * association discipline a closed argument: production only ever stores
 * residuals whose head frame is reachable by the mode search, and consumption
 * only ever asks the mode search about such a residual.
 *
 * **This is where nearness is load-bearing.** Both conjuncts of `presid_wf` come
 * from `pcut_scope` being the NEAREST cut: `lemma_cut_no_floor` needs it
 * outright, and `lemma_cut_no_mode` needs it to compose with `pfind_mode`'s own
 * termination at the first floor. `guard_far_cut_keeps_a_floor` and
 * `guard_far_cut_keeps_a_mode` are the same two conjuncts evaluated for
 * `pcut_scope_far`, and both are `false`.
 *
 * **WHAT IS HANDED TO STRAND 2, and it is one thing.** This lemma and
 * `lemma_ctx_drive_answers_head` are both LOCAL: each takes a branch condition
 * of `pstep` as its hypothesis and says what that step does. Neither says that
 * the machine, started from `pload`, only ever reaches stacks of the shapes they
 * describe -- and neither needs to, because their hypotheses are guards and not
 * shape assumptions. What strand 2 would ADD is the configuration-wide
 * statement: extend `pconf_wf` -- today only the store's freshness invariant --
 * with a stack condition, and prove `pstep` preserves it. `pno_floor` and
 * `pno_mode` are deliberately predicates on a SEGMENT and mention no `pconf`, so
 * they can be reused unchanged; `presid_wf` is the property strand 2 would want
 * to assert of every residual IN THE STORE, and this lemma is the step case for
 * the two rules that write one.
 *
 * The one place a reader might expect a reachability claim and will not find one
 * is `guard_far_drive_reyields`, which exhibits a separating stack without
 * exhibiting a program that builds it. That is deliberate and is stated there.
 *
 * **A warning strand 2 must not walk past.** "Every reachable stack is
 * well-bracketed" is FALSE for an arbitrary initial `pcomp` and an arbitrary
 * `papply_t`. A raw `PSplice` can push any frame list it likes, and `apply` can
 * return one. So the theorem is not `pload`-to-`pstep` preservation
 * unconditionally; it needs a well-scopedness condition on the initial term and
 * a preservation condition on the clause interpreter -- the counterparts of the
 * shipped machine's `ws` / `apply_ok` / `config_ok`. An unconditional statement
 * here would either be false or would have been narrowed until it was not about
 * this machine.
 *
 * Note also that the store holds `PCtxRequests` values, which carry a
 * `post: pval v -> pcomp v cl` beside the residual. If `post` may return an
 * ill-formed `PSplice`, keeping every residual `presid_wf` does not close
 * reachability. Whether the function component needs a condition of its own is
 * the first thing strand 2 should settle, before building the layers above it.
 *)
let lemma_pyield_residual_wf
    (#v #cl: Type) (x: pval v) (hd: pframe v cl)
    (rest: pstack v cl) (cf: pconf v cl)
  : Lemma (requires pfind_mode rest == None /\ (PBoundaryF? hd \/ PSiteF? hd))
          (ensures (match pcut_scope rest with
                    | None -> PPaused? (pyield x hd rest cf).st
                    | Some (above, below) ->
                      presid_wf (hd :: above) /\
                      (pyield x hd rest cf).st == PStep (PVar (PCtxKey cf.next)) below /\
                      (match pstore_lookup cf.next (pyield x hd rest cf).store with
                        | Some cx -> PCtxRequests? cx /\
                                     PCtxRequests?.value cx == x /\
                                     PCtxRequests?.residual cx == hd :: above
                        | None -> False)))
  = lemma_cut_no_floor rest;
    lemma_cut_no_mode rest

(** The delimited continuation handed to a clause, named for the reason
    `Hoop.Runtime.Semantics.kont_of` is named: a top-level symbol, so that facts
    about it are facts about one function rather than about whatever lambda a
    transition happened to build. *)
let pkont_of (#v #cl: Type) (captured: pstack v cl) (x: pval v) : pcomp v cl
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
 * **The value rules are the protocol**, and they are the only rules in the
 * machine that consult something other than the frame in front of them:
 *
 *   - `PModeF` is inert. A value passing a marker is a protocol that has
 *     finished; the marker is popped like a cell.
 *   - `PBoundaryF` with a mode in scope hands the value to that mode's responder
 *     and CONTINUES UNDER THE REST OF THE STACK, marker included, so the next
 *     boundary hit finds the same marker. With no mode in scope it YIELDS: the
 *     stack is cut at the scope floor and the token goes to the floor's
 *     continuation.
 *   - `PSiteF` with no mode in scope yields too, and for the same reason: the
 *     layers have finished, a recorded perform-site frame is next, and whether
 *     it fires is not yet known. With a mode in scope it is a `PBindF` under
 *     `MResume` and a no-op under `MExtend`.
 *   - `PScopeF` reached by a value DIRECTLY is a scope that drained without ever
 *     asking for anything: the residual is `PCtxDone`, it is ALLOCATED, and the
 *     machine goes on with the handle in the value position. This is the rule
 *     that used to be `PDone y -> PCtxDone y` in B1.5.s `pctx_of_state`, and the
 *     difference is that "the machine finished" and "the scope finished" are no
 *     longer the same event -- there is a stack below.
 *   - A handle a program never consumes is simply a value it dropped. The store
 *     entry stays, because the store is append-only; reclaiming it is an
 *     optimisation with an obligation, not the semantics.
 *
 * **`PEnterCtx` is the whole of production and it is four frames.** Boundary on
 * top, the plan's protocol frames beneath it, the floor beneath those, and the
 * ambient stack -- UNTOUCHED -- beneath that. No fuel, no lookup, no clause
 * interpreter, no `psteps`. The rule cannot inspect `body`, only push frames
 * under it.
 *
 * Nothing here looks inside a clause and nothing here assumes what `apply`
 * returns; see the note at `papply_t`.
 *)
let pstep (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Tot (pconf v cl)
  = let keep (s: pstate v cl) : pconf v cl = { cf with st = s } in
    match cf.st with
    | PDone _ -> cf
    | PPaused _ _ -> cf
    | PStuck _ _ -> cf
    | PRejected _ -> cf
    | PStep c k ->
      match c with
      | POp comp fn -> keep (PStep comp (PBindF fn :: k))
      | PHandle tbl ret prov body -> keep (PStep body (PPromptF tbl ret prov :: k))
      | PPerform eff op payload ->
        (match pfind_prompt lk eff op k with
          | None -> keep (PStuck eff op)
          | Some (captured, found, below) ->
            (match found.kind with
              | KScoped ->
                keep (PRejected (ClauseKindMismatch eff op KOrdinaryOperation KScoped))
              | _ -> keep (PStep (apply found.body payload (pkont_of captured)) below)))
      // **An observation.** The event is invisible to `pstep`, which reports only
      // a state; `pstep_tr` below is what reports it, and `prun` is what
      // accumulates. Keeping the event out of `pstate` is what makes requirement
      // 1 -- the trace is not preserved into the residual -- true by the TYPE of
      // the residual rather than by a check on its contents.
      | PEmit _ body -> keep (PStep body k)
      // **Entering a scope**: build the plan, then run the body under it. The
      // plan is what can fail, and it fails into the rejection the shipped
      // machine already produces -- the origin naming the scope, the labels
      // naming what stood in its way.
      | PWeave oeff oop ints own body ->
        (match plan_of ints own with
          | Inl (MonomorphicLayer bs) -> keep (PRejected (UnborrowableScope oeff oop bs))
          | Inr pl -> keep (PStep (enter_C pl body) k))
      // **Production**, and it is B1.6's rule with one field fewer: four frames
      // on the live stack, and no continuation carried on the node. The handle
      // is produced later, by the value rule, at the floor.
      | PEnterCtx pl body ->
        keep (PStep body (PBoundaryF :: (plan_protocol_frames pl @ (PScopeF :: k))))
      // **The three consuming rules, and each is: RESOLVE THE HANDLE PASSED,
      // then appeal to the operation ONCE.**
      //
      // `presolve cf.store h` is the whole of conditions 4 and 7. It reads `h`
      // -- the value the program wrote -- and the store, and it is not given `k`,
      // so no arm here can consult the stack. A handle that does not resolve is
      // `PStuck`, and that is the same stuck state a consumer with no context at
      // all reaches: there is no third behaviour in which a neighbouring context
      // is used instead.
      | PExtendC pl h g ->
        (match presolve cf.store h with
          | None -> keep (PStuck pctx_eff pctx_missing_op)
          | Some cx -> keep (PStep (extend_C pl cx g) k))
      // **`bindScope`, and it ALLOCATES.** The extended context is a new entry;
      // `h`'s entry is untouched, because `palloc` only conses. The node
      // evaluates to the fresh handle, so `cy <- bindScope cx g` is an ordinary
      // bind and `cx` is still `cx`. That is condition 8.
      | PExtendCtxC pl h g ->
        (match presolve cf.store h with
          | None -> keep (PStuck pctx_eff pctx_missing_op)
          | Some cx ->
            let (h', cf') = palloc (extend_ctx_C pl cx g) cf in
            { cf' with st = PStep (PVar h') k })
      | PResumeC pl h kk ->
        (match presolve cf.store h with
          | None -> keep (PStuck pctx_eff pctx_missing_op)
          | Some cx -> keep (PStep (resume_C pl cx kk) k))
      | PVar value ->
        (match k with
          | [] -> keep (PDone value)
          | PBindF fn :: rest -> keep (PStep (fn value) rest)
          | PParamF _ _ :: rest -> keep (PStep (PVar value) rest)
          | PModeF _ _ :: rest -> keep (PStep (PVar value) rest)
          // **A scope that reached its floor with no request outstanding.** The
          // residual is `PCtxDone`, and it is allocated and handed on as a
          // handle like any other -- a context that made no requests is still a
          // context the surface can hold and select.
          | PScopeF :: rest ->
            let (h, cf') = palloc (PCtxDone value) cf in
            { cf' with st = PStep (PVar h) rest }
          | PBoundaryF :: rest ->
            (match pfind_mode rest with
              | None -> pyield value PBoundaryF rest cf
              | Some (_, respond) -> keep (PStep (respond value) rest))
          | PSiteF fn :: rest ->
            (match pfind_mode rest with
              | None -> pyield value (PSiteF fn) rest cf
              | Some (MResume, _) -> keep (PStep (fn value) rest)
              | Some (MExtend, _) -> keep (PStep (PVar value) rest))
          | PPromptF _ ret _ :: rest ->
            (match ret with
              | Some fn -> keep (PStep (fn value) rest)
              | None -> keep (PStep (PVar value) rest)))
      | PSplice fs body -> keep (PStep body (fs @ k))
      | PNewP l init body -> keep (PStep body (PParamF l init :: k))
      | PReadP l ->
        (match pfind_param l k with
          | None -> keep (PStuck var_eff l)
          | Some x -> keep (PStep (PVar x) k))
      | PWriteP l x ->
        (match pset_param l x k with
          | None -> keep (PStuck var_eff l)
          | Some k' -> keep (PStep (PVar x) k'))

(**
 * **The two value rules that produce a context are exactly the two callers of
 * `pyield`, and they call it under `pfind_mode rest == None`.** PROVED, by
 * unfolding; it is a one-line fact and it is stated because it is the hinge of
 * `lemma_pyield_residual_wf`'s hypothesis.
 *
 * Without it, that lemma's `pfind_mode rest == None` could be read as an
 * assumption about which stacks are considered. With it, the assumption is
 * discharged by the transition relation itself: there is no way to reach
 * `pyield` other than through a `None` from the mode search.
 *)
let lemma_pstep_yield_guard
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (x: pval v) (hd: pframe v cl) (rest: pstack v cl)
  : Lemma (requires (PBoundaryF? hd \/ PSiteF? hd) /\
                    pfind_mode rest == None /\
                    cf.st == PStep (PVar x) (hd :: rest))
          (ensures pstep lk apply cf == pyield x hd rest cf)
  = ()

(**
 * **THE CONSUMPTION-SIDE THEOREM: driving a well-formed residual reaches the
 * DRIVING consumer's marker at the residual's head frame.** PROVED.
 *
 * This is the statement the module has been owing since B1.5, and it is the one
 * that decides the proximity question. Read the conclusion in three parts:
 *
 *   - the splice step puts the residual back with the marker appended beneath
 *     it, so the head frame of the residual is the frame the value meets;
 *   - `pfind_mode` from beneath that head frame returns `Some (m, resp)` -- the
 *     mode AND the responder this consumer just installed, not an outer
 *     consumer's and not `None`;
 *   - therefore the second transition RUNS THE CONSUMER'S RESPONDER (at a
 *     boundary) or is decided by the consumer's MODE (at a site), and in
 *     particular ALLOCATES NOTHING: `cf2.next == cf.next` says the machine did
 *     not yield a second context in the consumer's face.
 *
 * The only hypothesis about the residual is `presid_wf`, which
 * `lemma_pyield_residual_wf` PROVES of every residual this machine stores. So
 * the two together are closed: production establishes the invariant,
 * consumption consumes it, and neither step assumes anything about the ambient
 * stack `k`, which is universally quantified and arbitrary.
 *
 * **Where nearness enters, and what breaks without it.** `presid_wf` is exactly
 * what `pcut_scope`'s nearest cut delivers and what `pcut_scope_far` does not
 * (`guard_far_cut_keeps_a_floor`, `guard_far_cut_keeps_a_mode`). Drop either
 * conjunct and the conclusion is false, not merely unprovable: with a floor in
 * the residual the mode search returns `None` and the second transition is a
 * `pyield`, which allocates -- `guard_far_drive_reyields` runs both machines and
 * checks that it does. With a marker in the residual the search returns the
 * wrong responder. Proximity is therefore a SEMANTIC REQUIREMENT here and not a
 * normal form: the theorem is false under the farthest cut.
 *)
let lemma_ctx_drive_answers_head
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (m: weave_mode)
    (x: pval v) (hd: pframe v cl) (a: pstack v cl)
    (post: pval v -> pcomp v cl) (f: pval v -> pcomp v cl) (k: pstack v cl)
  : Lemma (requires presid_wf (hd :: a))
          (ensures (let resp = (fun (z: pval v) -> pbind (post z) f) in
                    let tl = a @ (PModeF m resp :: k) in
                    let cf0 = { cf with
                                st = PStep (ctx_drive m (PCtxRequests x (hd :: a) post) f) k } in
                    let cf1 = pstep lk apply cf0 in
                    cf1.store == cf.store /\ cf1.next == cf.next /\
                    cf1.st == PStep (PVar x) (hd :: tl) /\
                    pfind_mode tl == Some (m, resp) /\
                    (let cf2 = pstep lk apply cf1 in
                     cf2.store == cf.store /\ cf2.next == cf.next /\
                     (match hd with
                       | PBoundaryF -> cf2.st == PStep (resp x) tl
                       | PSiteF fn ->
                         cf2.st == (if MResume? m
                                    then PStep (fn x) tl
                                    else PStep (PVar x) tl)
                       | _ -> True))))
  = let resp = (fun (z: pval v) -> pbind (post z) f) in
    // `assert_norm` and not `assert`: `ctx_drive` BUILDS the responder lambda,
    // and F* gives a lambda occurring inside a definition an SMT encoding of its
    // own, so the equality between it and the same lambda written here is not
    // something Z3 can see. Normalising both sides makes the two terms identical
    // and the obligation disappears without an SMT query. The same trap is why
    // `lemma_find_mode_through` is stated as transparency rather than as an
    // answer.
    assert_norm (ctx_drive m (PCtxRequests x (hd :: a) post) f
                 == PSplice ((hd :: a) @ [PModeF m (fun z -> pbind (post z) f)])
                            (PVar x));
    append_assoc (hd :: a) [PModeF m resp] k;
    lemma_find_mode_marker a m resp k

(**
 * **The same transition, reporting what it observed** -- the instrument, and the
 * whole of B1.6's answer to requirements 1 to 4.
 *
 * It is a WRAPPER and not a second copy of `pstep`: exactly one node emits, so
 * exactly one case has to be intercepted, and every other transition is `pstep`'s
 * verbatim. A duplicated step relation would be two definitions of the semantics
 * that could drift, and the file would then be measuring one of them while the
 * laws spoke about the other.
 *
 * The event list is `[]` or a singleton. It is a list rather than an `option` so
 * that `prun` accumulates with `@` and the trace of a run is literally the
 * concatenation of the traces of its steps -- which is what makes "this event
 * appears once" a statement about a list and not about a counter.
 *)
let pstep_tr (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Tot (pconf v cl & list string)
  = match cf.st with
    | PStep (PEmit ev body) k -> ({ cf with st = PStep body k }, [ev])
    | _ -> (pstep lk apply cf, [])

(** The iteration of `pstep`, cut off at `fuel` transitions -- the shape of
    `Hoop.Runtime.Semantics.steps`, so that the laws below can be stated in the
    same idiom the shipped monad laws are stated in. `PPaused` is terminal, or
    production would never return a context. *)
let rec psteps (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (fuel: nat) (cf: pconf v cl)
  : Tot (pconf v cl) (decreases fuel)
  = if fuel = 0 then cf
    else
      match cf.st with
      | PDone _ -> cf
      | PPaused _ _ -> cf
      | PStuck _ _ -> cf
      | PRejected _ -> cf
      | PStep _ _ -> psteps lk apply (fuel - 1) (pstep lk apply cf)

(* ---- B2a GUARD 4: the farthest cut, RUN ---------------------------- *)

(**
 * **The two residuals, driven, side by side.**
 *
 * `lemma_ctx_drive_answers_head` says what happens when a WELL-FORMED residual
 * is driven. This is the same drive on the residual the farthest cut would have
 * stored instead, run by the same machine, and the two disagree about the
 * ANSWER and not merely about the segment.
 *
 * Both residuals come from the same yield: the stack is `gstack_mode_between`,
 * the guard `pfind_mode` returns `None` on it, and the head frame is a boundary.
 * `pcut_scope` takes nothing above the nearest floor; `pcut_scope_far` takes the
 * floor and the outer consumer's marker with it. Then a consumer resumes with a
 * continuation that answers `PV 7`.
 *
 *   - Nearest: the value meets the boundary, the search finds the resuming
 *     consumer's marker, the continuation runs, the answer is `PV 7`, and the
 *     store is untouched -- `next` is still `0`.
 *   - Farthest: the value meets the boundary, the search hits the floor that
 *     was swept into the residual and returns `None`, so the machine YIELDS
 *     AGAIN -- it allocates a second context (`next` becomes `1`) and the answer
 *     is that context's HANDLE. The consumer's continuation is never applied.
 *
 * That is `resumeScope cx k` failing to resume, on a machine that has no fixture
 * to say so. It is the separation B1.6 and B1.7 each looked for and did not
 * find, and what they were missing was not the handle representation: it was a
 * mode marker between the two floors, which no fixture in this file builds. Both
 * ingredients are ones the machine makes -- `PEnterCtx` pushes the floors,
 * `ctx_drive` appends the marker -- so this is a statement about frames this
 * transition system produces and not about an arbitrary list.
 *
 * **What is checked here and what is not.** CHECKED: that the two residuals
 * exist, that the guard `pyield` is called under holds of the stack they come
 * from, and that driving them gives different answers and different store sizes.
 * NOT CHECKED HERE: that a program reaches THIS stack, which is written by hand.
 * `fixture_22_separating_state_is_reachable` supplies the missing half from the
 * other side -- a closed program whose run reaches a configuration at which the
 * nearest cut satisfies both conjuncts of `presid_wf` and the farthest cut
 * satisfies neither -- so between the two nothing is left to argument except the
 * splice of one into the other. What remains genuinely open is the general
 * statement that EVERY reachable stack is well bracketed, which is `pconf_wf`
 * preservation and strand 2's; see the note at `lemma_pyield_residual_wf`.
 *)
let glk : plookup_t nat = fun _ _ _ -> None
let gapply : papply_t nat nat = fun _ _ _ -> PVar (PV 0)
let gk_answer : pval nat -> pcomp nat nat = fun _ -> PVar (PV 7)

(** The two residuals the two cuts would store, head frame included. *)
let gresid_near : pstack nat nat =
  PBoundaryF :: pcut_above (pcut_scope gstack_mode_between)
let gresid_far : pstack nat nat =
  PBoundaryF :: pcut_above (pcut_scope_far gstack_mode_between)

(** `resumeScope` on a residual, on an empty ambient stack. *)
let gdrive (resid: pstack nat nat) : pconf nat nat =
  { st = PStep (ctx_drive MResume
                          (PCtxRequests (PV 1) resid (PVar #nat #nat))
                          gk_answer)
               [];
    store = [];
    next = 0 }

let gresult (cf: pconf nat nat) : option (pval nat)
  = match cf.st with
    | PDone y -> Some y
    | _ -> None

let guard_far_drive_reyields () : Lemma
  (ensures presid_wf gresid_near == true /\
           presid_wf gresid_far == false /\
           gresult (psteps glk gapply 20 (gdrive gresid_near)) == Some (PV 7) /\
           (psteps glk gapply 20 (gdrive gresid_near)).next == 0 /\
           gresult (psteps glk gapply 20 (gdrive gresid_far)) == Some (PCtxKey 0) /\
           (psteps glk gapply 20 (gdrive gresid_far)).next == 1)
  = assert_norm (presid_wf gresid_near == true);
    assert_norm (presid_wf gresid_far == false);
    assert_norm (gresult (psteps glk gapply 20 (gdrive gresid_near)) == Some (PV 7));
    assert_norm ((psteps glk gapply 20 (gdrive gresid_near)).next == 0);
    assert_norm (gresult (psteps glk gapply 20 (gdrive gresid_far)) == Some (PCtxKey 0));
    assert_norm ((psteps glk gapply 20 (gdrive gresid_far)).next == 1)

(**
 * **The same iteration, keeping the trace** -- the driver requirement 1 is about.
 *
 * The trace is a SECOND RESULT of the driver and is not part of any state, of
 * any frame, or of a `pctx`. That is requirement 1 discharged by construction:
 * "the observation trace is not preserved into the residual" is not a property
 * that had to be checked of the residual, because there is nowhere in a residual
 * for it to be. A residual re-driven emits what the transitions it then takes
 * emit, and nothing else -- so an emission its prefix already made cannot come
 * back. `fixture_11_prefix_event_once` is the run that exhibits it, and
 * `fixture_12_suspension_emits_twice` is the control that shows the instrument
 * is measuring something.
 *
 * `psteps` above is kept and is not defined through this one. The laws are stated
 * over `pconverges`, which is about values, and threading a trace through them
 * would make every law also a statement about observations -- which is a
 * different and much stronger claim than B2 is being asked for.
 *)
let rec prun (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
             (fuel: nat) (cf: pconf v cl)
  : Tot (pconf v cl & list string) (decreases fuel)
  = if fuel = 0 then (cf, [])
    else
      match cf.st with
      | PDone _ -> (cf, [])
      | PPaused _ _ -> (cf, [])
      | PStuck _ _ -> (cf, [])
      | PRejected _ -> (cf, [])
      | PStep _ _ ->
        let (cf', ev) = pstep_tr lk apply cf in
        let (cff, tr) = prun lk apply (fuel - 1) cf' in
        (cff, ev @ tr)

(** **Loading a program**, and note the store starts EMPTY and `next` at zero.
    Every handle a run can resolve was therefore allocated by that run, which is
    the half of condition 7 that is about provenance rather than about lookup: a
    program cannot smuggle in a handle that happens to work, because at the
    moment it starts there is nothing for any handle to resolve to. *)
let pload (#v #cl: Type) (c: pcomp v cl) : pconf v cl
  = { st = PStep c []; store = []; next = 0 }

(** **The number of transitions to a settled state**, or `None` if the machine
    got stuck, was rejected, or did not settle within `fuel`. It exists for
    `fixture_1_prefix_runs_once`, which is a claim about WORK and can therefore
    not be made with `pobs_eq`; see the finding recorded there. *)
let rec pcost (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
              (fuel: nat) (cf: pconf v cl)
  : Tot (option nat) (decreases fuel)
  = match cf.st with
    | PDone _ -> Some 0
    | PPaused _ _ -> Some 0
    | PStuck _ _ -> None
    | PRejected _ -> None
    | PStep _ _ ->
      if fuel = 0 then None
      else (match pcost lk apply (fuel - 1) (pstep lk apply cf) with
            | None -> None
            | Some n -> Some (n + 1))

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
(*  IN B1.6 ALL FIVE FIELDS BUILD SYNTAX, AND NO FIELD MENTIONS A        *)
(*  `pctx` AT ALL. B1.5's `o_enter_ctx` took a lookup, a clause          *)
(*  interpreter and a fuel bound and returned a `pctx`, and the design   *)
(*  note is right that this is detached evaluation visible in a type     *)
(*  before any behaviour is examined: an operation that needs the        *)
(*  interpreter is an operation that RUNS the program. Every field is    *)
(*  now `... -> pcomp v cl`, so an implementation cannot run anything,   *)
(*  because it is not given anything to run with. That is the stop       *)
(*  condition, enforced by the record's type rather than by a reading of *)
(*  its inhabitants.                                                     *)
(*                                                                     *)
(*  IN B1.7 THE THREE CONSUMING FIELDS TAKE A `pval v` -- THE HANDLE.    *)
(*  B1.6 removed the `pctx` arguments for the wrong reason: not because  *)
(*  an operation should not name its context, but because under the      *)
(*  defunctionalisation there was no way to name one, so the fields said *)
(*  "the context in scope". A `pval v` restores the argument WITHOUT     *)
(*  restoring detached evaluation, because a handle is an object-language*)
(*  value and not a `pctx`: the field still cannot run anything, since it*)
(*  is still handed no store, no lookup and no fuel. Resolution is the   *)
(*  machine's, and a `ctx_ops` cannot perform it.                        *)
(*                                                                     *)
(*  That is the distinction the gate turns on. "Takes the context it     *)
(*  consumes" and "is given the means to evaluate" are different         *)
(*  properties, and B1.6 gave up the first to secure the second. The     *)
(*  handle buys back the first at no cost to the second, and the type    *)
(*  below is where that is visible.                                     *)
(*                                                                     *)
(*  `o_enter_ctx` LOST its `kbody`. Production evaluates to a value now, *)
(*  so it needs no continuation of its own -- and the field's arity is   *)
(*  condition 1 stated in the record.                                    *)
(* ------------------------------------------------------------------ *)

noeq
type ctx_ops (v: Type) (cl: Type) = {
  o_enter: plan v cl -> pcomp v cl -> pcomp v cl;
  o_enter_ctx: plan v cl -> pcomp v cl -> pcomp v cl;
  o_extend: plan v cl -> pval v -> (pval v -> pcomp v cl) -> pcomp v cl;
  o_extend_ctx: plan v cl -> pval v -> (pval v -> pcomp v cl) -> pcomp v cl;
  o_resume: plan v cl -> pval v -> (pval v -> pcomp v cl) -> pcomp v cl;
}

(** **The reference semantics**, as data. *)
let ref_ops (#v #cl: Type) : ctx_ops v cl = {
  o_enter = enter_C;
  o_enter_ctx = enter_ctx_C;
  o_extend = extend_at_C;
  o_extend_ctx = extend_ctx_at_C;
  o_resume = resume_at_C;
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
 * **And in B1.6 it gets shorter still.** Its `o_enter_ctx` is now the reference
 * NODE at a shorn plan -- the owner alone, with the layers thrown away -- rather
 * than a second detached evaluator. There is nothing left in the field for an
 * alternative implementation to be wrong in EXCEPT the plan it enters under,
 * which is exactly the thing this counterexample is about.
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
  let owner_only (pl: plan v cl) : plan v cl = Plan [] (Plan?.owner pl) in
  {
    o_enter = (fun pl c -> PSplice [owner_frame (Plan?.owner pl)] c);
    o_enter_ctx = (fun pl c -> PEnterCtx (owner_only pl) c);
    o_extend = extend_at_C;
    o_extend_ctx = extend_ctx_at_C;
    o_resume = resume_at_C;
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
    (fun pl h g -> PExtendC pl h (fun x -> PSplice (plan_enter_frames pl) (g x)));
  o_extend_ctx =
    (fun pl h g -> PExtendCtxC pl h (fun x -> PSplice (plan_enter_frames pl) (g x)));
  o_resume =
    (fun pl h k -> PResumeC pl h (fun x -> PSplice (plan_resume_frames pl) (k x)));
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
(*  A NOTE B1.5 LEFT AND B1.6 ANSWERS ELSEWHERE. This relation still    *)
(*  cannot see the defect B1 was withdrawn for. It observes VALUES, and *)
(*  a replayed pure prefix returns what it returned before, so          *)
(*  `pobs_eq` cannot separate the residual from the suspension and it   *)
(*  would be wrong to claim it does. What B1.6 adds is not a stronger   *)
(*  relation but a coarser observable: `PEmit` and `prun`, outside the  *)
(*  value language entirely. Exact-once is `fixture_11` against         *)
(*  `fixture_12`, on traces; `fixture_1_prefix_runs_once` stays as a    *)
(*  regression test on cost and is no longer offered as the semantic    *)
(*  statement.                                                          *)
(* ------------------------------------------------------------------ *)

let pconverges (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (cf: pconf v cl) (x: pval v) : GTot prop =
  exists (n: nat). (psteps lk apply n cf).st == PDone x

(**
 * **The observation, and in B1.7 it quantifies over the STORE as well as the
 * stack.**
 *
 * B1.6's version ranged over `k` alone, and the comment on `ctx_ops` claimed
 * that this was what quantified over "which context" a consuming operation
 * meant -- a stack being where a `PTokenF` lived. That reading is withdrawn with
 * the frame. A context now lives in the store, so a computation mentioning a
 * handle has a meaning only RELATIVE to a store, and an observation that fixed
 * the store at empty would be an observation about programs that have not yet
 * produced anything.
 *
 * Both sides start in the SAME configuration -- same stack, same store, same
 * counter -- and that is what makes the comparison fair. Quantifying the store
 * existentially, or letting the two sides start from different ones, would let
 * an implementation pass a law by allocating differently rather than by meaning
 * the same thing.
 *
 * `next` is quantified too. Two runs that allocate must be comparable at every
 * starting counter, or a law could hold only for programs that happen to be the
 * first allocation in their run.
 *)
let pobs_le (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
            (c1 c2: pcomp v cl) : GTot prop =
  forall (k: pstack v cl) (sto: pstore v cl) (n0: nat) (x: pval v).
    pconverges lk apply ({ st = PStep c1 k; store = sto; next = n0 }) x ==>
    pconverges lk apply ({ st = PStep c2 k; store = sto; next = n0 }) x

let pobs_eq (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
            (c1 c2: pcomp v cl) : GTot prop =
  pobs_le lk apply c1 c2 /\ pobs_le lk apply c2 c1

(* ------------------------------------------------------------------ *)
(*  The laws -- DEFINED, not proved                                    *)
(*                                                                     *)
(*  Each is a DEFINITION whose type is `prop`. None is a `val` without  *)
(*  a proof, none is assumed, and NOTHING IN THIS MODULE DEPENDS ON ANY *)
(*  OF THEM HOLDING: no operation, no transition, no fixture and no     *)
(*  other definition mentions them. Proving them is B2's job. B1.6's    *)
(*  job, like B1.5's, is to keep them STATABLE -- a representation that *)
(*  cannot express associativity has already failed, and one that can   *)
(*  express it only of a fixed implementation cannot be used to rule a  *)
(*  wrong one out.                                                      *)
(*                                                                     *)
(*  They are stated over `ctx_ops`, so `law_X ops ...` is a proposition *)
(*  about an implementation. The intended readings are                  *)
(*                                                                     *)
(*    law_X lk apply ref_ops ...             -- B2b is to prove these   *)
(*    ~(law_X lk apply pointwise_ops ...)    -- refused by all four     *)
(*    ~(law_X lk apply flat_ops ...)         -- refused by the two      *)
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
(*  WHAT B1.6 CHANGED, AND IT IS THE SHAPE OF EVERY STATEMENT.          *)
(*                                                                     *)
(*  B1.5's laws read "produce a context, then consume it", with the     *)
(*  production a meta-level term inside the proposition:                *)
(*                                                                     *)
(*    settles ... ==> pobs_eq lk apply                                  *)
(*      (ops.o_extend pl (ops.o_enter_ctx lk apply fuel pl c) g) ...    *)
(*                                                                     *)
(*  Both the `fuel` and the `settles` are gone, and neither by          *)
(*  weakening. A law now compares two PROGRAMS, and the production      *)
(*  appears in the left-hand one as the node it is, with the consumption*)
(*  written in the continuation it hands the token to. That is the same *)
(*  shape the gate demands of the exact-once fixture, for the same      *)
(*  reason: a token produced at the meta level invites F*'s             *)
(*  normalisation to decide what the machine was supposed to.           *)
(*                                                                     *)
(*  `settles` -- "production performs no operation outside the plan" -- *)
(*  IS REMOVED AND NOT WEAKENED. It was never a fact about the algebra; *)
(*  it was the condition under which B1.5's detached production agreed  *)
(*  with a real one, and there is no detached production left to        *)
(*  disagree. The argument that it may go, STATED AND NOT PROVED: both  *)
(*  sides of every law below are computations, `pobs_eq` plugs both     *)
(*  into the SAME arbitrary stack `k`, and an operation the plan does   *)
(*  not handle is then found by the same `pfind_prompt` walk on both    *)
(*  sides -- so an unhandled operation can no longer make one side      *)
(*  stuck while the other proceeds. What the laws now quantify over     *)
(*  therefore includes every ambient handler context, which is strictly *)
(*  more than B1.5 stated. Whether they HOLD there is B2b's, and this   *)
(*  file does not claim it.                                            *)
(*                                                                     *)
(*  Two further laws belong to B3. `law_transparent_agrees` below is    *)
(*  one of them and is stated, unproved, because gate condition 6 asks  *)
(*  for it; the other -- plan composition matching handler nesting --   *)
(*  needs the optimized machine that does not exist yet and is not      *)
(*  stated at all.                                                      *)
(* ------------------------------------------------------------------ *)

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
 *
 * The left-hand side is one PROGRAM: produce, and extend in the continuation
 * that receives the token. That is B1.6's shape throughout, and it is what lets
 * the hypothesis come off -- there is no longer a production that could have
 * failed separately from the program it belongs to.
 *)
let law_left_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (g: pval v -> pcomp v cl)
  : GTot prop
  = pobs_eq lk apply
      (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_extend pl cx g))
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
 * It is also the law that will make B2b prove the bridging fact of the whole
 * B1.5 design: the left-hand side runs `c` under `plan_protocol_frames pl` in
 * `MExtend`, the right-hand side under `plan_enter_frames pl`, and the two agree
 * exactly because a `PSiteF` under `MExtend` is nothing at all.
 *
 * In B1.6 it acquires a second job, and it is the harder one: `c` is arbitrary,
 * `pobs_eq` plugs both sides into an arbitrary stack, and the left-hand side
 * runs `c` with a boundary, the plan and a floor above that stack while the
 * right-hand side runs it with the plan alone. An operation of `c` that no plan
 * prompt handles reaches the same ambient handler on both sides -- but on the
 * left the segment that handler captures contains the scope's frames, so its
 * resumption re-enters the scope, and on the right it does not have to. That
 * they still agree is exactly what `settles` used to assume away.
 *)
let law_right_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pobs_eq lk apply
      (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
      (ops.o_enter pl c)

(**
 * **Associativity of extension.** Two conjuncts, and the second is there because
 * the first was checked against the counterexample and found insufficient.
 *
 * *The algebraic half* quantifies over an ARBITRARY CONTEXT, and **in B1.7 it
 * takes a parameter for it again.** B1.6 dropped the parameter and claimed
 * `pobs_eq`'s quantification over stacks stood in for it, a token being a frame.
 * That claim goes with the frame: a context is a handle now, so the law names
 * one, `cx`, and `pobs_le`'s quantification over the STORE is what ranges over
 * what `cx` may resolve to -- including the stores where it resolves to nothing,
 * in which both sides are `PStuck` and the case is vacuous rather than
 * accidentally true. The law is thereby stated about the context the program
 * PASSES, which is the whole of the gate, and B1.6's version could not say that.
 * It compares the
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
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
    (cx: pval v)
    (g h: pval v -> pcomp v cl)
  : GTot prop
  = // the algebraic half -- at the context `cx` NAMES, both sides built from `ops`
    pobs_eq lk apply
      (pbind (ops.o_extend_ctx pl cx g) (fun cy -> ops.o_extend pl cy h))
      (ops.o_extend pl cx (fun x -> pbind (g x) h))
    /\ // the anchored half -- one crossing of THIS plan, and no other
    pobs_eq lk apply
      (pbind (ops.o_enter_ctx pl c)
             (fun c0 -> pbind (ops.o_extend_ctx pl c0 g)
                              (fun cy -> ops.o_extend pl cy h)))
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
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (k: pval v -> pcomp v cl)
  : GTot prop
  = pobs_eq lk apply
      (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_resume pl cx k))
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
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pobs_eq lk apply
      (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
      (PSplice (plan_enter_frames pl) c)

(* ------------------------------------------------------------------ *)
(*  FIXTURES -- the gate conditions, CHECKED                           *)
(*                                                                     *)
(*  Every claim below is an `assert_norm` over a concrete run, not a    *)
(*  comment. The value and clause types are the prototype's `v` and     *)
(*  `cl` instantiated at something computable, exactly as               *)
(*  `Hoop.Runtime.Test` does for the shipped machine.                   *)
(*                                                                     *)
(*  EVERY PRODUCTION BELOW IS IN THE OBJECT LANGUAGE. B1.5 wrote        *)
(*  `let cx = fmk pl body` and then used `cx` twice, which asks F*'s    *)
(*  normaliser -- and its sharing and substitution -- what the answer   *)
(*  should be rather than asking the machine. There is no `fmk` any     *)
(*  more and there cannot be one: production is a node, so a fixture    *)
(*  is a closed `pcomp` and the token exists only during the run. Where *)
(*  a fixture needs to inspect the token it does so from inside, in the *)
(*  continuation the machine hands it to, and reports what it found as  *)
(*  an ordinary value.                                                  *)
(*                                                                     *)
(*  THE B1.5 FIXTURE-SIDE RESTRICTION IS PARTLY LIFTED. B1.5 recorded   *)
(*  that `flook` had to ignore its table argument, `handlers` being     *)
(*  abstract, so every prompt dispatched the same operations. That is   *)
(*  no longer true: `flook` reads `binds` off the `ptable`, so a        *)
(*  fixture can put an effect outside a prompt's reach, which is what   *)
(*  requirement 5 is about. What remains is that `binds` is supplied by *)
(*  the fixture rather than derived from `hs` -- see `ptable`.          *)
(* ------------------------------------------------------------------ *)

type fv =
  | FU
  | FI: int -> fv
  | FS: string -> fv
  | FL: list fv -> fv

(** The clause language the fixtures run with. Real clauses are opaque
    PureScript closures; these are the shapes the conditions need --
    tail-resumptive, multi-shot, discarding, the two that make a decision AFTER a
    round trip, and (new in B1.6) one that resumes and then has work left, which
    is what an outer handler needs in order for requirement 6 to have any
    content. *)
noeq
type fcl =
  | FEcho                        (* resume with payload[0] -- tail-resumptive   *)
  | FTwice: fv -> fv -> fcl      (* resume twice, collect both answers          *)
  | FAbort: fv -> fcl            (* never resume -- the `Full` shape            *)
  | FRetry                       (* resume again only if the first answer says  *)
  | FBetween                     (* resume, perform, resume                     *)
  | FWrap                        (* resume, then WRAP -- pending frames below   *)

let fneeds_retry (x: fv) : bool = match x with | FS "retry" -> true | _ -> false

(** Injection and return, so the fixtures below read as programs rather than as
    a column of `PV`s. *)
let fpv (x: fv) : pval fv = PV x
let fret (x: fv) : pcomp fv fcl = PVar (PV x)

(**
 * **What a fixture SEES when a handle reaches a value position**, and it exists
 * for the fixtures and for nothing else.
 *
 * The value language is `pval fv` now, so a clause that combines two answers has
 * to say what it means to combine things that might be handles. `fseen` is that
 * choice: an ordinary value is itself, and a handle becomes the tagged pair
 * `FL [FS "ctx"; FI i]`.
 *
 * **This is an observer, and it is deliberately NOT available to the machine.**
 * No transition applies it; `pstep` never takes a `pval` apart to see whether it
 * is a handle, and `presolve` is the only thing that looks inside one. A handle
 * is opaque to the SEMANTICS -- condition 1's word -- and the fixtures are
 * entitled to break that opacity because their whole job is to report what the
 * machine did. Without it, "these two handles are different" could not be
 * written down as a value, and conditions 1, 2 and 8 would be unstatable.
 *
 * The `FI i` retains the id, which is what lets a fixture check WHICH context it
 * was given rather than merely that it was given one.
 *)
let fseen (h: pval fv) : fv =
  match h with
  | PV x -> x
  | PCtxKey i -> FL [FS "ctx"; FI i]

let fapply : papply_t fv fcl = fun c payload k ->
  match c with
  | FEcho -> (match payload with | x :: _ -> k x | [] -> k (fpv FU))
  | FTwice a b ->
    POp (k (fpv a)) (fun r1 -> POp (k (fpv b)) (fun r2 -> fret (FL [fseen r1; fseen r2])))
  | FAbort z -> fret z
  | FRetry ->
    POp (k (fpv (FS "go1"))) (fun r1 ->
      if fneeds_retry (fseen r1)
      then POp (k (fpv (FS "go2"))) (fun r2 -> fret (FL [FS "twice"; fseen r1; fseen r2]))
      else fret (FL [FS "once"; fseen r1]))
  | FBetween ->
    POp (k (fpv (FS "b1"))) (fun r1 ->
      POp (PPerform "T" "mark" [fpv (FS "mid")]) (fun m ->
        POp (k (fpv (FS "b2"))) (fun r2 -> fret (FL [fseen r1; fseen m; fseen r2]))))
  // The `POp` is the point: `fun r -> wrap r` becomes a `PBindF` on the stack
  // BELOW this clause's own prompt, so it is pending work that a resumption has
  // to come back through. `FEcho` has none, which is why it cannot be used to
  // check requirement 6.
  | FWrap -> POp (k (fpv (FS "outer-ans"))) (fun r -> fret (FL [FS "wrap"; fseen r]))

let fclause (c: fcl) : found_clause fcl = { body = c; kind = KFull }

(** The fixtures' lookup. It answers only for effects the table it is asked about
    declares in `binds` -- which is what makes "the plan does not handle this
    operation" a fact about a PROMPT here and not only about an effect label. *)
let flook : plookup_t fcl = fun tbl eff _ ->
  if eff `mem` tbl.binds
  then
    (match eff with
      | "Two" -> Some (fclause (FTwice (FS "a") (FS "b")))
      | "Abort" -> Some (fclause (FAbort (FS "aborted")))
      | "Retry" -> Some (fclause FRetry)
      | "Betw" -> Some (fclause FBetween)
      | "Echo" -> Some (fclause FEcho)
      | "T" -> Some (fclause FEcho)
      | "Out" -> Some (fclause FWrap)
      | _ -> None)
  else None

(** A REAL table, built through `Hoop.Runtime.Handlers.mk_handlers` with the real
    classifier, so that the classification fixture below is a statement about the
    shipped table and not about a stand-in. It is empty, which is the cheapest
    table that is genuinely borrowable. *)
let fhs : handlers fcl = mk_handlers #fcl (fun _ -> KFast) []

(** The table every prompt inside a plan carries: the real one, declaring the
    effects the fixtures' scopes perform -- and NOT `"Out"`. *)
let ftbl : ptable fcl = { hs = fhs; binds = ["Two"; "Abort"; "Retry"; "Betw"; "Echo"; "T"] }

(** The table an AMBIENT prompt carries: `"Out"` and nothing else, so an
    operation of that effect performed inside a scope is refused by every plan
    prompt and by the owner, and is taken here. *)
let ftbl_out : ptable fcl = { hs = fhs; binds = ["Out"] }

let fown_ret : option (pval fv -> pcomp fv fcl) =
  Some (fun x -> fret (FL [FS "own"; fseen x]))
let fowner : powner fv fcl = POwner ftbl fown_ret PFamily
let fowner_plain : powner fv fcl = POwner ftbl None PFamily
let fsite (x: pval fv) : pcomp fv fcl = fret (FL [FS "site1"; fseen x])
let fsite2 (x: pval fv) : pcomp fv fcl = fret (FL [FS "site2"; fseen x])
let fk (x: pval fv) : pcomp fv fcl = fret (FL [FS "k"; fseen x])

(* The plan shapes. `plan_LB` is the one that matters most: its recorded bind
   frame sits BETWEEN the layer and the owner, which is the interleaving that
   makes the two projections differ and that no post-hoc re-insertion could
   reconstruct. *)
let plan_L : plan fv fcl = Plan [PIReenter ftbl None] fowner
let plan_L0 : plan fv fcl = Plan [PIReenter ftbl None] fowner_plain
let plan_LB : plan fv fcl = Plan [PIReenter ftbl None; PIBind fsite2] fowner
let plan_T : plan fv fcl = Plan [PITransparent ftbl] fowner_plain
let plan_M : plan fv fcl =
  Plan [PIBind fsite; PICell "c" (fpv (FI 7)); PIReenter ftbl None; PIBind fsite2;
        PITransparent ftbl]
       fowner

let frun (fuel: nat) (c: pcomp fv fcl) : pconf fv fcl = psteps flook fapply fuel (pload c)

(** The ANSWER of a run, as the fixtures state it: an `fv`, with a handle
    rendered by `fseen`. A run that ends anywhere but `PDone` has no answer. *)
let fresult (cf: pconf fv fcl) : option fv =
  match cf.st with | PDone x -> Some (fseen x) | _ -> None

(** **The trace of a whole run**, which is the observable requirements 1 to 4 are
    stated in. It is the driver's second result and comes from nowhere else. *)
let ftrace (fuel: nat) (c: pcomp fv fcl) : list string = snd (prun flook fapply fuel (pload c))

(** **The store a run ends with**, which is how the store-integrity and
    persistence fixtures look at allocation. Nothing in the machine reads this;
    it is the fixtures' window onto what `palloc` did. *)
let fstore_size (fuel: nat) (c: pcomp fv fcl) : nat = length (frun fuel c).store
let fnext (fuel: nat) (c: pcomp fv fcl) : nat = (frun fuel c).next

(**
 * **`cx <- runScope body; use cx`**, which is the surface program every fixture
 * below is a rendering of.
 *
 * It is an ordinary `pbind` over the production node -- NOT a combinator with
 * privileges. That is condition 1 in the form the fixtures use it: the handle
 * arrives in a `PBindF` like any other value, so `use` receives a `pval fv` it
 * may keep, ignore, pass twice, or pass alongside another one. B1.6 had no such
 * helper and could not have: production carried its continuation, so the shape
 * was `enter_ctx_C pl body (consume_here ...)` and there was no variable to
 * bind.
 *)
let fscope (pl: plan fv fcl) (body: pcomp fv fcl) (use: pval fv -> pcomp fv fcl)
  : pcomp fv fcl
  = pbind (enter_ctx_C pl body) use

(* ---- 1 / 8. The protected prefix runs once, and the context is multi-shot
   FROM THE SAVED POINT.

   THIS FIXTURE IS DEMOTED IN B1.6, AND THE DEMOTION IS THE POINT. B1.5 could not
   state exact-once as an OBSERVATION -- the machine was pure, so a residual
   consumed twice and a suspension re-run twice returned the same value, and
   `pobs_eq` sees only values. It therefore stated the claim about WORK, with
   `pcost`, and recorded honestly that a transition count is not a semantic
   acceptance criterion: counts move when bookkeeping frames are added, and "did
   less work" is not "ran once".

   The semantic statement is now `fixture_11_prefix_event_once` against
   `fixture_12_suspension_emits_twice`, on traces. What survives here is a
   PERFORMANCE / STRUCTURE REGRESSION TEST THAT PREFIX WORK IS SHARED: `body1 n`
   is a prefix of `n` trivial binds in front of the operation the layer handles,
   and lengthening the prefix by four units costs the residual route one copy and
   the suspension route exactly two. The slope is the claim; the intercepts are
   not, and are not equal. Reporting the intercept as if it were the result would
   be rounding the answer in the wrong direction. ---- *)

let rec pchain (n: nat) (c: pcomp fv fcl) : Tot (pcomp fv fcl) (decreases n)
  = if n = 0 then c else POp (fret FU) (fun _ -> pchain (n - 1) c)

let body1 (n: nat) : pcomp fv fcl =
  pchain n (POp (PPerform "Two" "flip" []) (fun x -> fret (FL [FS "leaf"; fseen x])))

(* The residual route, and in B1.7 it is one program in which THE SAME HANDLE IS
   NAMED TWICE. B1.6 could only consume "the context in scope" twice and had to
   argue that both consumptions found the same token; here `cx` is a variable
   bound once by an ordinary `pbind` and used by both operations, so that they
   consume one context is a fact about the SYNTAX. This is `runScope` followed by
   `bindScope cx` and `resumeScope cx`. *)
let prog1new (n: nat) : pcomp fv fcl =
  pbind (enter_ctx_C plan_L (body1 n))
        (fun cx -> POp (extend_at_C plan_L cx (PVar #fv #fcl))
                       (fun _ -> resume_at_C plan_L cx fk))

(* The withdrawn route: the same two consumptions of the same unrun computation,
   which is what B1's `PCtx` made them. *)
let prog1old (n: nat) : pcomp fv fcl =
  POp (susp_extend plan_L (body1 n) (PVar #fv #fcl))
      (fun _ -> susp_resume plan_L (body1 n) fk)

(* Production is inside the program now, so its cost is counted with it and there
   is no second run to add on. *)
let cost_new (n: nat) : option nat = pcost flook fapply 4000 (pload (prog1new n))
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
  = assert_norm (cost_new 1 == Some 48);
    assert_norm (cost_new 5 == Some 56);
    assert_norm (cost_old 1 == Some 41);
    assert_norm (cost_old 5 == Some 57)

(* **How a fixture observes the SHAPE of a token without leaving the object
   language.** There is no `cx` to write `PCtxRequests? cx` about: the token
   exists only while the machine is running and cannot be named by a program. It
   is observed by BEHAVIOUR instead, and the probe is enough to separate the two
   shapes -- a `PCtxDone` absorbs the consumer's function and a `PCtxRequests`
   applies it at every leaf, so `"applied"` appears in the answer exactly when
   the token was a request. *)
let fprobe (_: pval fv) : pcomp fv fcl = fret (FS "applied")

(* ---- 2. `firstOfTwo`: a clause that resumes twice produces two requests, in
   order. The first request is what production yielded on; the second happens
   because the layer resumed its own captured continuation, which carries the
   boundary frame with it. The consumer's `fk` runs at each, and the layer
   assembles them in the order they arrived. ---- *)

let body2 : pcomp fv fcl =
  POp (PPerform "Two" "flip" []) (fun x -> fret (FL [FS "leaf"; fseen x]))

let prog2 : pcomp fv fcl = fscope plan_L body2 (fun cx -> resume_at_C plan_L cx fk)
let prog2_probe : pcomp fv fcl = fscope plan_L body2 (fun cx -> extend_at_C plan_L cx fprobe)

let fixture_2_two_requests () : Lemma
  (ensures fresult (frun 400 prog2_probe)
             == Some (FL [FS "own"; FL [FS "applied"; FS "applied"]])
        /\ fresult (frun 400 prog2)
           == Some (FL [FS "own";
                        FL [FL [FS "k"; FL [FS "leaf"; FS "a"]];
                            FL [FS "k"; FL [FS "leaf"; FS "b"]]]]))
  = assert_norm (fresult (frun 400 prog2_probe)
                 == Some (FL [FS "own"; FL [FS "applied"; FS "applied"]]));
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
let prog3a : pcomp fv fcl =
  fscope plan_L body3 (fun cx -> resume_at_C plan_L cx (fun _ -> fret (FS "retry")))
let prog3b : pcomp fv fcl =
  fscope plan_L body3 (fun cx -> resume_at_C plan_L cx (fun _ -> fret (FS "stop")))

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

let body4 : pcomp fv fcl =
  POp (PPerform "Betw" "go" []) (fun x -> fret (FL [FS "leaf"; fseen x]))
let prog4 : pcomp fv fcl = fscope plan_L0 body4 (fun cx -> resume_at_C plan_L0 cx fk)

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
   drains through the owner and then through the SCOPE FLOOR, which is the rule
   that makes the token `PCtxDone`; consuming it returns that answer and applies
   nothing. The probe run is what says "applies nothing": `"applied"` does not
   occur in it. This is the case B1's note said would otherwise have needed a "no
   values to return" branch, and there is none. ---- *)

let body5 : pcomp fv fcl =
  POp (PPerform "Abort" "x" []) (fun x -> fret (FL [FS "leaf"; fseen x]))
let prog5 : pcomp fv fcl = fscope plan_L body5 (fun cx -> resume_at_C plan_L cx fk)
let prog5_probe : pcomp fv fcl = fscope plan_L body5 (fun cx -> extend_at_C plan_L cx fprobe)

let fixture_5_never_resumes () : Lemma
  (ensures fresult (frun 400 prog5_probe) == Some (FL [FS "own"; FS "aborted"])
        /\ fresult (frun 400 prog5) == Some (FL [FS "own"; FS "aborted"]))
  = assert_norm (fresult (frun 400 prog5_probe) == Some (FL [FS "own"; FS "aborted"]));
    assert_norm (fresult (frun 400 prog5) == Some (FL [FS "own"; FS "aborted"]))

(* ---- 5b. THE SAME CLAUSE, at a plan whose recorded bind frame lies between the
   layer and the owner -- and the fixture that shows the two consuming operations
   are still two.

   Production drains as before, but now it meets a `PSiteF` on the way out and
   YIELDS there, because whether a perform-site bind fires is not production's
   question. ONE residual is then consumed both ways, in one program and from one
   token: `resume_C` fires the site frame and `extend_C` does not, so the answers
   differ. Under any representation that had committed to a projection at
   production time, one of these two would have been unavailable.

   This is the fixture that breaks if `resume_at_C` and `extend_at_C` are
   collapsed into one definition, which is why it is kept in exactly this shape:
   one production, both consumers, and an explicit statement that the answers are
   not equal. ---- *)

let prog5b : pcomp fv fcl =
  fscope plan_LB body5 (fun cx ->
    POp (resume_at_C plan_LB cx fk) (fun a ->
      POp (extend_at_C plan_LB cx fk) (fun b -> fret (FL [fseen a; fseen b]))))

let fixture_5b_never_resumes_with_bind () : Lemma
  (ensures fresult (frun 400 prog5b)
           == Some (FL [FL [FS "own"; FL [FS "site2"; FS "aborted"]];
                        FL [FS "own"; FS "aborted"]])
        /\ FL [FS "own"; FL [FS "site2"; FS "aborted"]] =!= FL [FS "own"; FS "aborted"])
  = assert_norm (fresult (frun 400 prog5b)
                 == Some (FL [FL [FS "own"; FL [FS "site2"; FS "aborted"]];
                              FL [FS "own"; FS "aborted"]]))

(* ---- 6. A transparent plan agrees with the borrow.

   Two checks, and neither is the quantified statement -- that is
   `law_transparent_agrees`, and it is B3's.

   The first is structural: the frames a transparent item contributes are
   `PPromptF tbl None PMono`, which is frame for frame what
   `Hoop.Runtime.Semantics.borrow` produces for a borrowable prompt, and the same
   in all three projections -- a transparent layer has no bind frame to defer, so
   the three agree. The equality across the two ASTs cannot be written here
   (`borrow` is over `comp_tree`, this is over `pcomp`) and is B3's to state.

   The second is observational at an instance: `enter_C` on a concrete program
   and the residual-driven extension of the same program converge to the same
   value.

   The classification is checked on a REAL table rather than on a hand-built
   `PITransparent`: `fhs` goes through `mk_handlers` with the real classifier,
   and `classify_prompt PMono ftbl None` really is `ContextTransparent` -- the
   `binds` field is not consulted, because the classification reads `hs`. ---- *)

let body6 : pcomp fv fcl =
  POp (PPerform "Echo" "e" [fpv (FS "v")]) (fun x -> fret (FL [FS "leaf"; fseen x]))
let prog6_enter : pcomp fv fcl = enter_C plan_T body6
let prog6_residual : pcomp fv fcl =
  fscope plan_T body6 (fun cx -> extend_at_C plan_T cx (PVar #fv #fcl))

let fixture_6_transparent_classification () : Lemma
  (ensures classify_prompt #fv #fcl PMono ftbl None == ContextTransparent)
  = assert (Nil? (blocking_effects ftbl.hs))

let fixture_6_transparent () : Lemma
  (ensures plan_enter_frames plan_T
             == [PPromptF ftbl None PMono; PPromptF ftbl None PFamily]
        /\ plan_resume_frames plan_T == plan_enter_frames plan_T
        /\ plan_protocol_frames plan_T == plan_enter_frames plan_T
        /\ fresult (frun 400 prog6_enter) == fresult (frun 400 prog6_residual))
  = assert_norm (plan_enter_frames plan_T
                 == [PPromptF ftbl None PMono; PPromptF ftbl None PFamily]);
    assert_norm (plan_resume_frames plan_T
                 == [PPromptF ftbl None PMono; PPromptF ftbl None PFamily]);
    assert_norm (plan_protocol_frames plan_T
                 == [PPromptF ftbl None PMono; PPromptF ftbl None PFamily]);
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
   no site frames at all, and the layer and owner untouched. Both consumptions
   are of ONE token, in one program. ---- *)

let body7 : pcomp fv fcl =
  POp (PReadP "c") (fun cv ->
    POp (PPerform "Two" "flip" []) (fun x -> fret (FL [fseen cv; fseen x])))
let prog7 : pcomp fv fcl =
  fscope plan_M body7 (fun cx ->
    POp (resume_at_C plan_M cx fk) (fun a ->
      POp (extend_at_C plan_M cx fk) (fun b -> fret (FL [fseen a; fseen b]))))

let fixture_7_mixed_order_frames () : Lemma
  (ensures plan_enter_frames plan_M
             == [PParamF "c" (fpv (FI 7));
                 PPromptF ftbl None PFamily;
                 PPromptF ftbl None PMono;
                 PPromptF ftbl fown_ret PFamily]
        /\ plan_resume_frames plan_M
             == [PBindF fsite;
                 PParamF "c" (fpv (FI 7));
                 PPromptF ftbl None PFamily;
                 PBindF fsite2;
                 PPromptF ftbl None PMono;
                 PPromptF ftbl fown_ret PFamily]
        /\ plan_protocol_frames plan_M
             == [PSiteF fsite;
                 PParamF "c" (fpv (FI 7));
                 PPromptF ftbl None PFamily;
                 PSiteF fsite2;
                 PPromptF ftbl None PMono;
                 PPromptF ftbl fown_ret PFamily])
  = assert_norm (plan_enter_frames plan_M
                 == [PParamF "c" (fpv (FI 7));
                     PPromptF ftbl None PFamily;
                     PPromptF ftbl None PMono;
                     PPromptF ftbl fown_ret PFamily]);
    assert_norm (plan_resume_frames plan_M
                 == [PBindF fsite;
                     PParamF "c" (fpv (FI 7));
                     PPromptF ftbl None PFamily;
                     PBindF fsite2;
                     PPromptF ftbl None PMono;
                     PPromptF ftbl fown_ret PFamily]);
    assert_norm (plan_protocol_frames plan_M
                 == [PSiteF fsite;
                     PParamF "c" (fpv (FI 7));
                     PPromptF ftbl None PFamily;
                     PSiteF fsite2;
                     PPromptF ftbl None PMono;
                     PPromptF ftbl fown_ret PFamily])

let fixture_7_mixed_order () : Lemma
  (ensures fresult (frun 800 prog7)
           == Some (FL [FL [FS "own";
                            FL [FS "site2";
                                FL [FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "a"]]];
                                    FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "b"]]]]]];
                        FL [FS "own";
                            FL [FL [FS "k"; FL [FI 7; FS "a"]];
                                FL [FS "k"; FL [FI 7; FS "b"]]]]]))
  = assert_norm (fresult (frun 800 prog7)
                 == Some (FL [FL [FS "own";
                                  FL [FS "site2";
                                      FL [FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "a"]]];
                                          FL [FS "site1"; FL [FS "k"; FL [FI 7; FS "b"]]]]]];
                              FL [FS "own";
                                  FL [FL [FS "k"; FL [FI 7; FS "a"]];
                                      FL [FS "k"; FL [FI 7; FS "b"]]]]]))

(* ---- 8. A context resumed more than once is multi-shot FROM THE SAVED POINT.

   One `enter_ctx_C`, one token, driven twice -- once as an extension and once as a
   resumption -- and the answers paired. Both consumptions see the layer's two
   branches; the resumption additionally fires the recorded bind frame and the
   extension does not. That the prefix was run once is
   `fixture_11_prefix_event_once`. ---- *)

let body8 : pcomp fv fcl =
  POp (PPerform "Two" "flip" []) (fun x -> fret (FL [FS "leaf"; fseen x]))
let prog8 : pcomp fv fcl =
  fscope plan_LB body8 (fun cx ->
    POp (extend_at_C plan_LB cx fk) (fun a ->
      POp (resume_at_C plan_LB cx fk) (fun b -> fret (FL [fseen a; fseen b]))))

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

(* ---- 8b. `bindScope` IN ITS PUBLISHED SHAPE, and in B1.7 it is literally the
   surface program: `cy <- bindScope cx fext; resumeScope cy fk`. `extend_ctx_at_C`
   evaluates to a FRESH handle, so `cy` is an ordinary bound variable and `cx` is
   still in scope beside it, untouched.

   B1.6 needed a `kbody` field here, because the context an extension produced
   could only be installed on the stack for the rest of the clause to find. The
   field is gone and the program is a bind.

   Here the context is extended by `fun x -> FL ["ext"; x]` and then resumed; the
   extension composes onto the residual's `post` chain, so it runs at each leaf
   BEFORE the resumption's own function. Reading outwards: `ext` inside `k`. ---- *)

let fext (x: pval fv) : pcomp fv fcl = fret (FL [FS "ext"; fseen x])
let prog8b : pcomp fv fcl =
  fscope plan_L body8 (fun cx ->
    pbind (extend_ctx_at_C plan_L cx fext) (fun cy -> resume_at_C plan_L cy fk))

let fixture_8b_extend_then_resume () : Lemma
  (ensures fresult (frun 800 prog8b)
           == Some (FL [FS "own";
                        FL [FL [FS "k"; FL [FS "ext"; FL [FS "leaf"; FS "a"]]];
                            FL [FS "k"; FL [FS "ext"; FL [FS "leaf"; FS "b"]]]]]))
  = assert_norm (fresult (frun 800 prog8b)
                 == Some (FL [FS "own";
                              FL [FL [FS "k"; FL [FS "ext"; FL [FS "leaf"; FS "a"]]];
                                  FL [FS "k"; FL [FS "ext"; FL [FS "leaf"; FS "b"]]]]]))

(* ---- 9. No clause-inspecting mechanism, and no assumption about `apply`.

   Mostly a property of the design, so it is stated where it is respected rather
   than fabricated as a fixture:

     - `papply_t` and its note: a clause is opaque, and the machine's only
       interaction with one is to hand it a payload and a continuation.
     - `pstep`: no rule matches on a clause, and the protocol is built entirely
       from frames the machine pushed -- `PBoundaryF`, `PSiteF`, `PModeF`,
       `PScopeF` -- so a layer reaches the boundary only by resuming,
       through the ordinary `PSplice` rule, the continuation it was given.
     - `enter_ctx_C`'s rule: production PUSHES FRAMES UNDER the inner computation
       and never reads it.

   The fixtures above are the evidence that this is not vacuous: `FEcho`,
   `FTwice`, `FAbort`, `FRetry`, `FBetween` and `FWrap` resume once, twice,
   never, conditionally, and with work left over, and the protocol is the same
   protocol in every case, with no rule anywhere asking which of them it is
   looking at.

   The two parts that ARE runs are below. `PPaused` is the answer the value rules
   give when a boundary or site frame has neither a mode above it nor a floor
   below it -- a stack no transition builds -- and every fixture in this file
   reaches `PDone`, so none of them relies on it. And a consuming node with no
   context in scope is REPORTED, as an ordinary stuck action under a reserved
   label, rather than silently taken for something else. ---- *)

let fsettled (fuel: nat) (c: pcomp fv fcl) : bool = PDone? (frun fuel c).st

let fixture_9_paused_is_unreachable () : Lemma
  (ensures fsettled 4000 (prog1new 1) /\ fsettled 400 prog2 /\ fsettled 400 prog2_probe
        /\ fsettled 400 prog3a /\ fsettled 400 prog3b /\ fsettled 400 prog4
        /\ fsettled 400 prog5 /\ fsettled 400 prog5_probe /\ fsettled 400 prog5b
        /\ fsettled 400 prog6_residual
        /\ fsettled 800 prog7 /\ fsettled 800 prog8 /\ fsettled 800 prog8b)
  = assert_norm (fsettled 4000 (prog1new 1));
    assert_norm (fsettled 400 prog2);
    assert_norm (fsettled 400 prog2_probe);
    assert_norm (fsettled 400 prog3a);
    assert_norm (fsettled 400 prog3b);
    assert_norm (fsettled 400 prog4);
    assert_norm (fsettled 400 prog5);
    assert_norm (fsettled 400 prog5_probe);
    assert_norm (fsettled 400 prog5b);
    assert_norm (fsettled 400 prog6_residual);
    assert_norm (fsettled 800 prog7);
    assert_norm (fsettled 800 prog8);
    assert_norm (fsettled 800 prog8b)

(* In B1.6 this fixture ran a consumer on an empty stack, where there was no
   `PTokenF` to find. Under a handle there is no such thing as "no context in
   scope" -- a consumer always HAS a handle, because it takes one -- so the
   fixture becomes the sharper question condition 7 asks: what happens to a
   handle that names nothing. All three consumers, on a forged key, get stuck. *)
let fixture_9_consumer_without_token () : Lemma
  (ensures (frun 400 (resume_at_C plan_L (PCtxKey 0) fk)).st
             == PStuck pctx_eff pctx_missing_op
        /\ (frun 400 (extend_at_C plan_L (PCtxKey 0) fk)).st
             == PStuck pctx_eff pctx_missing_op
        /\ (frun 400 (extend_ctx_at_C plan_L (PCtxKey 0) fk)).st
             == PStuck pctx_eff pctx_missing_op)
  = assert_norm ((frun 400 (resume_at_C plan_L (PCtxKey 0) fk)).st
                 == PStuck pctx_eff pctx_missing_op);
    assert_norm ((frun 400 (extend_at_C plan_L (PCtxKey 0) fk)).st
                 == PStuck pctx_eff pctx_missing_op);
    assert_norm ((frun 400 (extend_ctx_at_C plan_L (PCtxKey 0) fk)).st
                 == PStuck pctx_eff pctx_missing_op)

(* ================================================================== *)
(*  B1.6's own requirements                                            *)
(* ================================================================== *)

(* ---- 10. An operation the plan does NOT handle, performed in the PREFIX, is
   handled by a prompt OUTSIDE the owner -- and that handler's pending binds and
   answer transformation are not lost. (Requirements 5 and 6, which are the
   substance of the gate.)

   The program is an ambient prompt whose table binds `"Out"` and nothing else,
   with a scope inside it whose plan prompts and owner bind everything EXCEPT
   `"Out"`. So when the prefix performs `Out.o`:

     - `pfind_prompt` is refused by the layer prompt and by the owner, walks past
       the SCOPE FLOOR, and finds the ambient prompt. The segment it captures
       contains the whole scope -- boundary, plan frames and floor.
     - the clause is `FWrap`, which resumes and then still has `fun r -> wrap r`
       to do. That pending frame is BELOW the ambient prompt, so it is not in the
       captured segment; resuming puts the scope back ON TOP of it.
     - the prefix then continues, performs `Echo.e` -- which the layer DOES
       handle -- reaches the boundary, and the token is produced. It is installed
       beneath the continuation on the stack below the floor, which by now is the
       ambient prompt followed by that pending frame.

   The answer is `wrap(outer-ret(own(k(outer-ans, v))))`. Read it outwards: the
   scope's own answer former ran (`own`), then the ambient prompt's answer
   transformation (`outer-ret`), then the ambient clause's pending bind (`wrap`)
   -- and `outer-ans`, the value the ambient handler resumed with, is inside,
   where the prefix received it. Nothing of the ambient handler was lost and
   nothing of the scope was.

   `fixture_10_detached_gets_stuck` is the control: B1.5's production, which is
   still writable as a meta-level call and is kept here for exactly this
   comparison, gets `PStuck "Out" "o"` on the same body. That is what the
   `settles` hypothesis was hiding. ---- *)

let fouter_ret : option (pval fv -> pcomp fv fcl) =
  Some (fun x -> fret (FL [FS "outer-ret"; fseen x]))

let body_out : pcomp fv fcl =
  POp (PPerform "Out" "o" [fpv (FS "q")]) (fun x ->
    POp (PPerform "Echo" "e" [fpv (FS "v")]) (fun y -> fret (FL [fseen x; fseen y])))

let prog_out : pcomp fv fcl =
  PHandle ftbl_out fouter_ret PMono
    (fscope plan_L body_out (fun cx -> resume_at_C plan_L cx fk))

(** B1.5's production, kept executable and named for what it was, exactly as
    `susp_extend` / `susp_resume` keep B1's. Nothing but the control fixture
    refers to it. *)
let detached_production (pl: plan fv fcl) (c: pcomp fv fcl) : pstate fv fcl
  = (psteps flook fapply 400
       { st = PStep c (PBoundaryF :: plan_protocol_frames pl); store = []; next = 0 }).st

let fixture_10_outer_handler () : Lemma
  (ensures fresult (frun 400 prog_out)
           == Some (FL [FS "wrap";
                        FL [FS "outer-ret";
                            FL [FS "own";
                                FL [FS "k"; FL [FS "outer-ans"; FS "v"]]]]]))
  = assert_norm (fresult (frun 400 prog_out)
                 == Some (FL [FS "wrap";
                              FL [FS "outer-ret";
                                  FL [FS "own";
                                      FL [FS "k"; FL [FS "outer-ans"; FS "v"]]]]]))

let fixture_10_detached_gets_stuck () : Lemma
  (ensures detached_production plan_L body_out == PStuck "Out" "o")
  = assert_norm (detached_production plan_L body_out == PStuck "Out" "o")

(* ---- 11. One observation event in the protected prefix, and the residual
   consumed twice yields it ONCE. (Requirements 1, 2 and 3.)

   `body_e` emits `"prefix"` and then performs an operation the layer handles
   tail-resumptively, so each consumption reaches the boundary exactly once and
   the trace is short enough to read whole.

   `prog_silent`'s consumers emit nothing, so the entire trace of a program that
   produces one token and drives it twice is `["prefix"]` -- which is requirement
   1 as a run: driving a residual re-emits nothing, because there is nothing in a
   residual to re-emit.

   `prog_traced`'s consumers emit `"c1"` and `"c2"`, and the trace is
   `["prefix"; "c1"; "c2"]`: the prefix event once, each consumer's own event
   once per consumption, in order. ---- *)

let body_e : pcomp fv fcl =
  PEmit "prefix"
    (POp (PPerform "Echo" "e" [fpv (FS "v")]) (fun x -> fret (FL [FS "leaf"; fseen x])))

let fc1 (x: pval fv) : pcomp fv fcl = PEmit "c1" (PVar x)
let fc2 (x: pval fv) : pcomp fv fcl = PEmit "c2" (PVar x)

let prog_silent : pcomp fv fcl =
  fscope plan_L body_e (fun cx ->
    POp (extend_at_C plan_L cx (PVar #fv #fcl)) (fun _ -> resume_at_C plan_L cx fk))

let prog_traced : pcomp fv fcl =
  fscope plan_L body_e (fun cx ->
    POp (extend_at_C plan_L cx fc1) (fun _ -> resume_at_C plan_L cx fc2))

let fixture_11_prefix_event_once () : Lemma
  (ensures ftrace 400 prog_silent == ["prefix"]
        /\ ftrace 400 prog_traced == ["prefix"; "c1"; "c2"])
  = assert_norm (ftrace 400 prog_silent == ["prefix"]);
    assert_norm (ftrace 400 prog_traced == ["prefix"; "c1"; "c2"])

(* ---- 12. THE CONTROL. The withdrawn suspension, on the same body and with the
   same two consumers, emits the prefix event TWICE. (Requirement 4.)

   Without this the instrument would not be known to be measuring anything: a
   trace that shows one event once is only evidence if a representation that
   replays shows it twice. The two traces differ in exactly one element, and it
   is the prefix's. ---- *)

let prog_susp : pcomp fv fcl =
  POp (susp_extend plan_L body_e fc1) (fun _ -> susp_resume plan_L body_e fc2)

let fixture_12_suspension_emits_twice () : Lemma
  (ensures ftrace 400 prog_susp == ["prefix"; "c1"; "prefix"; "c2"]
        /\ ftrace 400 prog_traced =!= ftrace 400 prog_susp)
  = assert_norm (ftrace 400 prog_susp == ["prefix"; "c1"; "prefix"; "c2"]);
    assert_norm (ftrace 400 prog_traced == ["prefix"; "c1"; "c2"])

(* ---- 13. The same, with a layer that resumes TWICE: the check that requirement
   3 is not an artefact of a tail-resumptive layer.

   Each consumption now reaches the boundary twice, so the consumer's own event
   appears twice per consumption -- four in all -- while the prefix event still
   appears once, first, and never again. ---- *)

let body_e2 : pcomp fv fcl =
  PEmit "prefix"
    (POp (PPerform "Two" "flip" []) (fun x -> fret (FL [FS "leaf"; fseen x])))

let prog_traced2 : pcomp fv fcl =
  fscope plan_L body_e2 (fun cx ->
    POp (extend_at_C plan_L cx fc1) (fun _ -> resume_at_C plan_L cx fc2))

let fixture_13_multi_shot_trace () : Lemma
  (ensures ftrace 800 prog_traced2 == ["prefix"; "c1"; "c1"; "c2"; "c2"])
  = assert_norm (ftrace 800 prog_traced2 == ["prefix"; "c1"; "c1"; "c2"; "c2"])

(* ---- 14. A SCOPE OPENED INSIDE A CONSUMPTION, which is the program the scope
   floor has to keep apart from its enclosing protocol.

   B1.5 could not build this configuration. Production ran on an empty stack, so
   during a production there was provably no mode marker anywhere beneath, and
   `pfind_mode`'s unlabelled nearest-enclosing search could only ever find the
   marker of the residual actually being driven. Under B1.6 production runs on
   the LIVE stack, so a scope entered from inside a consumer's own function has
   that consumer's marker somewhere below it -- and an unguarded search would
   answer the INNER boundary with the OUTER consumer's responder, which is a
   genuine confusion of `MResume` with `MExtend`.

   The `PScopeF` arm of `pfind_mode` is what stops it, and this fixture is what
   fires that arm: deleting it changes the answer. Read the result outwards --
   `ik(inner(leaf v))` is the inner scope's own protocol completing, and `own`
   the outer owner's answer former applied once, afterwards. ---- *)

let finner (x: pval fv) : pcomp fv fcl =
  fscope plan_L0
    (POp (PPerform "Echo" "e" [x]) (fun y -> fret (FL [FS "inner"; fseen y])))
    (fun ci -> resume_at_C plan_L0 ci (fun z -> fret (FL [FS "ik"; fseen z])))

let prog_nested : pcomp fv fcl =
  fscope plan_L body6 (fun cx -> resume_at_C plan_L cx finner)

let fixture_14_nested_scope () : Lemma
  (ensures fresult (frun 800 prog_nested)
           == Some (FL [FS "own"; FL [FS "ik"; FL [FS "inner"; FL [FS "leaf"; FS "v"]]]]))
  = assert_norm (fresult (frun 800 prog_nested)
                 == Some (FL [FS "own"; FL [FS "ik"; FL [FS "inner"; FL [FS "leaf"; FS "v"]]]]))

(* ---- 15. TWO SCOPE FLOORS ALIVE AT ONCE: a scope nested inside another
   scope's PROTECTED PREFIX.

   Fixture 14 has two protocols but never two floors -- by the time the inner
   scope is entered the outer handle has been produced, so the outer floor has
   already been consumed by `pcut_scope`. Here the outer scope's own body IS a
   scope, so
   when the inner boundary is reached the stack carries `PScopeF` twice, and
   `pcut_scope` has to take the NEARER one. Taking the farther one would hand the
   inner scope's residual to the outer scope's continuation and cut away the
   outer plan with it.

   This is also the configuration B2a's well-bracketing obligation is about, in
   the smallest program that has it. ---- *)

let fmid : pcomp fv fcl =
  fscope plan_L0 body6
    (fun cm -> resume_at_C plan_L0 cm (fun z -> fret (FL [FS "m"; fseen z])))

let prog_two_floors : pcomp fv fcl =
  fscope plan_L fmid (fun cx -> resume_at_C plan_L cx fk)

let fixture_15_two_floors () : Lemma
  (ensures fresult (frun 800 prog_two_floors)
           == Some (FL [FS "own"; FL [FS "k"; FL [FS "m"; FL [FS "leaf"; FS "v"]]]]))
  = assert_norm (fresult (frun 800 prog_two_floors)
                 == Some (FL [FS "own"; FL [FS "k"; FL [FS "m"; FL [FS "leaf"; FS "v"]]]]))

(* ------------------------------------------------------------------ *)
(*  B1.7 -- THE EIGHT CONDITIONS OF THE FIRST-CLASS HANDLE             *)
(*                                                                     *)
(*  Fixtures 1 to 15 above are B1.6's and they are unchanged in intent: *)
(*  they still run, which is condition 5. What follows is what B1.6     *)
(*  could not write down at all, because under a dynamically scoped     *)
(*  token there was no way for a program to NAME a context.             *)
(*                                                                     *)
(*  EVERY FIXTURE BELOW GOES THROUGH THE NAMED OPERATIONS --            *)
(*  `enter_ctx_C`, `extend_at_C`, `extend_ctx_at_C`, `resume_at_C` --   *)
(*  and never through a raw constructor. B1.6 recorded that a first     *)
(*  firing round found constructor-level fixtures accepting a collapse  *)
(*  that the named operations reject; that finding is respected here.   *)
(* ------------------------------------------------------------------ *)

(* ---- 16. CONDITION 1: production returns an opaque handle as an
   object-language value, ONCE.

   The program is `cx <- runScope body2; pure cx` -- the scope's handle is the
   whole answer of the program. B1.6 could not run this: its production carried
   the continuation, so there was no value to return, and the note recorded
   exactly this as the price ("a context cannot be stored, returned as a scope's
   own result, or put in a list"). What is checked here is the middle one:
   returned as a scope's own result. Whether a live handle can be put in a
   CONTAINER is a separate question the shallow value model cannot pose -- see
   `fixture_17`.

   Three things are checked. The answer IS the handle, and `fseen` reports which
   one. The store holds exactly ONE entry, so the scope was reified once even
   though its layer resumes twice -- production stops at the first boundary and
   the rest of the layer's work is inside the residual. And `next` is 1, so
   exactly one allocation happened in the whole run. ---- *)

let prog16 : pcomp fv fcl = fscope plan_L body2 (fun cx -> PVar cx)

let fixture_16_handle_is_a_value () : Lemma
  (ensures fresult (frun 400 prog16) == Some (FL [FS "ctx"; FI 0])
        /\ fstore_size 400 prog16 == 1
        /\ fnext 400 prog16 == 1)
  = assert_norm (fresult (frun 400 prog16) == Some (FL [FS "ctx"; FI 0]));
    assert_norm (fstore_size 400 prog16 == 1);
    assert_norm (fnext 400 prog16 == 1)

(* ---- 17. CONDITION 2: two contexts alive at the same time.

   Two scopes are produced one after the other, the first handle is still bound
   when the second is produced, and both are named in the answer. The two
   handles are DIFFERENT, and that is checked rather than assumed: they are
   `ctx 0` and `ctx 1`, and the store holds both. Under an implementation that
   overwrote a single cell they would be equal and the store would hold one.

   **What this does NOT check, stated so the fixture is not read for more than
   it says.** The answer is a list of `fseen cx` and `fseen cy` -- each handle
   RENDERED to an ordinary value -- not of the handles themselves. So this is
   "two contexts alive at once, separately nameable", and not "a live handle can
   be put in a container and taken out again". The obstruction is the model, not
   the design: the shallow `pval = PV v | PCtxKey nat` has no way to say what it
   means to combine two things that might be handles, so `fseen` is the only way
   to write the comparison down at all. Container storage of live handles needs
   a different value model, and is untested here. ---- *)

let body_a : pcomp fv fcl =
  POp (PPerform "Echo" "e" [fpv (FS "A")]) (fun x -> fret (FL [FS "leaf"; fseen x]))
let body_b : pcomp fv fcl =
  POp (PPerform "Echo" "e" [fpv (FS "B")]) (fun x -> fret (FL [FS "leaf"; fseen x]))

let prog17 : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    fscope plan_L0 body_b (fun cy ->
      fret (FL [fseen cx; fseen cy])))

let fixture_17_two_contexts_alive () : Lemma
  (ensures fresult (frun 800 prog17)
             == Some (FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]])
        /\ fstore_size 800 prog17 == 2
        /\ FL [FS "ctx"; FI 0] =!= FL [FS "ctx"; FI 1])
  = assert_norm (fresult (frun 800 prog17)
                 == Some (FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]]));
    assert_norm (fstore_size 800 prog17 == 2)

(* ---- 18. CONDITIONS 3 AND 4: THE OUTER CONTEXT IS SELECTED WHILE THE INNER
   ONE IS LIVE, AND WHAT IS CONSUMED IS DECIDED BY THE HANDLE PASSED.

   **This is the fixture the gate exists for.** The two programs are identical
   except for ONE VARIABLE -- `cx` against `cy` -- at the same point in the same
   stack, with both contexts live. If resolution were by nearness the two would
   have to agree, because the stack they are read from is the same stack; they
   disagree, and the disagreement is exactly the two scopes' own bodies.

   `prog18_outer` selects the context produced FIRST and gets `A`.
   `prog18_inner` selects the context produced SECOND and gets `B`.

   The published surface's

       r1 <- t.runScope p
       r2 <- t.runScope q
       t.bindScope cx1 g

   is this program. B1.6 ran it with `cx2`, silently. The third conjunct is the
   statement that it no longer does, and it is an inequality rather than two
   equalities so that a collapse of the two answers cannot pass by making both
   sides wrong in the same way. ---- *)

let prog18_outer : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    fscope plan_L0 body_b (fun cy ->
      resume_at_C plan_L0 cx fk))

let prog18_inner : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    fscope plan_L0 body_b (fun cy ->
      resume_at_C plan_L0 cy fk))

let fixture_18_handle_not_nearness () : Lemma
  (ensures fresult (frun 800 prog18_outer)
             == Some (FL [FS "k"; FL [FS "leaf"; FS "A"]])
        /\ fresult (frun 800 prog18_inner)
             == Some (FL [FS "k"; FL [FS "leaf"; FS "B"]])
        /\ fresult (frun 800 prog18_outer) =!= fresult (frun 800 prog18_inner))
  = assert_norm (fresult (frun 800 prog18_outer)
                 == Some (FL [FS "k"; FL [FS "leaf"; FS "A"]]));
    assert_norm (fresult (frun 800 prog18_inner)
                 == Some (FL [FS "k"; FL [FS "leaf"; FS "B"]]))

(* ---- 19. CONDITION 7: STORE INTEGRITY. A forged handle FAILS, and it fails
   EVEN WHERE A REAL CONTEXT IS AVAILABLE TO FALL BACK ON.

   `fixture_9_consumer_without_token` already checks a forged handle on an empty
   store. That is the easy half: with nothing to resolve to, any implementation
   fails. The hard half is here, and it is the one the gate names -- "a missing
   or forged handle must NOT fall back to the nearest context".

   `prog19_forged` produces a real context, binds it to `cx`, and then consumes
   `PCtxKey 7`, which the machine never allocated. A live, resolvable, perfectly
   good context is sitting in the store one entry away. The machine gets stuck.

   `prog19_notahandle` is the other forgery: an ORDINARY VALUE where a handle was
   wanted. The surface's types make it unreachable, but the machine still has to
   answer, and the answer is a refusal rather than a coercion.

   `prog19_good` is the control -- the same program with the real handle -- so
   that "it got stuck" is known to be about the forgery and not about the shape
   of the program. ---- *)

let prog19_good : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx -> resume_at_C plan_L0 cx fk)

let prog19_forged : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx -> resume_at_C plan_L0 (PCtxKey 7) fk)

let prog19_notahandle : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx -> resume_at_C plan_L0 (fpv (FS "not-a-handle")) fk)

let fixture_19_forged_handle_fails () : Lemma
  (ensures fresult (frun 800 prog19_good)
             == Some (FL [FS "k"; FL [FS "leaf"; FS "A"]])
        /\ (frun 800 prog19_forged).st == PStuck pctx_eff pctx_missing_op
        /\ (frun 800 prog19_notahandle).st == PStuck pctx_eff pctx_missing_op
        /\ fstore_size 800 prog19_forged == 1)
  = assert_norm (fresult (frun 800 prog19_good)
                 == Some (FL [FS "k"; FL [FS "leaf"; FS "A"]]));
    assert_norm ((frun 800 prog19_forged).st == PStuck pctx_eff pctx_missing_op);
    assert_norm ((frun 800 prog19_notahandle).st == PStuck pctx_eff pctx_missing_op);
    assert_norm (fstore_size 800 prog19_forged == 1)

(* ---- 20. CONDITION 8: PERSISTENCE AND ALIASING. Extending a context produces a
   FRESH handle without modifying the original, and two extensions of the same
   handle stay independent.

   This is the design note's program, transcribed:

       cy1 <- bindScope cx g
       cy2 <- bindScope cx h

   `cx`, `cy1` and `cy2` must be three INDEPENDENT contexts, because the
   published API admits multi-shot use of the same `ctx x`. All three are
   consumed in one program and the three answers are reported together:
   `cy1` carries `g`, `cy2` carries `h`, and **`cx` carries neither** -- which is
   the conjunct that fails for any implementation that extends in place.

   An implementation that overwrote `cx`'s store entry would give `cx` the answer
   of whichever extension ran last, and one that shared a single cell between the
   two extensions would give `cy1` and `cy2` the same answer. Both are refused
   here by a value.

   `prog20_rev` consumes the same three in a DIFFERENT ORDER and assembles the
   answers back into the same positions. The two programs agree, which is
   "may be consumed in either order" as an equation rather than as a claim. It
   also rules out a store that a consumption CONSUMES: if driving `cy1` removed
   or altered anything, the later drives would differ between the two orders. ---- *)

let fg (x: pval fv) : pcomp fv fcl = fret (FL [FS "g"; fseen x])
let fh (x: pval fv) : pcomp fv fcl = fret (FL [FS "h"; fseen x])

let prog20 : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    pbind (extend_ctx_at_C plan_L0 cx fg) (fun cy1 ->
      pbind (extend_ctx_at_C plan_L0 cx fh) (fun cy2 ->
        POp (resume_at_C plan_L0 cy1 fk) (fun a ->
          POp (resume_at_C plan_L0 cy2 fk) (fun b ->
            POp (resume_at_C plan_L0 cx fk) (fun c ->
              fret (FL [fseen a; fseen b; fseen c])))))))

let prog20_rev : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    pbind (extend_ctx_at_C plan_L0 cx fg) (fun cy1 ->
      pbind (extend_ctx_at_C plan_L0 cx fh) (fun cy2 ->
        POp (resume_at_C plan_L0 cy2 fk) (fun b ->
          POp (resume_at_C plan_L0 cy1 fk) (fun a ->
            POp (resume_at_C plan_L0 cx fk) (fun c ->
              fret (FL [fseen a; fseen b; fseen c])))))))

(* The three handles are distinct, and the store holds all three: one production
   and two extensions, nothing overwritten. *)
let prog20_handles : pcomp fv fcl =
  fscope plan_L0 body_a (fun cx ->
    pbind (extend_ctx_at_C plan_L0 cx fg) (fun cy1 ->
      pbind (extend_ctx_at_C plan_L0 cx fh) (fun cy2 ->
        fret (FL [fseen cx; fseen cy1; fseen cy2]))))

let fixture_20_persistence_and_aliasing () : Lemma
  (ensures fresult (frun 800 prog20)
             == Some (FL [FL [FS "k"; FL [FS "g"; FL [FS "leaf"; FS "A"]]];
                          FL [FS "k"; FL [FS "h"; FL [FS "leaf"; FS "A"]]];
                          FL [FS "k"; FL [FS "leaf"; FS "A"]]])
        /\ fresult (frun 800 prog20_rev) == fresult (frun 800 prog20)
        /\ fresult (frun 800 prog20_handles)
             == Some (FL [FL [FS "ctx"; FI 0];
                          FL [FS "ctx"; FI 1];
                          FL [FS "ctx"; FI 2]])
        /\ fstore_size 800 prog20_handles == 3)
  = assert_norm (fresult (frun 800 prog20)
                 == Some (FL [FL [FS "k"; FL [FS "g"; FL [FS "leaf"; FS "A"]]];
                              FL [FS "k"; FL [FS "h"; FL [FS "leaf"; FS "A"]]];
                              FL [FS "k"; FL [FS "leaf"; FS "A"]]]));
    assert_norm (fresult (frun 800 prog20_rev)
                 == Some (FL [FL [FS "k"; FL [FS "g"; FL [FS "leaf"; FS "A"]]];
                              FL [FS "k"; FL [FS "h"; FL [FS "leaf"; FS "A"]]];
                              FL [FS "k"; FL [FS "leaf"; FS "A"]]]));
    assert_norm (fresult (frun 800 prog20_handles)
                 == Some (FL [FL [FS "ctx"; FI 0];
                              FL [FS "ctx"; FI 1];
                              FL [FS "ctx"; FI 2]]));
    assert_norm (fstore_size 800 prog20_handles == 3)

(* ---- 21. THE MULTI-SHOT ALLOCATION HAZARD, which no fixture above would
   catch.

   Every fixture so far allocates along one path. This one allocates along TWO,
   and they are two resumptions of ONE captured continuation.

   `FTwice` resumes its continuation twice. The continuation contains a `runScope`,
   so the scope is entered -- and a handle allocated -- once per resumption. If
   the allocation counter were carried anywhere the continuation captures, both
   resumptions would restore the same counter and allocate the SAME key, and the
   two branches would then disagree about what that key names while both being
   entitled to it.

   `next` lives in the `pconf` and a `pconf` is not a frame, so nothing about it
   is captured by `PSplice` and nothing is restored. The check is that the two
   branches got `ctx 0` and `ctx 1`, and that consuming each afterwards yields
   that branch's OWN body -- `a` for the first, `b` for the second. Both handles
   were allocated by the machine, so this is not the forged-handle case; it is
   the case where two legitimate handles must not be one. ---- *)

let body_ms (x: pval fv) : pcomp fv fcl =
  POp (PPerform "Echo" "e" [x]) (fun y -> fret (FL [FS "leaf"; fseen y]))

let prog21_handles : pcomp fv fcl =
  PHandle ftbl None PMono
    (POp (PPerform "Two" "flip" []) (fun x ->
       fscope plan_L0 (body_ms x) (fun cx -> PVar cx)))

(* The consumption sits BELOW the prompt, so it runs once after both branches
   rather than being captured into the continuation and re-run inside each. *)
let prog21_consume : pcomp fv fcl =
  pbind
    (PHandle ftbl None PMono
       (POp (PPerform "Two" "flip" []) (fun x ->
          fscope plan_L0 (body_ms x) (fun cx -> PVar cx))))
    (fun both ->
       POp (resume_at_C plan_L0 (PCtxKey 0) fk) (fun a ->
         POp (resume_at_C plan_L0 (PCtxKey 1) fk) (fun b ->
           fret (FL [fseen both; fseen a; fseen b]))))

let fixture_21_multi_shot_alloc () : Lemma
  (ensures fresult (frun 800 prog21_handles)
             == Some (FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]])
        /\ fstore_size 800 prog21_handles == 2
        /\ fresult (frun 800 prog21_consume)
             == Some (FL [FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]];
                          FL [FS "k"; FL [FS "leaf"; FS "a"]];
                          FL [FS "k"; FL [FS "leaf"; FS "b"]]]))
  = assert_norm (fresult (frun 800 prog21_handles)
                 == Some (FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]]));
    assert_norm (fstore_size 800 prog21_handles == 2);
    assert_norm (fresult (frun 800 prog21_consume)
                 == Some (FL [FL [FL [FS "ctx"; FI 0]; FL [FS "ctx"; FI 1]];
                              FL [FS "k"; FL [FS "leaf"; FS "a"]];
                              FL [FS "k"; FL [FS "leaf"; FS "b"]]]))

(* ------------------------------------------------------------------ *)
(*  B2a, strand 1 -- 22. THE SEPARATING CONFIGURATION IS REACHABLE     *)
(* ------------------------------------------------------------------ *)

(* ---- 22. A CLOSED PROGRAM WHOSE RUN REACHES A STATE WHERE THE NEAREST AND
   FARTHEST CUTS DIFFER IN THE WAY THAT MATTERS.

   The theorems above are what decide the proximity question and they need no
   fixture. This one answers the separate question the two earlier gates were
   really asking -- *can the machine get into a position where the choice is
   observable* -- and it answers it about a program rather than about a list of
   frames written by hand.

   **What was missing before, stated exactly.** Two floors are not enough.
   `fixture_15_two_floors` has two, and the two cuts agree there, because the
   inner scope's consumption completes before the outer boundary is reached: a
   value passing a `PModeF` POPS it, so by the time the outer boundary yields
   there is nothing between the floors but ordinary frames, and sweeping them
   into the residual really does merely defer. What is needed is a mode marker
   that is still LIVE between the two floors, and that requires a scope to be
   entered from inside a resumption -- not from inside a scope body. No fixture
   in this file did that.

   `prog_sep` does. Reading it outwards:

     - a first scope produces `cx0` and yields, so `cx0` is a residual;
     - a SECOND scope is entered, and its body is `resumeScope cx0 ...`, so the
       second scope's floor is beneath the marker that resumption installs;
     - the resumption's continuation enters a THIRD scope, whose floor is
       therefore ABOVE that marker.

   When the third scope's body reaches its boundary the stack is
   `... Floor_3 ... Mode_0 ... Floor_2 ...`, the yield guard holds, and the two
   cuts disagree: the nearest takes the frames above `Floor_3` and the farthest
   takes `Floor_3`, `Mode_0` and the second scope's boundary with them.

   **What is checked**: that the run reaches such a state, and that at that state
   the nearest cut satisfies BOTH conjuncts of `presid_wf` and the farthest cut
   satisfies NEITHER. That is `lemma_pyield_residual_wf`'s conclusion holding and
   failing at a configuration this machine actually reaches from `pload`.

   **What is NOT checked, and it is deliberate**: this file does not contain a
   second machine built on `pcut_scope_far`, so there is no run-against-run
   comparison of ANSWERS for this program. Duplicating `pstep` to get one would
   be two definitions of the semantics that can drift, which the note at
   `pstep_tr` rejects for the same reason. `guard_far_drive_reyields` supplies
   the answer-level separation instead, on the two residuals directly. ---- *)

let prog_sep : pcomp fv fcl =
  fscope plan_L0 body6 (fun cx0 ->
    fscope plan_L
      (resume_at_C plan_L0 cx0
         (fun z ->
            fscope plan_L0 body6
              (fun cb ->
                 resume_at_C plan_L0 cb (fun w -> fret (FL [FS "b"; fseen w])))))
      (fun ca -> resume_at_C plan_L ca fk))

(** The state predicate: a value at a boundary, with no mode in scope -- which is
    the exact position `pstep` calls `pyield` from -- at which the nearest cut
    gives a well-formed residual and the farthest cut violates BOTH conjuncts. *)
let fsep_at (cf: pconf fv fcl) : bool
  = match cf.st with
    | PStep (PVar _) (PBoundaryF :: rest) ->
      None? (pfind_mode rest) &&
      pno_floor (pcut_above (pcut_scope rest)) &&
      pno_mode (pcut_above (pcut_scope rest)) &&
      not (pno_floor (pcut_above (pcut_scope_far rest))) &&
      not (pno_mode (pcut_above (pcut_scope_far rest)))
    | _ -> false

(** One pass of the real machine, checking the predicate at every configuration.
    It is a scan and not a guessed step index, so the fixture states REACHABILITY
    rather than a number that would move if a bookkeeping step were added. *)
let rec fsep_scan (fuel: nat) (cf: pconf fv fcl) : Tot bool (decreases fuel)
  = if fuel = 0 then false
    else if fsep_at cf then true
    else fsep_scan (fuel - 1) (pstep flook fapply cf)

let fixture_22_separating_state_is_reachable () : Lemma
  (ensures fsep_scan 400 (pload prog_sep) == true
        /\ fsettled 800 prog_sep == true
        /\ fsep_scan 400 (pload prog_two_floors) == false
        /\ fsep_scan 400 (pload prog_nested) == false)
  = assert_norm (fsep_scan 400 (pload prog_sep) == true);
    assert_norm (fsettled 800 prog_sep == true);
    assert_norm (fsep_scan 400 (pload prog_two_floors) == false);
    assert_norm (fsep_scan 400 (pload prog_nested) == false)
