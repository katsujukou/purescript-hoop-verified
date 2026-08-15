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
 * ===========================================================================
 * **WHAT B1.8 CHANGED: THE OBSERVATION RELATION CAUGHT UP WITH THE TRACE.**
 *
 * B1.6 added `PEmit` and `prun` and showed, on two runs at fuel 400, that a
 * residual consumed twice emits the protected prefix's event ONCE while the
 * withdrawn suspension emits it TWICE. What it did not do was connect that to
 * any obligation. `pobs_le` and `pobs_eq` are stated through `pconverges`,
 * which observes the FINAL VALUE only, and on a pure machine replay changes no
 * value -- so **a prefix-replaying implementation satisfied every one of the
 * five laws exactly as they were stated**, and the exact-once result sat beside
 * the laws rather than inside them.
 *
 * B1.8 changes the RELATION, which is the only thing that could have closed
 * that. `pconverges_tr` converges to a TRACE AND a value and says so as "there
 * exists a step count", with no fuel in it; `pobs_tr_le` and `pobs_tr_eq`
 * preserve both, in both directions, from the same stack, store and counter;
 * and the five laws are stated over `pobs_tr_eq`. The value-only relation is
 * kept, and `lemma_pobs_tr_eq_forget` proves the new one implies it, so the
 * retarget is a strengthening rather than a change of subject.
 *
 * Three lemmas make the definition mean anything. `lemma_prun_stable` proves
 * that once a run has reached a terminal state, more fuel changes neither the
 * configuration NOR THE TRACE -- the trace being the half a careless driver
 * would break, by appending to it after the machine had stopped. Without it the
 * existential picks out no particular observation.
 * `lemma_pconverges_tr_unique` turns that into "at most one trace and at most
 * one value per configuration". And `lemma_prun_erase` proves `prun` and
 * `psteps` agree on the configuration at every fuel, so the instrumented driver
 * and the plain one are one semantics rather than two definitions that could
 * drift.
 *
 * What that buys is `guard_trace_separates_residual_from_suspension`: the
 * residual program and the suspension program are NOT equivalent under the new
 * relation, in either direction, as a THEOREM about the relation -- while
 * `guard_susp_agrees_on_value` checks that they converge to the same value, so
 * the separation is genuinely the trace's doing. That is what `fixture_11`
 * against `fixture_12` could not be.
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
 *   - ~~The four laws, plus `law_transparent_agrees`, are unproved.~~
 *     **B2b SETTLED THEM, AND THE ANSWER IS NO.** All five are FALSE of
 *     `ref_ops` as stated, and the negations are proved:
 *     `guard_ref_ops_refutes_left_identity`,
 *     `guard_ref_ops_refutes_right_identity`,
 *     `guard_ref_ops_refutes_transparent_agrees`,
 *     `guard_ref_ops_refutes_resume`, `guard_ref_ops_refutes_assoc` and, for
 *     `law_assoc`'s two conjuncts separately,
 *     `guard_ref_ops_refutes_assoc_algebraic` and
 *     `guard_ref_ops_refutes_assoc_anchored`. Nothing in this module depended on
 *     any of them holding, and nothing now depends on their failing either.
 *
 *     **The cause is the OBSERVATION and not the algebra, and the distinction is
 *     the finding.** `pobs_tr_le` fixes the store and the counter at the start
 *     and compares a `pval v` at the end; `pval v` contains `PCtxKey`; so the
 *     NAME of a freshly allocated handle is an observable. Each law compares a
 *     side that allocates with a side that does not, and a continuation that
 *     produces a context afterwards reads the difference off the counter. The
 *     counterexample stands at the EMPTY store and counter zero -- one
 *     transition from `pload` of a closed program, which
 *     `guard_ce_conf_one_step_from_pload` proves and `guard_ce_conf_ok` shows
 *     satisfies the full `pconf_ok` invariant -- so this is NOT the case of a
 *     law failing only where the machine cannot go.
 *
 *     **No law is amended and none is restated.** The two amendments available
 *     -- observing only answers in the image of `PV`, or quotienting by a store
 *     isomorphism -- each change what the laws claim, and choosing is a design
 *     decision about the relation. It is left open.
 *
 *     **Whether the five would hold under an amended relation is NOT
 *     established, in either direction.** The counterexample is silent about
 *     the difference that remains once handle names are hidden -- the left
 *     sides run the inner computation under `plan_protocol_frames` beneath a
 *     `PModeF MExtend`, the right sides under `plan_enter_frames` -- and that
 *     bisimulation is not attempted here. STATED, not proved.
 *
 *     **The laws as stated therefore DISCRIMINATE NOTHING, and that too is
 *     checked.** `guard_pointwise_ops_refutes_left_identity` and
 *     `guard_flat_ops_refutes_left_identity` refute `law_left_identity` of the
 *     other two implementations this file defines, by the same counterexample --
 *     so it is false of all three. These are NOT the separations the design
 *     wanted and must not be read as such; the block comment before them records
 *     how little they establish, and in particular that at `plan_A` the two sides
 *     `flat_ops` compares ARE the two sides `ref_ops` compares. The note on
 *     `flat_ops` carried an overclaim as a result -- that left identity, right
 *     identity and the algebraic half of associativity HOLD of it -- and it is
 *     corrected in place rather than deleted.
 *
 *     They remain stated over `pobs_tr_eq` and are therefore AT LEAST AS HARD as
 *     they were over `pobs_eq` -- `lemma_pobs_tr_eq_forget` proves that
 *     direction, and STRICTLY harder is still not established, since no pair is
 *     exhibited that the value-only relation joins and the trace-aware one does
 *     not. In particular the refutations above do NOT establish it: they turn on
 *     the VALUE and not on the trace, both sides running silently, so each of
 *     them refutes the corresponding `pobs_eq` law equally.
 *   - **That the trace-aware relation relates two DIFFERENT programs at all is
 *     now checked**, which before B2b it was not: everything the file
 *     established about `pobs_tr_eq` was a separation.
 *     `lemma_pobs_tr_eq_pbind_left` and `lemma_pobs_tr_eq_splice_nil` are two
 *     positive inhabitants, proved from `lemma_pconverges_tr_silent`. What that
 *     calculus does NOT give is a bisimulation: it relates two programs only
 *     when they converge on ONE configuration by emitting nothing, so it proves
 *     the administrative equations and no others.
 *   - **That `pobs_eq flook fapply prog_traced prog_susp` HOLDS is not claimed
 *     and not checked.** The value-only relation quantifies over every stack,
 *     store and counter, and this file proves nothing about it here. What
 *     `guard_susp_agrees_on_value` checks is the weaker and sufficient thing:
 *     at the one configuration where the traces separate the two programs, both
 *     converge to the SAME value, so the trace-aware separation is not one the
 *     value-only relation could have made there.
 *   - `settles` is DELETED, and what that establishes is that the laws can be
 *     STATED without it -- together with `fixture_10_outer_handler`, which runs
 *     the program `settles` used to exclude. Whether the propositions so stated
 *     HOLD of `ref_ops` was the same B2b obligation as the line above, and B2b
 *     answered it: they do not. **`settles` is not what would have saved them**,
 *     and that is worth recording so that its deletion is not blamed. The
 *     counterexample performs no operation whatever -- no `PPerform`, no
 *     ambient handler, nothing outside the plan -- so it is inside every domain
 *     `settles` would have carved out. Restoring the hypothesis would refute the
 *     laws at exactly the same configuration.
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
 * trade than leaving the nine conditions unchecked. The laws expose lookup as a
 * parameter, so B2b can state them uniformly over the lookup discipline it
 * assumes. Any theorem quantified over `lk` would include the former
 * reference-lookup instance; this file does not claim that the parameterisation
 * is a strict logical strengthening.
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
 *
 * **WHAT STRAND 2 DID WITH IT, recorded here because this paragraph is what it
 * was handed.** `lemma_pstep_store_resid_wf` is this lemma promoted to the step
 * case of an induction, and `lemma_reachable_residual_wf` is the
 * configuration-wide statement -- with NO condition on the initial term and NONE
 * on `apply`, which is not the shape this note expected. The warning above is
 * still exactly right; it is answered by SPLITTING the invariant rather than by
 * conditioning all of it. The STACK layer (`pwb`, `pterm_wb`, `papply_wb`) is
 * conditional, and what it buys is a different property -- that `PPaused` is
 * unreachable (`lemma_reachable_not_paused`). The STORE layer needs none of
 * that, because `pcut_scope` cuts at the nearest floor whether or not the stack
 * was well bracketed.
 *
 * The `post` question came out **no, FOR THE B2a RESIDUAL AND STACK-SAFETY
 * INVARIANTS**: the function component needs no condition of its own to keep a
 * stored residual `presid_wf` or to keep `PPaused` unreachable. `ctx_drive`
 * appends the driving consumer's `PModeF` beneath the residual, so `post` is
 * only ever run on a stack that carries that marker, and on such a stack the
 * shape obligation is vacuous. See `pterm_wb_n`'s clauses for the three
 * consuming nodes and `lemma_ctx_drive_wb`.
 *
 * **The scope of that answer, stated so a later gate does not inherit it.** It
 * is about SHAPE. Whether `post` needs a condition for B2b's observational laws
 * or for B3's simulation is untouched here: those are about what a computation
 * MEANS, and a `post` that is shape-correct can still return the wrong
 * computation. Read this as "no shape obligation", not as "no obligation".
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
 * `psteps` above is kept and is not defined through this one. That is a choice
 * that has to be paid for, and B1.8 pays for it: `lemma_pstep_tr_erase` and
 * `lemma_prun_erase` below say that forgetting the trace turns this driver back
 * into `psteps`, at every fuel and from every configuration. They are therefore
 * not two semantics that could drift apart -- they are one semantics and its
 * instrument, and gate condition 7 is that fact and nothing more.
 *
 * **A JUDGEMENT PROMOTED, AND THE HISTORY IS THE POINT.** B1.6 ended this
 * comment with:
 *
 *   "The laws are stated over `pconverges`, which is about values, and
 *    threading a trace through them would make every law also a statement about
 *    observations -- which is a different and much stronger claim than B2 is
 *    being asked for."
 *
 * That sentence was true of B1.6's brief and it is SUPERSEDED -- promoted, not
 * corrected. What overtook it is what B1.7 left visible: on a pure machine a
 * replay changes no value, so a value-only relation cannot tell a residual from
 * a suspension, and an implementation that re-runs the protected prefix at every
 * consumption satisfies all five laws exactly as they were then stated. The
 * exact-once result this driver was built to exhibit was thereby connected to no
 * proof obligation at all. The stronger claim is not optional any more; it is
 * the only claim under which exact-once is a law-level obligation rather than a
 * fixture. So the laws are retargeted at `pobs_tr_eq`,
 * `lemma_pobs_tr_le_forget` proves that the new relation implies the old one so
 * that nothing B1.6 stated is lost, and
 * `guard_trace_separates_residual_from_suspension` is the separation as a
 * statement ABOUT THE RELATION, which is what `fixture_11` against `fixture_12`
 * could not be.
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

(* ---- B1.8: the instrument is the same machine -------------------- *)

(**
 * **Trace erasure, one step.** PROVED, by case analysis on the current node.
 *
 * `pstep_tr` intercepts exactly one shape, `PStep (PEmit ev body) k`, and
 * returns `{ cf with st = PStep body k }` -- which is verbatim what `pstep`'s
 * `PEmit` arm returns through `keep`. Every other shape is delegated. So the
 * instrumented transition and the transition are the same function on states,
 * and the event list is a second result that no state depends on.
 *)
let lemma_pstep_tr_erase (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                         (cf: pconf v cl)
  : Lemma (ensures fst (pstep_tr lk apply cf) == pstep lk apply cf)
  = match cf.st with
    | PStep (PEmit _ _) _ -> ()
    | _ -> ()

(**
 * **Trace erasure, whole runs -- GATE CONDITION 7.** PROVED, by induction on the
 * fuel.
 *
 * `psteps` and `prun` are written as two recursions and this is the statement
 * that they are not two semantics. Both stop on the same four terminal shapes
 * and step on the same one; at the stepping case the configurations agree by
 * `lemma_pstep_tr_erase` and the induction hypothesis carries it forward. The
 * trace is the only thing `prun` has that `psteps` does not, and the equation
 * says so precisely: the FIRST component is `psteps`, on the nose.
 *)
let rec lemma_prun_erase (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                         (fuel: nat) (cf: pconf v cl)
  : Lemma (ensures fst (prun lk apply fuel cf) == psteps lk apply fuel cf)
          (decreases fuel)
  = if fuel = 0 then ()
    else
      match cf.st with
      | PDone _ -> ()
      | PPaused _ _ -> ()
      | PStuck _ _ -> ()
      | PRejected _ -> ()
      | PStep _ _ ->
        lemma_pstep_tr_erase lk apply cf;
        lemma_prun_erase lk apply (fuel - 1) (pstep lk apply cf)

(**
 * **FUEL STABILITY, FOR THE STATE AND FOR THE TRACE.** PROVED, by induction on
 * `n`, and it is the lemma without which "there exists a fuel at which the
 * machine has converged" defines nothing.
 *
 * The equation is between PAIRS, so it is one statement about the terminal
 * configuration and about the trace at once -- and the trace is the half that
 * could have failed. A driver that kept stepping after a terminal state would
 * preserve the state (the four terminal arms of `pstep` are the identity) while
 * appending to the trace at every further unit of fuel, and the existential
 * would then pick out no particular observation. `prun` does not: it returns
 * `(cf, [])` at a terminal state without consulting `pstep_tr`, so the extra
 * fuel contributes the empty list and `@` leaves the trace alone.
 *
 * The hypothesis is stated as "the run of `n` did not end mid-computation",
 * which is weaker than "ended in `PDone`" and covers the stuck, rejected and
 * paused ends too. `pconverges_tr` below uses only the `PDone` instance.
 *)
let rec lemma_prun_stable (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                          (n: nat) (extra: nat) (cf: pconf v cl)
  : Lemma (requires ~(PStep? (fst (prun lk apply n cf)).st))
          (ensures prun lk apply (n + extra) cf == prun lk apply n cf)
          (decreases n)
  = if n = 0 then ()
    else
      match cf.st with
      | PDone _ -> ()
      | PPaused _ _ -> ()
      | PStuck _ _ -> ()
      | PRejected _ -> ()
      | PStep _ _ ->
        lemma_prun_stable lk apply (n - 1) extra (fst (pstep_tr lk apply cf))

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
(*  B2a, strand 2: the invariant, configuration-wide                   *)
(*                                                                     *)
(*  Strand 1 left two LOCAL results: each takes a branch condition of   *)
(*  `pstep` as its hypothesis and says what that step does. This        *)
(*  section makes them configuration-wide, and it does so in TWO        *)
(*  LAYERS THAT ARE DELIBERATELY KEPT APART, because they need          *)
(*  different hypotheses and the difference is the finding.             *)
(*                                                                     *)
(*    - THE STORE LAYER, below, is UNCONDITIONAL. `presid_wf` holds of  *)
(*      every residual in the store of every reachable configuration,   *)
(*      for an ARBITRARY initial `pcomp` and an ARBITRARY `papply_t`.   *)
(*      No well-scopedness condition, no condition on `apply`, no       *)
(*      condition on the stack. This was not the expected shape and     *)
(*      the reason it comes out is recorded at                          *)
(*      `lemma_pstep_store_resid_wf`.                                   *)
(*                                                                     *)
(*    - THE STACK LAYER, further down, is CONDITIONAL, and it is where  *)
(*      the warning at `lemma_pyield_residual_wf` bites: a raw          *)
(*      `PSplice` can push any frame list it likes and `apply` can      *)
(*      return one, so it needs an initial-term condition (`pterm_wb`)  *)
(*      and a condition on the clause interpreter (`papply_wb`) -- the  *)
(*      counterparts of the shipped machine's `ws` and `apply_ok`. What *)
(*      it buys is a DIFFERENT property: that `PPaused` -- the          *)
(*      well-bracketing failure -- is unreachable.                      *)
(*                                                                     *)
(*  Keeping them apart is the point. Folding the store layer into the   *)
(*  conditional one would have made the thing strand 1 actually needs   *)
(*  depend on hypotheses it does not need, and a reader would have had  *)
(*  no way to see that.                                                 *)
(* ------------------------------------------------------------------ *)

(**
 * **The store condition: every context it holds has a well-formed residual.**
 *
 * `PCtxDone` carries no residual and is unconditionally acceptable -- there is
 * no boundary and no site frame left to ask, so `presid_wf` has nothing to say
 * about it. `PCtxRequests` is the case that matters, and the condition on it is
 * `presid_wf` VERBATIM: strand 1's predicate, reused and not restated.
 *)
let pctx_resid_wf (#v #cl: Type) (cx: pctx v cl) : bool
  = match cx with
    | PCtxDone _ -> true
    | PCtxRequests _ r _ -> presid_wf r

(** Pointwise over the store, as a `bool` recursion on the list rather than a
    `memP` quantifier, so that the fixtures can evaluate it. *)
let rec pstore_resid_wf (#v #cl: Type) (sto: pstore v cl) : Tot bool (decreases sto)
  = match sto with
    | [] -> true
    | (_, cx) :: rest -> pctx_resid_wf cx && pstore_resid_wf rest

(** Lookup respects it. PROVED, by induction on the store. *)
let rec lemma_store_resid_lookup (#v #cl: Type) (i: nat) (sto: pstore v cl)
  : Lemma (requires pstore_resid_wf sto)
          (ensures (match pstore_lookup i sto with
                    | None -> True
                    | Some cx -> pctx_resid_wf cx))
          (decreases sto)
  = match sto with
    | [] -> ()
    | _ :: rest -> lemma_store_resid_lookup i rest

(** And so does the only route a transition has to a context. PROVED. *)
let lemma_presolve_resid_wf (#v #cl: Type) (sto: pstore v cl) (h: pval v)
  : Lemma (requires pstore_resid_wf sto)
          (ensures (match presolve sto h with
                    | None -> True
                    | Some cx -> pctx_resid_wf cx))
  = match h with
    | PV _ -> ()
    | PCtxKey id -> lemma_store_resid_lookup id sto

(** **Extension does not touch the residual.** PROVED, and it is what makes the
    store layer close without a condition on `post`: `extend_ctx_C` composes onto
    the FUNCTION component and copies the segment across unchanged, so a
    well-formed residual stays the same well-formed residual however many times
    it is extended. *)
let lemma_extend_ctx_resid_wf
    (#v #cl: Type) (pl: plan v cl) (cx: pctx v cl) (g: pval v -> pcomp v cl)
  : Lemma (requires pctx_resid_wf cx)
          (ensures pctx_resid_wf (extend_ctx_C pl cx g))
  = ()

(** **Yielding stores a well-formed residual.** PROVED, and it is strand 1's
    theorem with its conclusion narrowed to the store. The hypotheses are the two
    branch conditions of the callers, exactly as there. *)
let lemma_pyield_store_resid_wf
    (#v #cl: Type) (x: pval v) (hd: pframe v cl)
    (rest: pstack v cl) (cf: pconf v cl)
  : Lemma (requires pstore_resid_wf cf.store /\
                    pfind_mode rest == None /\ (PBoundaryF? hd \/ PSiteF? hd))
          (ensures pstore_resid_wf (pyield x hd rest cf).store)
  = lemma_cut_no_floor rest;
    lemma_cut_no_mode rest

(**
 * **THE STORE LAYER, PRESERVED BY EVERY TRANSITION, UNCONDITIONALLY.** PROVED.
 *
 * There is no hypothesis on `lk`, none on `apply`, none on the stack and none on
 * the initial term. That is worth stating plainly because it was not the
 * expected shape, and the reason it comes out is a fact about which rules write
 * the store -- there are exactly three, and each of them is closed on its own:
 *
 *   - the `PScopeF` value rule allocates a `PCtxDone`, which carries no residual
 *     and so has nothing to violate;
 *   - `pyield` allocates the segment above the NEAREST floor, and
 *     `lemma_cut_no_floor` and `lemma_cut_no_mode` establish `presid_wf` of it
 *     from the branch guard alone, whatever the stack was and however it was
 *     built (`lemma_pyield_residual_wf`);
 *   - `PExtendCtxC` allocates `extend_ctx_C pl cx g`, which COPIES the residual
 *     of an already-stored context and changes only `post`.
 *
 * So the store is closed under the transition relation without any appeal to
 * reachability of the stack. **The warning at `lemma_pyield_residual_wf` is
 * about a different property.** "Every reachable stack is well-bracketed" is
 * indeed false for an arbitrary term and an arbitrary `apply`, and the stack
 * layer below is conditional for exactly that reason -- but the residual a yield
 * hands to the store is well formed on an ILL-BRACKETED stack too, because
 * `pcut_scope` cuts at the nearest floor whether or not that floor is where a
 * well-bracketed program would have put it. Nearness is doing the work that
 * reachability would otherwise have had to do.
 *)
let lemma_pstep_store_resid_wf
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Lemma (requires pstore_resid_wf cf.store)
          (ensures pstore_resid_wf (pstep lk apply cf).store)
  = match cf.st with
    | PStep c k ->
      (match c with
        | PExtendCtxC pl h g ->
          (match presolve cf.store h with
            | None -> ()
            | Some cx ->
              lemma_presolve_resid_wf cf.store h;
              lemma_extend_ctx_resid_wf pl cx g)
        | PVar value ->
          (match k with
            | PBoundaryF :: rest ->
              (match pfind_mode rest with
                | None -> lemma_pyield_store_resid_wf value PBoundaryF rest cf
                | Some _ -> ())
            | PSiteF fn :: rest ->
              (match pfind_mode rest with
                | None -> lemma_pyield_store_resid_wf value (PSiteF fn) rest cf
                | Some _ -> ())
            | _ -> ())
        | _ -> ())
    | _ -> ()

(* ---- The stack layer: shapes ------------------------------------- *)

(**
 * **"Something below can answer a boundary."** Defined FROM strand 1's two
 * predicates and not beside them, which is the reuse that section asked for.
 *
 * Unfolded, it says: `k` contains a scope floor, or a mode marker, or both. Both
 * halves are needed and they are what the two value rules do at a boundary --
 * a mode marker makes the boundary hand its value to a responder, a floor makes
 * it yield -- and a stack with neither is precisely the stack on which `pyield`
 * answers `PPaused`.
 *
 * It is a single BOOLEAN, which is what keeps the judgement below first-order:
 * everything a term needs to know about the stack it will run on, for the
 * purposes of this invariant, is this one bit.
 *)
let panswered (#v #cl: Type) (k: pstack v cl) : bool
  = not (pno_floor k && pno_mode k)

(**
 * **THE STACK CONDITION: every boundary and every recorded site has something
 * below it that can answer.**
 *
 * This is the configuration-wide counterpart of `presid_wf`, and the two are
 * deliberately different shapes. `presid_wf` is about a segment that has already
 * been cut and asks that the head frame reach the marker a consumer will append;
 * `pwb` is about a LIVE stack and asks that no boundary on it is stranded.
 *
 * **It is NOT "well-bracketed" in the sense the warning at
 * `lemma_pyield_residual_wf` says is false.** It does not say that a boundary is
 * matched by a floor pushed by the same `PEnterCtx`, nor that the frames between
 * them are the ones that production put there. It says only that the search a
 * boundary runs terminates at something rather than falling off the end. That
 * weaker statement is what a raw `PSplice` can be asked to respect, and it is
 * exactly enough for the payoff below.
 *)
let rec pwb (#v #cl: Type) (k: pstack v cl) : Tot bool (decreases k)
  = match k with
    | [] -> true
    | PBoundaryF :: rest -> panswered rest && pwb rest
    | PSiteF _ :: rest -> panswered rest && pwb rest
    | _ :: rest -> pwb rest

(** Both strand-1 predicates distribute over `@`. PROVED, by induction. *)
let rec lemma_pno_floor_append (#v #cl: Type) (a b: pstack v cl)
  : Lemma (ensures pno_floor (a @ b) == (pno_floor a && pno_floor b)) (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_pno_floor_append rest b

let rec lemma_pno_mode_append (#v #cl: Type) (a b: pstack v cl)
  : Lemma (ensures pno_mode (a @ b) == (pno_mode a && pno_mode b)) (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_pno_mode_append rest b

(** And so, therefore, does `panswered`. PROVED. *)
let lemma_panswered_append (#v #cl: Type) (a b: pstack v cl)
  : Lemma (ensures panswered (a @ b) == (panswered a || panswered b))
  = lemma_pno_floor_append a b;
    lemma_pno_mode_append a b

(** A mode search that answers is a stack that can answer. PROVED, by induction:
    `pfind_mode` returns `Some` only at a `PModeF` it reached without meeting a
    floor first, and that marker is what `panswered` sees. *)
let rec lemma_find_mode_answered (#v #cl: Type) (k: pstack v cl)
  : Lemma (ensures Some? (pfind_mode k) ==> panswered k) (decreases k)
  = match k with
    | [] -> ()
    | PModeF _ _ :: _ -> ()
    | PScopeF :: _ -> ()
    | _ :: rest -> lemma_find_mode_answered rest

(** **The interlock, stated as the fact the payoff needs.** PROVED, by induction.
    A stack that can answer and whose mode search came back empty must have a
    floor, and therefore a cut -- so `pyield` takes its `Some` arm and not its
    `PPaused` one. *)
let rec lemma_answered_has_cut (#v #cl: Type) (k: pstack v cl)
  : Lemma (requires panswered k /\ pfind_mode k == None)
          (ensures Some? (pcut_scope k))
          (decreases k)
  = match k with
    | [] -> ()
    | PScopeF :: _ -> ()
    | PModeF _ _ :: _ -> ()
    | _ :: rest -> lemma_answered_has_cut rest

(** The cut, as a decomposition of the stack it was taken from. PROVED. *)
let rec lemma_pcut_scope_shape (#v #cl: Type) (k: pstack v cl)
  : Lemma (ensures (match pcut_scope k with
                    | None -> True
                    | Some (a, b) -> k == a @ (PScopeF :: b)))
          (decreases k)
  = match k with
    | [] -> ()
    | PScopeF :: _ -> ()
    | _ :: rest -> lemma_pcut_scope_shape rest

(** The prompt search, likewise: the captured segment and what is below it
    reassemble into the stack, the found prompt frame being the last of the
    captured part. PROVED. *)
let rec lemma_pfind_prompt_shape
    (#v #cl: Type) (lk: plookup_t cl) (eff op: string) (k: pstack v cl)
  : Lemma (ensures (match pfind_prompt lk eff op k with
                    | None -> True
                    | Some (cap, _, below) -> k == cap @ below))
          (decreases k)
  = match k with
    | [] -> ()
    | PPromptF _ _ _ :: rest ->
      (match lk (PPromptF?.tbl (Cons?.hd k)) eff op with
        | Some _ -> ()
        | None -> lemma_pfind_prompt_shape lk eff op rest)
    | _ :: rest -> lemma_pfind_prompt_shape lk eff op rest

(** `pwb` is closed under taking suffixes. PROVED. *)
let rec lemma_pwb_suffix (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pwb (a @ b)) (ensures pwb b) (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_pwb_suffix rest b

(**
 * **`pwb` composes, and the side condition is the whole of the design.** PROVED,
 * by induction on the segment being pushed.
 *
 * If the stack underneath can already answer, the segment pushed on top is
 * unconstrained: every boundary in it sees that answer past whatever lies
 * between. If the stack underneath cannot, the segment must answer its own
 * boundaries. That disjunction is what lets a `PSplice` of a captured
 * continuation -- which may well carry a boundary whose floor was left behind --
 * be spliced back onto a stack that still holds the floor.
 *)
let rec lemma_pwb_append (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pwb b /\ (panswered b \/ pwb a))
          (ensures pwb (a @ b))
          (decreases a)
  = match a with
    | [] -> ()
    | f :: rest ->
      lemma_panswered_append rest b;
      lemma_pwb_append rest b

(** The converse, at the one hypothesis that makes it true. PROVED. When nothing
    below can answer, a composite stack's obligations are exactly the segment's
    own, so the segment is `pwb` on its own account. This is what discharges the
    premise of the condition on `apply` at a dispatch. *)
let rec lemma_pwb_split (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pwb (a @ b) /\ ~(panswered b))
          (ensures pwb a)
          (decreases a)
  = match a with
    | [] -> ()
    | f :: rest ->
      lemma_panswered_append rest b;
      lemma_pwb_split rest b

(** **The frames a scope is entered under carry no boundary and no site**, so
    they are `pwb` outright and answer nothing. PROVED, by induction on the plan;
    the owner frame is a prompt and adds neither. *)
let rec lemma_enter_layer_frames_shape (#v #cl: Type) (ls: list (plan_item v cl))
  : Lemma (ensures pwb (enter_layer_frames ls) /\ ~(panswered (enter_layer_frames ls)))
          (decreases ls)
  = match ls with
    | [] -> ()
    | _ :: rest -> lemma_enter_layer_frames_shape rest

let lemma_plan_enter_frames_shape (#v #cl: Type) (pl: plan v cl)
  : Lemma (ensures pwb (plan_enter_frames pl) /\ ~(panswered (plan_enter_frames pl)))
  = lemma_enter_layer_frames_shape (Plan?.layers pl);
    lemma_panswered_append (enter_layer_frames (Plan?.layers pl))
                           [owner_frame (Plan?.owner pl)];
    lemma_pwb_append (enter_layer_frames (Plan?.layers pl))
                     [owner_frame (Plan?.owner pl)]

(** Writing a cell rewrites one frame in place, and a `PParamF` is invisible to
    both strand-1 predicates, so nothing this section can see changes. PROVED, by
    induction, and split from the `pwb` half because the frame judgement below
    needs the `panswered` half on its own -- with no `pwb` hypothesis to carry. *)
let rec lemma_pset_param_answered
    (#v #cl: Type) (l: string) (x: pval v) (k: pstack v cl)
  : Lemma (ensures (match pset_param l x k with
                    | None -> True
                    | Some k' -> panswered k' == panswered k))
          (decreases k)
  = match k with
    | [] -> ()
    | PParamF l' _ :: rest ->
      if l' = l then () else lemma_pset_param_answered l x rest
    | _ :: rest -> lemma_pset_param_answered l x rest

let rec lemma_pset_param_shape
    (#v #cl: Type) (l: string) (x: pval v) (k: pstack v cl)
  : Lemma (requires pwb k)
          (ensures (match pset_param l x k with
                    | None -> True
                    | Some k' -> pwb k' /\ panswered k' == panswered k))
          (decreases k)
  = lemma_pset_param_answered l x k;
    match k with
    | [] -> ()
    | PParamF l' _ :: rest ->
      if l' = l then () else (lemma_pset_param_answered l x rest;
                              lemma_pset_param_shape l x rest)
    | _ :: rest ->
      lemma_pset_param_answered l x rest;
      lemma_pset_param_shape l x rest

(* ---- The stack layer: the judgement on terms ---------------------- *)

(**
 * **The well-scopedness judgement, and it is STEP-INDEXED for the reason
 * `Hoop.Runtime.WellScopedness.ws_n` is.**
 *
 * The obligation a prompt's return clause carries is `forall x. <judgement> (r x)`
 * with `r` reached through an `option`, and F* does not offer
 * `r x << PHandle tbl (Some r) prov body`: the subterm ordering gives the
 * function-application step only where the function is an IMMEDIATE constructor
 * argument, and `Some` interposes. The plain structural definition was written,
 * rejected at exactly those two clauses, and replaced by this one -- the same
 * repair, for the same reason, that the shipped judgement makes.
 *
 * `n = 0` is `True`, so a larger index is a STRONGER statement, and the
 * judgement proper is the intersection over all indices.
 *
 * **What the judgement says, read at `n` large.** Everything turns on ONE
 * question: whether the stack a term will run on can already answer a boundary.
 * If it can, the term is unconstrained here; if it cannot, then every raw frame
 * list the term splices must be `pwb` on its own account, and the suspended
 * computations those frames carry must be judged in turn.
 *
 *   - `PSplice fs body` is where the whole judgement earns its keep. It is the
 *     one node that can put arbitrary frames on the stack -- the warning at
 *     `lemma_pyield_residual_wf` names it -- so this is the clause that asks for
 *     `pwb fs`. `body` is judged only if the segment did not itself answer.
 *
 *   - `PWeave` splices `plan_enter_frames`, which drops the bind frames and
 *     keeps the prompts. So the condition on its intervening segment is
 *     `pints_wb`, which constrains the PROMPT RETURN CLAUSES and nothing else --
 *     minimal on purpose, since a condition on the bind frames would be a demand
 *     on continuations that `enter_layer_frames` discards.
 *
 *   - **`PEnterCtx`, `PExtendC`, `PExtendCtxC` and `PResumeC` ask for NOTHING,
 *     and that is a result rather than an omission.** Production pushes its own
 *     `PScopeF` beneath everything it installs, so every frame it lays down and
 *     the body itself run on a stack that can answer; a consumer splices the
 *     residual with its own `PModeF` appended beneath it, so the same is true
 *     there. The four nodes that manipulate scopes are exactly the four that
 *     cannot strand a boundary. See `lemma_pstep_state_wb` for where this is
 *     discharged.
 *)
let rec pterm_wb_n (#v #cl: Type) (n: nat) (c: pcomp v cl)
  : Tot prop (decreases %[n; 4; 0])
  = if n = 0 then True
    else
      match c with
      | PVar _ -> True
      | PPerform _ _ _ -> True
      | PReadP _ -> True
      | PWriteP _ _ -> True
      | POp inner fn ->
          pterm_wb_n (n - 1) inner /\ (forall (x: pval v). pterm_wb_n (n - 1) (fn x))
      | PHandle _ ret _ body -> pret_wb_n n ret /\ pterm_wb_n (n - 1) body
      | PEmit _ body -> pterm_wb_n (n - 1) body
      | PNewP _ _ body -> pterm_wb_n (n - 1) body
      | PSplice fs body ->
          pwb fs /\ pframes_wb_n n fs /\ (panswered fs \/ pterm_wb_n (n - 1) body)
      | PWeave _ _ ints own body ->
          pints_wb_n n ints /\ pret_wb_n n (POwner?.ret own) /\ pterm_wb_n (n - 1) body
      | PEnterCtx _ _ -> True
      | PExtendC _ _ _ -> True
      | PExtendCtxC _ _ _ -> True
      | PResumeC _ _ _ -> True

(**
 * **The judgement on a live stack**, and the `panswered rest` escape is the
 * whole of its content: a frame's suspended computation will be resumed on what
 * lies BELOW that frame, so if that can answer, the computation is unconstrained.
 *
 * `PSiteF` and `PModeF` carry functions and are given NO obligation here, which
 * is worth a sentence. A `PSiteF`'s function is run by exactly one rule, and
 * only in the arm where `pfind_mode` answered -- so the stack it is run on
 * contains that marker and can answer. A `PModeF`'s responder likewise runs at a
 * boundary that found this very marker. Both are therefore always resumed on an
 * answering stack, and an obligation here would be one no rule could ever use.
 *)
and pframes_wb_n (#v #cl: Type) (n: nat) (fs: pstack v cl)
  : Tot prop (decreases %[n; 3; length fs])
  = if n = 0 then True
    else
      match fs with
      | [] -> True
      | fr :: rest -> (panswered rest \/ pframe_wb_n n fr) /\ pframes_wb_n n rest

(** **The judgement on a `PWeave`'s intervening segment**: the prompts' return
    clauses, and nothing else, because `plan_layers` followed by
    `enter_layer_frames` keeps exactly those. Unconditional -- no `panswered`
    escape -- because the segment is REBUILT into a frame list of its own, in
    which nothing answers, so what the segment sat above is no help. *)
and pints_wb_n (#v #cl: Type) (n: nat) (fs: pstack v cl)
  : Tot prop (decreases %[n; 3; length fs])
  = if n = 0 then True
    else
      match fs with
      | [] -> True
      | PPromptF _ ret _ :: rest -> pret_wb_n n ret /\ pints_wb_n n rest
      | _ :: rest -> pints_wb_n n rest

and pframe_wb_n (#v #cl: Type) (n: nat) (fr: pframe v cl)
  : Tot prop (decreases %[n; 2; 0])
  = if n = 0 then True
    else
      match fr with
      | PBindF fn -> forall (x: pval v). pterm_wb_n (n - 1) (fn x)
      | PPromptF _ ret _ -> pret_wb_n n ret
      | _ -> True

and pret_wb_n (#v #cl: Type) (n: nat) (ret: option (pval v -> pcomp v cl))
  : Tot prop (decreases %[n; 1; 0])
  = if n = 0 then True
    else
      match ret with
      | None -> True
      | Some r -> forall (x: pval v). pterm_wb_n (n - 1) (r x)

(** The judgements proper: the intersection over every index. *)
let pterm_wb (#v #cl: Type) (c: pcomp v cl) : prop
  = forall (n: nat). pterm_wb_n n c
let pframes_wb (#v #cl: Type) (fs: pstack v cl) : prop
  = forall (n: nat). pframes_wb_n n fs
let pints_wb (#v #cl: Type) (fs: pstack v cl) : prop
  = forall (n: nat). pints_wb_n n fs
let pframe_wb (#v #cl: Type) (fr: pframe v cl) : prop
  = forall (n: nat). pframe_wb_n n fr
let pret_wb (#v #cl: Type) (ret: option (pval v -> pcomp v cl)) : prop
  = forall (n: nat). pret_wb_n n ret

(* ---- The defining equations, recovered from the index ------------- *)
(*                                                                     *)
(*  The step index is an implementation detail of the definition and    *)
(*  nothing below it mentions one. These are the equations the rest of  *)
(*  the section works through, exactly as `Hoop.Runtime.Metatheory`     *)
(*  assembles `ws_var`, `ws_op`, `ws_splice` and the rest into the      *)
(*  structural reading of `ws`. Each is PROVED.                         *)

let lemma_wb_trivial (#v #cl: Type) (c: pcomp v cl)
  : Lemma (requires PVar? c \/ PPerform? c \/ PReadP? c \/ PWriteP? c \/
                    PEnterCtx? c \/ PExtendC? c \/ PExtendCtxC? c \/ PResumeC? c)
          (ensures pterm_wb c)
  = ()

(** The one equation that needs its index peeled by hand: both components of a
    bind are judged at `n - 1`, so neither direction is a single instantiation.
    PROVED, in two halves. *)
let lemma_wb_op_fwd (#v #cl: Type) (inner: pcomp v cl) (fn: pval v -> pcomp v cl)
  : Lemma (requires pterm_wb (POp inner fn))
          (ensures pterm_wb inner /\ (forall (x: pval v). pterm_wb (fn x)))
  = introduce forall (n: nat). pterm_wb_n n inner
    with assert (pterm_wb_n (n + 1) (POp inner fn));
    introduce forall (x: pval v). pterm_wb (fn x)
    with (introduce forall (n: nat). pterm_wb_n n (fn x)
          with assert (pterm_wb_n (n + 1) (POp inner fn)))

let lemma_wb_op_bwd (#v #cl: Type) (inner: pcomp v cl) (fn: pval v -> pcomp v cl)
  : Lemma (requires pterm_wb inner /\ (forall (x: pval v). pterm_wb (fn x)))
          (ensures pterm_wb (POp inner fn))
  = introduce forall (n: nat). pterm_wb_n n (POp inner fn)
    with (if n = 0 then () else assert (pterm_wb_n (n - 1) inner))

let lemma_wb_op (#v #cl: Type) (inner: pcomp v cl) (fn: pval v -> pcomp v cl)
  : Lemma (pterm_wb (POp inner fn)
           <==> (pterm_wb inner /\ (forall (x: pval v). pterm_wb (fn x))))
  = introduce pterm_wb (POp inner fn)
              ==> (pterm_wb inner /\ (forall (x: pval v). pterm_wb (fn x)))
    with lemma_wb_op_fwd inner fn;
    introduce (pterm_wb inner /\ (forall (x: pval v). pterm_wb (fn x)))
              ==> pterm_wb (POp inner fn)
    with lemma_wb_op_bwd inner fn

let lemma_wb_handle_fwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance) (body: pcomp v cl)
  : Lemma (requires pterm_wb (PHandle tbl ret prov body))
          (ensures pret_wb ret /\ pterm_wb body)
  = introduce forall (n: nat). pret_wb_n n ret
    with (if n = 0 then () else assert (pterm_wb_n n (PHandle tbl ret prov body)));
    introduce forall (n: nat). pterm_wb_n n body
    with assert (pterm_wb_n (n + 1) (PHandle tbl ret prov body))

let lemma_wb_handle_bwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance) (body: pcomp v cl)
  : Lemma (requires pret_wb ret /\ pterm_wb body)
          (ensures pterm_wb (PHandle tbl ret prov body))
  = introduce forall (n: nat). pterm_wb_n n (PHandle tbl ret prov body)
    with (if n = 0 then ()
          else (assert (pret_wb_n n ret); assert (pterm_wb_n (n - 1) body)))

let lemma_wb_emit_fwd (#v #cl: Type) (ev: string) (body: pcomp v cl)
  : Lemma (requires pterm_wb (PEmit ev body)) (ensures pterm_wb body)
  = introduce forall (n: nat). pterm_wb_n n body
    with assert (pterm_wb_n (n + 1) (PEmit ev body))

let lemma_wb_emit_bwd (#v #cl: Type) (ev: string) (body: pcomp v cl)
  : Lemma (requires pterm_wb body) (ensures pterm_wb (PEmit ev body))
  = introduce forall (n: nat). pterm_wb_n n (PEmit ev body)
    with (if n = 0 then () else assert (pterm_wb_n (n - 1) body))

let lemma_wb_newp_fwd (#v #cl: Type) (l: string) (init: pval v) (body: pcomp v cl)
  : Lemma (requires pterm_wb (PNewP l init body)) (ensures pterm_wb body)
  = introduce forall (n: nat). pterm_wb_n n body
    with assert (pterm_wb_n (n + 1) (PNewP l init body))

let lemma_wb_newp_bwd (#v #cl: Type) (l: string) (init: pval v) (body: pcomp v cl)
  : Lemma (requires pterm_wb body) (ensures pterm_wb (PNewP l init body))
  = introduce forall (n: nat). pterm_wb_n n (PNewP l init body)
    with (if n = 0 then () else assert (pterm_wb_n (n - 1) body))

let lemma_wb_splice_fwd (#v #cl: Type) (fs: pstack v cl) (body: pcomp v cl)
  : Lemma (requires pterm_wb (PSplice fs body))
          (ensures pwb fs /\ pframes_wb fs /\ (panswered fs \/ pterm_wb body))
  = assert (pterm_wb_n 1 (PSplice fs body));
    introduce forall (n: nat). pframes_wb_n n fs
    with (if n = 0 then () else assert (pterm_wb_n n (PSplice fs body)));
    if panswered fs then ()
    else (introduce forall (n: nat). pterm_wb_n n body
          with assert (pterm_wb_n (n + 1) (PSplice fs body)))

let lemma_wb_splice_bwd (#v #cl: Type) (fs: pstack v cl) (body: pcomp v cl)
  : Lemma (requires pwb fs /\ pframes_wb fs /\ (panswered fs \/ pterm_wb body))
          (ensures pterm_wb (PSplice fs body))
  = introduce forall (n: nat). pterm_wb_n n (PSplice fs body)
    with (if n = 0 then ()
          else (assert (pframes_wb_n n fs);
                if panswered fs then () else assert (pterm_wb_n (n - 1) body)))

let lemma_wb_weave_fwd
    (#v #cl: Type) (oeff oop: string) (ints: pstack v cl)
    (own: powner v cl) (body: pcomp v cl)
  : Lemma (requires pterm_wb (PWeave oeff oop ints own body))
          (ensures pints_wb ints /\ pret_wb (POwner?.ret own) /\ pterm_wb body)
  = introduce forall (n: nat). pints_wb_n n ints
    with (if n = 0 then () else assert (pterm_wb_n n (PWeave oeff oop ints own body)));
    introduce forall (n: nat). pret_wb_n n (POwner?.ret own)
    with (if n = 0 then () else assert (pterm_wb_n n (PWeave oeff oop ints own body)));
    introduce forall (n: nat). pterm_wb_n n body
    with assert (pterm_wb_n (n + 1) (PWeave oeff oop ints own body))

let lemma_wb_frames_nil (#v #cl: Type) ()
  : Lemma (pframes_wb ([] <: pstack v cl))
  = ()

let lemma_wb_frames_cons_fwd (#v #cl: Type) (fr: pframe v cl) (rest: pstack v cl)
  : Lemma (requires pframes_wb (fr :: rest))
          (ensures (panswered rest \/ pframe_wb fr) /\ pframes_wb rest)
  = introduce forall (n: nat). pframes_wb_n n rest
    with (if n = 0 then () else assert (pframes_wb_n n (fr :: rest)));
    if panswered rest then ()
    else (introduce forall (n: nat). pframe_wb_n n fr
          with (if n = 0 then () else assert (pframes_wb_n n (fr :: rest))))

let lemma_wb_frames_cons_bwd (#v #cl: Type) (fr: pframe v cl) (rest: pstack v cl)
  : Lemma (requires (panswered rest \/ pframe_wb fr) /\ pframes_wb rest)
          (ensures pframes_wb (fr :: rest))
  = introduce forall (n: nat). pframes_wb_n n (fr :: rest)
    with (if n = 0 then ()
          else (assert (pframes_wb_n n rest);
                if panswered rest then () else assert (pframe_wb_n n fr)))

let lemma_wb_frame_bind_fwd (#v #cl: Type) (fn: pval v -> pcomp v cl)
  : Lemma (requires pframe_wb (PBindF fn))
          (ensures forall (x: pval v). pterm_wb (fn x))
  = introduce forall (x: pval v). pterm_wb (fn x)
    with (introduce forall (n: nat). pterm_wb_n n (fn x)
          with assert (pframe_wb_n (n + 1) (PBindF fn)))

let lemma_wb_frame_bind_bwd (#v #cl: Type) (fn: pval v -> pcomp v cl)
  : Lemma (requires forall (x: pval v). pterm_wb (fn x))
          (ensures pframe_wb (PBindF fn))
  = introduce forall (n: nat). pframe_wb_n n (PBindF fn)
    with (if n = 0 then () else ())

let lemma_wb_frame_prompt_fwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance)
  : Lemma (requires pframe_wb (PPromptF tbl ret prov)) (ensures pret_wb ret)
  = introduce forall (n: nat). pret_wb_n n ret
    with (if n = 0 then () else assert (pframe_wb_n n (PPromptF tbl ret prov)))

let lemma_wb_frame_prompt_bwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance)
  : Lemma (requires pret_wb ret) (ensures pframe_wb (PPromptF tbl ret prov))
  = introduce forall (n: nat). pframe_wb_n n (PPromptF tbl ret prov)
    with (if n = 0 then () else assert (pret_wb_n n ret))

let lemma_wb_frame_inert (#v #cl: Type) (fr: pframe v cl)
  : Lemma (requires PParamF? fr \/ PBoundaryF? fr \/ PSiteF? fr \/
                    PModeF? fr \/ PScopeF? fr)
          (ensures pframe_wb fr)
  = ()

let lemma_wb_ret_none (#v #cl: Type) ()
  : Lemma (pret_wb (None <: option (pval v -> pcomp v cl)))
  = ()

let lemma_wb_ret_some_fwd (#v #cl: Type) (r: pval v -> pcomp v cl)
  : Lemma (requires pret_wb (Some r)) (ensures forall (x: pval v). pterm_wb (r x))
  = introduce forall (x: pval v). pterm_wb (r x)
    with (introduce forall (n: nat). pterm_wb_n n (r x)
          with assert (pret_wb_n (n + 1) (Some r)))

let lemma_wb_ret_some_bwd (#v #cl: Type) (r: pval v -> pcomp v cl)
  : Lemma (requires forall (x: pval v). pterm_wb (r x)) (ensures pret_wb (Some r))
  = introduce forall (n: nat). pret_wb_n n (Some r)
    with (if n = 0 then () else ())

let lemma_wb_ints_nil (#v #cl: Type) ()
  : Lemma (pints_wb ([] <: pstack v cl))
  = ()

let lemma_wb_ints_prompt_fwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance) (rest: pstack v cl)
  : Lemma (requires pints_wb (PPromptF tbl ret prov :: rest))
          (ensures pret_wb ret /\ pints_wb rest)
  = introduce forall (n: nat). pret_wb_n n ret
    with (if n = 0 then () else assert (pints_wb_n n (PPromptF tbl ret prov :: rest)));
    introduce forall (n: nat). pints_wb_n n rest
    with (if n = 0 then () else assert (pints_wb_n n (PPromptF tbl ret prov :: rest)))

let lemma_wb_ints_prompt_bwd
    (#v #cl: Type) (tbl: ptable cl) (ret: option (pval v -> pcomp v cl))
    (prov: prompt_provenance) (rest: pstack v cl)
  : Lemma (requires pret_wb ret /\ pints_wb rest)
          (ensures pints_wb (PPromptF tbl ret prov :: rest))
  = introduce forall (n: nat). pints_wb_n n (PPromptF tbl ret prov :: rest)
    with (if n = 0 then ()
          else (assert (pret_wb_n n ret); assert (pints_wb_n n rest)))

let lemma_wb_ints_other_fwd (#v #cl: Type) (fr: pframe v cl) (rest: pstack v cl)
  : Lemma (requires ~(PPromptF? fr) /\ pints_wb (fr :: rest))
          (ensures pints_wb rest)
  = introduce forall (n: nat). pints_wb_n n rest
    with (if n = 0 then () else assert (pints_wb_n n (fr :: rest)))

let lemma_wb_ints_other_bwd (#v #cl: Type) (fr: pframe v cl) (rest: pstack v cl)
  : Lemma (requires ~(PPromptF? fr) /\ pints_wb rest)
          (ensures pints_wb (fr :: rest))
  = introduce forall (n: nat). pints_wb_n n (fr :: rest)
    with (if n = 0 then () else assert (pints_wb_n n rest))

(* ---- `pframes_wb` composes, exactly as `pwb` does ----------------- *)

let rec lemma_pframes_wb_append_n
    (#v #cl: Type) (n: nat) (a b: pstack v cl)
  : Lemma (requires pframes_wb_n n b /\ (panswered b \/ pframes_wb_n n a))
          (ensures pframes_wb_n n (a @ b))
          (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest ->
      lemma_panswered_append rest b;
      lemma_pframes_wb_append_n n rest b

let rec lemma_pframes_wb_split_n
    (#v #cl: Type) (n: nat) (a b: pstack v cl)
  : Lemma (requires pframes_wb_n n (a @ b) /\ ~(panswered b))
          (ensures pframes_wb_n n a)
          (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest ->
      lemma_panswered_append rest b;
      lemma_pframes_wb_split_n n rest b

let rec lemma_pframes_wb_suffix_n
    (#v #cl: Type) (n: nat) (a b: pstack v cl)
  : Lemma (requires pframes_wb_n n (a @ b))
          (ensures pframes_wb_n n b)
          (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_pframes_wb_suffix_n n rest b

(** The same three, with the index quantified away. PROVED. *)
let lemma_pframes_wb_append (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pframes_wb b /\ (panswered b \/ pframes_wb a))
          (ensures pframes_wb (a @ b))
  = introduce forall (n: nat). pframes_wb_n n (a @ b)
    with lemma_pframes_wb_append_n n a b

let lemma_pframes_wb_split (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pframes_wb (a @ b) /\ ~(panswered b))
          (ensures pframes_wb a)
  = introduce forall (n: nat). pframes_wb_n n a
    with lemma_pframes_wb_split_n n a b

let lemma_pframes_wb_suffix (#v #cl: Type) (a b: pstack v cl)
  : Lemma (requires pframes_wb (a @ b))
          (ensures pframes_wb b)
  = introduce forall (n: nat). pframes_wb_n n b
    with lemma_pframes_wb_suffix_n n a b

(** Writing a cell preserves the frame judgement too. PROVED, at a fixed index by
    induction, then lifted. *)
let rec lemma_pset_param_frames_wb_n
    (#v #cl: Type) (n: nat) (l: string) (x: pval v) (k: pstack v cl)
  : Lemma (requires pframes_wb_n n k)
          (ensures (match pset_param l x k with
                    | None -> True
                    | Some k' -> pframes_wb_n n k'))
          (decreases k)
  = match k with
    | [] -> ()
    | PParamF l' _ :: rest ->
      if l' = l then ()
      else (lemma_pset_param_answered l x rest;
            lemma_pset_param_frames_wb_n n l x rest)
    | _ :: rest ->
      lemma_pset_param_answered l x rest;
      lemma_pset_param_frames_wb_n n l x rest

let lemma_pset_param_frames_wb
    (#v #cl: Type) (l: string) (x: pval v) (k: pstack v cl)
  : Lemma (requires pframes_wb k)
          (ensures (match pset_param l x k with
                    | None -> True
                    | Some k' -> pframes_wb k'))
  = match pset_param l x k with
    | None -> ()
    | Some k' ->
      introduce forall (n: nat). pframes_wb_n n k'
      with lemma_pset_param_frames_wb_n n l x k

(**
 * **The frames a `PWeave` splices satisfy the frame judgement**, given only the
 * judgement on the prompts of its intervening segment. PROVED, by induction on
 * that segment.
 *
 * This is where `pints_wb` is shown to be exactly the right condition rather
 * than a convenient one: the walk below is `plan_layers` followed by
 * `enter_layer_frames`, and every frame it produces is either a `PParamF`, which
 * carries no obligation, or a `PPromptF` whose return clause is either `None`
 * (a transparent layer, whose clause the classification already established was
 * absent) or one that came from a prompt of the segment. The bind frames are
 * DROPPED by `enter_layer_frames`, which is why `pints_wb` does not constrain
 * them.
 *)
let rec lemma_plan_layers_wb (#v #cl: Type) (ints: pstack v cl)
  : Lemma (requires pints_wb ints)
          (ensures (match plan_layers ints with
                    | Inl _ -> True
                    | Inr ls -> pframes_wb (enter_layer_frames ls)))
          (decreases ints)
  = match ints with
    | [] -> lemma_wb_frames_nil #v #cl ()
    | PBindF fn :: rest ->
      lemma_wb_ints_other_fwd (PBindF fn) rest;
      lemma_plan_layers_wb rest
    | PParamF l y :: rest ->
      lemma_wb_ints_other_fwd (PParamF l y) rest;
      lemma_plan_layers_wb rest;
      (match plan_layers rest with
        | Inl _ -> ()
        | Inr ls ->
          lemma_wb_frame_inert (PParamF l y <: pframe v cl);
          lemma_wb_frames_cons_bwd (PParamF l y) (enter_layer_frames ls))
    | PPromptF tbl ret prov :: rest ->
      lemma_wb_ints_prompt_fwd tbl ret prov rest;
      lemma_plan_layers_wb rest;
      (match classify_prompt prov tbl ret with
        | Monomorphic -> ()
        | ContextTransparent ->
          (match plan_layers rest with
            | Inl _ -> ()
            | Inr ls ->
              lemma_wb_ret_none #v #cl ();
              lemma_wb_frame_prompt_bwd #v #cl tbl None PMono;
              lemma_wb_frames_cons_bwd (PPromptF tbl None PMono) (enter_layer_frames ls))
        | Family ->
          (match plan_layers rest with
            | Inl _ -> ()
            | Inr ls ->
              lemma_wb_frame_prompt_bwd tbl ret PFamily;
              lemma_wb_frames_cons_bwd (PPromptF tbl ret PFamily) (enter_layer_frames ls)))
    | PBoundaryF :: rest ->
      lemma_wb_ints_other_fwd (PBoundaryF <: pframe v cl) rest;
      lemma_plan_layers_wb rest
    | PSiteF fn :: rest ->
      lemma_wb_ints_other_fwd (PSiteF fn) rest;
      lemma_plan_layers_wb rest
    | PModeF m r :: rest ->
      lemma_wb_ints_other_fwd (PModeF m r) rest;
      lemma_plan_layers_wb rest
    | PScopeF :: rest ->
      lemma_wb_ints_other_fwd (PScopeF <: pframe v cl) rest;
      lemma_plan_layers_wb rest

(** And with the owner's frame appended, which is what `plan_enter_frames` is.
    PROVED. *)
let lemma_plan_enter_frames_wb (#v #cl: Type) (ints: pstack v cl) (own: powner v cl)
  : Lemma (requires pints_wb ints /\ pret_wb (POwner?.ret own))
          (ensures (match plan_of ints own with
                    | Inl _ -> True
                    | Inr pl -> pframes_wb (plan_enter_frames pl)))
  = lemma_plan_layers_wb ints;
    match plan_layers ints with
    | Inl _ -> ()
    | Inr ls ->
      lemma_wb_frame_prompt_bwd (POwner?.tbl own) (POwner?.ret own) (POwner?.prov own);
      lemma_wb_frames_nil #v #cl ();
      lemma_wb_frames_cons_bwd (owner_frame own) ([] <: pstack v cl);
      lemma_pframes_wb_append (enter_layer_frames ls) [owner_frame own]

(* ---- The condition on the clause interpreter --------------------- *)

(**
 * **The condition imposed on the FFI parameter `apply`**, and it is
 * `Hoop.Runtime.WellScopedness.apply_ok` with one thing missing.
 *
 * A clause handed a payload and a continuation whose every branch is judged
 * builds a computation that is judged. **There is no `cok` and no `can`**: the
 * shipped `apply_ok` carries a clause predicate and a capability environment
 * because `ws` is a judgement about WHICH ACTIONS may be fired, and a clause has
 * to be admissible in the environment it runs in. This judgement is about
 * FRAME SHAPES ONLY -- it says nothing about effect labels -- so there is
 * nothing for a clause predicate to say and nothing for an environment to index.
 * The divergence is a consequence of what the two judgements are about, not a
 * weakening of this one.
 *
 * As there, this is NOT provable inside F* and is not meant to be: `apply` is a
 * parameter. It appears only as a hypothesis. `guard_fapply_wb` below discharges
 * it for the fixtures' own interpreter, which is the check that it is not
 * vacuous.
 *)
let papply_wb (#v #cl: Type) (apply: papply_t v cl) : prop
  = forall (c: cl) (payload: list (pval v)) (kf: (pval v -> pcomp v cl)).
      (forall (x: pval v). pterm_wb (kf x)) ==> pterm_wb (apply c payload kf)

(* ---- The configuration invariant --------------------------------- *)

(**
 * **The machine invariant.** The stack is `pwb`, every computation suspended in
 * it is judged where it will be resumed, and the control component is judged
 * unless the stack can already answer.
 *
 * **`PPaused` is `False`, and that is the payoff.** It is the state a boundary
 * reaches with no consumer above it and no floor below it -- the well-bracketing
 * failure the `pstate` header calls a totality obligation, checked by execution
 * at `fixture_9_paused_is_unreachable` on the fixtures and by this invariant on
 * every program satisfying `pterm_wb`.
 *
 * **`PStuck` is `True`, and that is a divergence from the shipped `wf_state`,
 * which sets `Stuck` to `False` and proves progress.** It cannot be `False`
 * here, and not because the proof would be hard: a stuck state is REACHABLE and
 * MEANT to be. A forged handle is `PStuck pctx_eff pctx_missing_op` by design
 * (`fixture_19_forged_handle_fails`), and an operation no prompt handles is
 * `PStuck eff op` (`fixture_10_detached_gets_stuck`). Ruling those out would
 * make the invariant false, not stronger. Progress in the shipped sense is a
 * statement about capabilities and would need the capability judgement this
 * prototype does not have.
 *
 * `PRejected` is `True` for the reason the shipped `wf_state` gives: refusing a
 * scope is not a failure of this kind.
 *)
let pstate_wb (#v #cl: Type) (s: pstate v cl) : prop
  = match s with
    | PDone _ -> True
    | PStuck _ _ -> True
    | PRejected _ -> True
    | PPaused _ _ -> False
    | PStep c k -> pwb k /\ pframes_wb k /\ (panswered k \/ pterm_wb c)

(** **THE CONFIGURATION INVARIANT**: freshness, the store layer and the stack
    layer, composed. The first two conjuncts need no hypothesis to be preserved;
    the third needs `papply_wb`. *)
let pconf_ok (#v #cl: Type) (cf: pconf v cl) : prop
  = pconf_wf cf /\ pstore_resid_wf cf.store /\ pstate_wb cf.st

(** **Loading establishes it, from the initial-term condition and nothing else.**
    PROVED. The store is empty and `next` is zero, so both of those conjuncts are
    immediate; the stack is empty, which is `pwb`, carries nothing, and -- being
    unable to answer -- is exactly why the term must be judged. *)
let lemma_pload_ok (#v #cl: Type) (c: pcomp v cl)
  : Lemma (requires pterm_wb c) (ensures pconf_ok (pload c))
  = lemma_wb_frames_nil #v #cl ()

(* ---- Preservation, rule by rule ---------------------------------- *)

(** **Driving a context always builds a judged term, for ANY context and any
    consumer function.** PROVED, and it is why the three consuming nodes carry no
    obligation: `ctx_drive` appends its own `PModeF` beneath the residual, so
    every boundary and every site in that residual is answered by the marker the
    consumer just installed, whatever the residual is and whatever it is spliced
    onto. Nothing here appeals to `presid_wf`. *)
let lemma_ctx_drive_wb
    (#v #cl: Type) (m: weave_mode) (cx: pctx v cl) (f: pval v -> pcomp v cl)
  : Lemma (ensures pterm_wb (ctx_drive m cx f))
  = match cx with
    | PCtxDone y -> lemma_wb_trivial (PVar y <: pcomp v cl)
    | PCtxRequests x resid post ->
      let mk : pstack v cl = [PModeF m (fun (z: pval v) -> pbind (post z) f)] in
      assert_norm (ctx_drive m (PCtxRequests x resid post) f
                   == PSplice (resid @ mk) (PVar x));
      lemma_wb_frame_inert (Cons?.hd mk);
      lemma_wb_frames_nil #v #cl ();
      lemma_wb_frames_cons_bwd (Cons?.hd mk) ([] <: pstack v cl);
      lemma_panswered_append resid mk;
      lemma_pwb_append resid mk;
      lemma_pframes_wb_append resid mk;
      lemma_wb_trivial (PVar x <: pcomp v cl);
      lemma_wb_splice_bwd (resid @ mk) (PVar x)

(** **Yielding lands in a judged state, and in particular NOT in `PPaused`.**
    PROVED. `panswered rest` comes from `pwb` at the boundary or site frame the
    value arrived at, and `pfind_mode rest == None` is the branch guard; together
    they force a floor, hence a cut. *)
let lemma_pyield_state_wb
    (#v #cl: Type) (x: pval v) (hd: pframe v cl)
    (rest: pstack v cl) (cf: pconf v cl)
  : Lemma (requires pwb rest /\ pframes_wb rest /\
                    panswered rest /\ pfind_mode rest == None)
          (ensures pstate_wb (pyield x hd rest cf).st)
  = lemma_answered_has_cut rest;
    lemma_pcut_scope_shape rest;
    match pcut_scope rest with
    | None -> ()
    | Some (above, below) ->
      lemma_pwb_suffix above (PScopeF :: below);
      lemma_pframes_wb_suffix above (PScopeF :: below);
      lemma_wb_frames_cons_fwd (PScopeF <: pframe v cl) below;
      lemma_wb_trivial (PVar (PCtxKey cf.next) <: pcomp v cl)

(**
 * **THE STACK LAYER, PRESERVED BY EVERY TRANSITION.** PROVED, and the only
 * hypothesis beyond the invariant itself is the one on `apply`. The lookup `lk`
 * is arbitrary; no condition on the handler tables is needed, because this
 * judgement does not speak about effect labels.
 *
 * Read the case analysis for where the work is:
 *
 *   - `PSplice` is the case the whole judgement exists for, and it discharges
 *     from the node's own `pwb fs`.
 *   - `PPerform` is the case that needs `papply_wb`, and it needs it only when
 *     the stack BELOW the handling prompt cannot answer -- in which case the
 *     captured segment's own obligations are exactly what the composite stack
 *     had, so `lemma_pwb_split` hands the premise over. When the stack below CAN
 *     answer, the conclusion is not needed at all.
 *   - `PEnterCtx` and the three consuming rules discharge with no appeal to the
 *     term, for the reason recorded at `pterm_wb_n` and `lemma_ctx_drive_wb`.
 *   - the boundary and site value rules are where `PPaused` is excluded.
 *)
let lemma_pstep_state_wb
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Lemma (requires papply_wb apply /\ pstate_wb cf.st)
          (ensures pstate_wb (pstep lk apply cf).st)
  = match cf.st with
    | PDone _ -> ()
    | PPaused _ _ -> ()
    | PStuck _ _ -> ()
    | PRejected _ -> ()
    | PStep c k ->
      match c with
      | POp inner fn ->
        if panswered k then lemma_wb_frames_cons_bwd (PBindF fn) k
        else (lemma_wb_op_fwd inner fn;
              lemma_wb_frame_bind_bwd fn;
              lemma_wb_frames_cons_bwd (PBindF fn) k)
      | PHandle tbl ret prov body ->
        if panswered k then lemma_wb_frames_cons_bwd (PPromptF tbl ret prov) k
        else (lemma_wb_handle_fwd tbl ret prov body;
              lemma_wb_frame_prompt_bwd tbl ret prov;
              lemma_wb_frames_cons_bwd (PPromptF tbl ret prov) k)
      | PPerform eff op payload ->
        (match pfind_prompt lk eff op k with
          | None -> ()
          | Some (captured, found, below) ->
            lemma_pfind_prompt_shape lk eff op k;
            lemma_pwb_suffix captured below;
            lemma_pframes_wb_suffix captured below;
            if panswered below then ()
            else (lemma_pwb_split captured below;
                  lemma_pframes_wb_split captured below;
                  introduce forall (x: pval v). pterm_wb (pkont_of captured x)
                  with (lemma_wb_trivial (PVar x <: pcomp v cl);
                        lemma_wb_splice_bwd captured (PVar x))))
      | PEmit ev body ->
        if panswered k then () else lemma_wb_emit_fwd ev body
      | PWeave oeff oop ints own body ->
        (match plan_of ints own with
          | Inl _ -> ()
          | Inr pl ->
            if panswered k then ()
            else (lemma_wb_weave_fwd oeff oop ints own body;
                  lemma_plan_enter_frames_shape pl;
                  lemma_plan_enter_frames_wb ints own;
                  lemma_wb_splice_bwd (plan_enter_frames pl) body))
      | PEnterCtx pl body ->
        let pf = plan_protocol_frames pl in
        let t : pstack v cl = PScopeF :: k in
        lemma_wb_frame_inert (PScopeF <: pframe v cl);
        lemma_wb_frames_cons_bwd (PScopeF <: pframe v cl) k;
        lemma_panswered_append pf t;
        lemma_pwb_append pf t;
        lemma_pframes_wb_append pf t;
        lemma_wb_frames_cons_bwd (PBoundaryF <: pframe v cl) (pf @ t)
      | PExtendC pl h g ->
        (match presolve cf.store h with
          | None -> ()
          | Some cx -> lemma_ctx_drive_wb MExtend cx g)
      | PExtendCtxC pl h g ->
        (match presolve cf.store h with
          | None -> ()
          | Some cx -> lemma_wb_trivial (PVar (PCtxKey cf.next) <: pcomp v cl))
      | PResumeC pl h kk ->
        (match presolve cf.store h with
          | None -> ()
          | Some cx -> lemma_ctx_drive_wb MResume cx kk)
      | PVar value ->
        (match k with
          | [] -> ()
          | PBindF fn :: rest ->
            lemma_wb_frames_cons_fwd (PBindF fn) rest;
            if panswered rest then () else lemma_wb_frame_bind_fwd fn
          | PParamF l y :: rest ->
            lemma_wb_frames_cons_fwd (PParamF l y) rest;
            lemma_wb_trivial (PVar value <: pcomp v cl)
          | PModeF m r :: rest ->
            lemma_wb_frames_cons_fwd (PModeF m r) rest;
            lemma_wb_trivial (PVar value <: pcomp v cl)
          | PScopeF :: rest ->
            lemma_wb_frames_cons_fwd (PScopeF <: pframe v cl) rest;
            lemma_wb_trivial (PVar (PCtxKey cf.next) <: pcomp v cl)
          | PBoundaryF :: rest ->
            lemma_wb_frames_cons_fwd (PBoundaryF <: pframe v cl) rest;
            (match pfind_mode rest with
              | None -> lemma_pyield_state_wb value PBoundaryF rest cf
              | Some _ -> ())
          | PSiteF fn :: rest ->
            lemma_wb_frames_cons_fwd (PSiteF fn) rest;
            (match pfind_mode rest with
              | None -> lemma_pyield_state_wb value (PSiteF fn) rest cf
              | Some (MResume, _) -> ()
              | Some (MExtend, _) -> lemma_wb_trivial (PVar value <: pcomp v cl))
          | PPromptF tbl ret prov :: rest ->
            lemma_wb_frames_cons_fwd (PPromptF tbl ret prov) rest;
            (match ret with
              | None -> lemma_wb_trivial (PVar value <: pcomp v cl)
              | Some fn ->
                if panswered rest then ()
                else (lemma_wb_frame_prompt_fwd tbl ret prov;
                      lemma_wb_ret_some_fwd fn)))
      | PSplice fs body ->
        lemma_panswered_append fs k;
        if panswered k
        then (lemma_pwb_append fs k; lemma_pframes_wb_append fs k)
        else (lemma_wb_splice_fwd fs body;
              lemma_pwb_append fs k;
              lemma_pframes_wb_append fs k)
      | PNewP l init body ->
        lemma_wb_frame_inert (PParamF l init <: pframe v cl);
        lemma_wb_frames_cons_bwd (PParamF l init) k;
        if panswered k then () else lemma_wb_newp_fwd l init body
      | PReadP l ->
        (match pfind_param l k with
          | None -> ()
          | Some y -> lemma_wb_trivial (PVar y <: pcomp v cl))
      | PWriteP l y ->
        lemma_pset_param_shape l y k;
        lemma_pset_param_frames_wb l y k;
        lemma_wb_trivial (PVar y <: pcomp v cl)

(** Freshness is preserved too -- the three allocation sites are all `palloc`,
    and `lemma_alloc_wf` is what says so. PROVED. *)
let lemma_pstep_conf_wf
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Lemma (requires pconf_wf cf) (ensures pconf_wf (pstep lk apply cf))
  = ()

(** **THE INVARIANT, PRESERVED BY THE TRANSITION RELATION.** PROVED. The three
    conjuncts are discharged by the three lemmas above, and only the third of
    them uses `papply_wb`. *)
let lemma_pstep_conf_ok
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Lemma (requires papply_wb apply /\ pconf_ok cf)
          (ensures pconf_ok (pstep lk apply cf))
  = lemma_pstep_conf_wf lk apply cf;
    lemma_pstep_store_resid_wf lk apply cf;
    lemma_pstep_state_wb lk apply cf

(** The instrumented transition differs from `pstep` on exactly one node, and
    that node leaves the stack alone. PROVED. *)
let lemma_pstep_tr_conf_ok
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : Lemma (requires papply_wb apply /\ pconf_ok cf)
          (ensures pconf_ok (fst (pstep_tr lk apply cf)))
  = match cf.st with
    | PStep (PEmit ev body) k ->
      if panswered k then () else lemma_wb_emit_fwd ev body
    | _ -> lemma_pstep_conf_ok lk apply cf

(* ---- Preservation along a run ------------------------------------ *)

(** The store layer, along a whole run, still with no hypothesis. PROVED. *)
let rec lemma_psteps_store_resid_wf
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (cf: pconf v cl)
  : Lemma (requires pstore_resid_wf cf.store)
          (ensures pstore_resid_wf (psteps lk apply fuel cf).store)
          (decreases fuel)
  = if fuel = 0 then ()
    else
      match cf.st with
      | PStep _ _ ->
        lemma_pstep_store_resid_wf lk apply cf;
        lemma_psteps_store_resid_wf lk apply (fuel - 1) (pstep lk apply cf)
      | _ -> ()

(** The whole invariant, along a whole run. PROVED. *)
let rec lemma_psteps_conf_ok
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (cf: pconf v cl)
  : Lemma (requires papply_wb apply /\ pconf_ok cf)
          (ensures pconf_ok (psteps lk apply fuel cf))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      match cf.st with
      | PStep _ _ ->
        lemma_pstep_conf_ok lk apply cf;
        lemma_psteps_conf_ok lk apply (fuel - 1) (pstep lk apply cf)
      | _ -> ()

(** And along an instrumented run. PROVED. *)
let rec lemma_prun_conf_ok
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (cf: pconf v cl)
  : Lemma (requires papply_wb apply /\ pconf_ok cf)
          (ensures pconf_ok (fst (prun lk apply fuel cf)))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      match cf.st with
      | PStep _ _ ->
        lemma_pstep_tr_conf_ok lk apply cf;
        lemma_prun_conf_ok lk apply (fuel - 1) (fst (pstep_tr lk apply cf))
      | _ -> ()

(* ---- The consequences ------------------------------------------- *)

(**
 * **THE CONSEQUENCE STRAND 1 ASKED FOR: `presid_wf` holds of every residual the
 * store can ever contain.** PROVED, from `pload`, over any number of
 * transitions, at any key, FOR ANY INITIAL TERM AND ANY CLAUSE INTERPRETER.
 *
 * This is `lemma_pyield_residual_wf` promoted from a statement about one step to
 * a statement about the machine. Strand 1's production-side theorem gives the
 * step case; `lemma_pstep_store_resid_wf` closes the induction; and this is what
 * it says at the only starting point the machine has.
 *)
let lemma_reachable_residual_wf
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (c: pcomp v cl) (i: nat)
  : Lemma (ensures (let cfr = psteps lk apply fuel (pload c) in
                    match pstore_lookup i cfr.store with
                    | Some (PCtxRequests _ r _) -> presid_wf r
                    | _ -> True))
  = lemma_psteps_store_resid_wf lk apply fuel (pload c);
    lemma_store_resid_lookup i (psteps lk apply fuel (pload c)).store

(**
 * **The two strands closed against each other**: a residual taken out of the
 * store of ANY configuration whose store satisfies the invariant is one that
 * `lemma_ctx_drive_answers_head` applies to, so driving it reaches the driving
 * consumer's marker at its head frame and allocates nothing.
 *
 * PROVED. It is strand 1's consumption theorem with its one hypothesis --
 * `presid_wf` -- discharged from the store rather than assumed of a residual
 * written by hand. Read together with `lemma_reachable_residual_wf`, which says
 * the store of every reachable configuration satisfies it, this is the whole of
 * what B2a set out to establish: production only ever stores residuals whose
 * head frame the mode search can reach, consumption only ever asks about such
 * residuals, and NO REACHABILITY ASSUMPTION IS LEFT ANYWHERE IN THE ARGUMENT.
 *
 * The residual is taken apart in the SIGNATURE rather than in the conclusion:
 * the hypothesis says the store holds exactly this context at this key, which
 * makes the statement one a caller can instantiate at a key it has in hand. A
 * residual with no head frame is excluded by the store condition already --
 * `presid_wf []` is `false` -- so no arm is owed for it.
 *)
let lemma_stored_residual_answers_head
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (i: nat) (m: weave_mode)
    (x: pval v) (hd: pframe v cl) (a: pstack v cl) (post: pval v -> pcomp v cl)
    (f: pval v -> pcomp v cl) (k: pstack v cl)
  : Lemma (requires pstore_resid_wf cf.store /\
                    pstore_lookup i cf.store == Some (PCtxRequests x (hd :: a) post))
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
  = lemma_store_resid_lookup i cf.store;
    lemma_ctx_drive_answers_head lk apply cf m x hd a post f k

(**
 * **THE STACK LAYER'S PAYOFF: `PPaused` is unreachable.** PROVED, from the
 * initial-term condition and the condition on the clause interpreter.
 *
 * `fixture_9_paused_is_unreachable` checks this by execution on the fixture
 * programs and at a fixed fuel; this is the same statement for every program
 * satisfying `pterm_wb`, every interpreter satisfying `papply_wb`, every lookup
 * and every fuel. It is exactly the totality obligation the `pstate` header
 * records at `PPaused` -- "a stack that no transition of this machine can build"
 * -- discharged rather than observed.
 *)
let lemma_reachable_not_paused
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (c: pcomp v cl)
  : Lemma (requires papply_wb apply /\ pterm_wb c)
          (ensures ~(PPaused? (psteps lk apply fuel (pload c)).st))
  = lemma_pload_ok c;
    lemma_psteps_conf_ok lk apply fuel (pload c)

(** The same, along an instrumented run. PROVED. *)
let lemma_prun_not_paused
    (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (fuel: nat) (c: pcomp v cl)
  : Lemma (requires papply_wb apply /\ pterm_wb c)
          (ensures ~(PPaused? (fst (prun lk apply fuel (pload c))).st))
  = lemma_pload_ok c;
    lemma_prun_conf_ok lk apply fuel (pload c)

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
 * **B2b CORRECTION, and it is a correction to the sentence above and not to the
 * argument in it.** "Left identity, right identity and the algebraic half of
 * associativity all hold of it" is FALSE as an assertion about the propositions
 * this file defines: `guard_flat_ops_refutes_left_identity` proves that
 * `law_left_identity` does not hold of `flat_ops`. The sentence was a claim
 * about a plan-free ALGEBRA, and `pobs_tr_eq` is not an algebraic equality -- it
 * observes the store's counter, and `flat_ops`'s production allocates exactly as
 * the reference one does. The underlying argument stands: an implementation
 * wrong uniformly satisfies every equation BETWEEN ITS OWN OPERATIONS, and that
 * is still why at least one law must be anchored. What does not stand is the
 * inference from that to "these three propositions hold of `flat_ops`".
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
(*  A NOTE B1.5 LEFT, B1.6 ANSWERED ELSEWHERE, AND B1.8 CLOSES.         *)
(*  `pobs_eq` observes VALUES, and a replayed pure prefix returns what  *)
(*  it returned before, so `pobs_eq` cannot separate the residual from  *)
(*  the suspension and it would be wrong to claim it does. B1.6 added   *)
(*  not a stronger relation but a coarser observable -- `PEmit` and     *)
(*  `prun`, outside the value language entirely -- and left exact-once  *)
(*  as `fixture_11` against `fixture_12`, two runs at one fixed fuel.   *)
(*                                                                     *)
(*  THAT IS THE GAP B1.8 EXISTS TO CLOSE, and it is worth naming        *)
(*  precisely, because it is not a gap in the machine. On a pure        *)
(*  machine replay changes no value, so AN IMPLEMENTATION THAT RE-RUNS  *)
(*  THE PROTECTED PREFIX AT EVERY CONSUMPTION SATISFIES ALL FIVE LAWS   *)
(*  AS THEY WERE STATED OVER `pobs_eq`. B1.6's exact-once result was    *)
(*  therefore attached to no proof obligation whatever: it was a        *)
(*  measurement beside the laws, not a constraint on them.              *)
(*                                                                     *)
(*  So the relation itself changes. `pconverges_tr` below converges to  *)
(*  a TRACE AND a value, `pobs_tr_le` / `pobs_tr_eq` preserve both, and *)
(*  the laws are retargeted at `pobs_tr_eq`. The value-only relation is *)
(*  KEPT, not replaced: `lemma_pobs_tr_le_forget` proves the new        *)
(*  relation implies it, which is how everything B1.5 and B1.6 stated   *)
(*  survives the promotion instead of being quietly dropped.            *)
(*                                                                     *)
(*  `fixture_1_prefix_runs_once` stays as a regression test on cost and *)
(*  is still not offered as the semantic statement.                     *)
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
(*  B1.8: THE TRACE-AWARE OBSERVATION                                  *)
(* ------------------------------------------------------------------ *)

(**
 * **Convergence to a trace AND a value -- gate condition 1.**
 *
 * Written as "there EXISTS a step count", not at a fixed fuel, and that is gate
 * condition 3: no concrete number occurs in the definition, so no law stated
 * through it can be satisfied by an implementation that merely agrees up to some
 * particular budget. Comparing `prun n` at one chosen `n` would have been such a
 * statement, and `fixture_11` against `fixture_12` -- both at fuel 400 -- is
 * exactly that weaker thing.
 *
 * `PDone` is the only end that counts as convergence. Stuck, rejected and paused
 * ends are NOT convergence and two computations that both fail are not thereby
 * related by anything below; they are simply outside the relation's antecedent,
 * as they were under `pconverges`.
 *
 * The existential is only a definition because of `lemma_prun_stable`: once the
 * run has reached a terminal state, more fuel changes neither the configuration
 * nor the trace. `lemma_pconverges_tr_unique` is that fact in the form this
 * definition needs -- a configuration converges to AT MOST ONE trace and at most
 * one value -- and without it "the trace of `cf`" would not denote.
 *)
let pconverges_tr (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                  (cf: pconf v cl) (tr: list string) (x: pval v) : GTot prop =
  exists (n: nat).
    (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr

(**
 * **The observation converges to at most one trace and at most one value.**
 * PROVED, from `lemma_prun_stable` alone.
 *
 * Two witnesses `n1` and `n2` are given; the smaller one has already reached
 * `PDone`, so stability carries its whole result -- configuration and trace --
 * forward to the larger, and the two readings coincide. This is the lemma that
 * makes the existential in `pconverges_tr` a definition of an observable rather
 * than a claim that SOME reading of the run looks like this.
 *)
let lemma_pconverges_tr_unique (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (tr1 tr2: list string) (x1 x2: pval v)
  : Lemma (requires pconverges_tr lk apply cf tr1 x1 /\ pconverges_tr lk apply cf tr2 x2)
          (ensures tr1 == tr2 /\ x1 == x2)
  = eliminate exists (n1: nat).
        (fst (prun lk apply n1 cf)).st == PDone x1 /\ snd (prun lk apply n1 cf) == tr1
    with
      (eliminate exists (n2: nat).
           (fst (prun lk apply n2 cf)).st == PDone x2 /\ snd (prun lk apply n2 cf) == tr2
       with
         (if n1 <= n2
          then lemma_prun_stable lk apply n1 (n2 - n1) cf
          else lemma_prun_stable lk apply n2 (n1 - n2) cf))

(**
 * **THE TRACE-AWARE ORDERING -- gate condition 2.**
 *
 * It is `pobs_le` with the observable widened. Everything B1.7 established about
 * the quantification is kept verbatim and for the same reasons: both sides start
 * from the SAME stack, the SAME store and the SAME allocation counter, so an
 * implementation cannot pass by allocating differently, and the store is ranged
 * over because a computation mentioning a handle means nothing without one.
 *
 * What is added is `tr`. The consequent demands the same trace, so a program
 * that emits the same events in a different ORDER, or one more time, or one time
 * fewer, is not below anything that does not. That is the whole of the gate:
 * under `pobs_le` a prefix-replaying implementation is indistinguishable from a
 * residual one, and under this it is not.
 *
 * `x` is still quantified, so this is AT LEAST AS STRONG as `pobs_le` and not
 * merely different -- `lemma_pobs_tr_le_forget` proves that direction.
 *
 * **Not "strictly" stronger, and the difference is not pedantic.** Strictness
 * would need a witness: a pair related by `pobs_eq` and not by `pobs_tr_eq`.
 * `prog_traced` and `prog_susp` are the obvious candidates and this file does
 * NOT establish them as one -- see the header, which records that
 * `pobs_eq flook fapply prog_traced prog_susp` is neither claimed nor checked.
 * What is proved is the implication one way; the converse failing is expected
 * and unwitnessed.
 *)
let pobs_tr_le (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (c1 c2: pcomp v cl) : GTot prop =
  forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
         (tr: list string) (x: pval v).
    pconverges_tr lk apply ({ st = PStep c1 k; store = sto; next = n0 }) tr x ==>
    pconverges_tr lk apply ({ st = PStep c2 k; store = sto; next = n0 }) tr x

(** **The trace-aware equivalence**: convergence to the same trace and the same
    value is preserved in BOTH directions, from every stack, store and counter.
    This is what the five laws are stated over from B1.8 on. *)
let pobs_tr_eq (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
               (c1 c2: pcomp v cl) : GTot prop =
  pobs_tr_le lk apply c1 c2 /\ pobs_tr_le lk apply c2 c1

(**
 * **Forgetting the trace -- gate condition 4, at the level of convergence.**
 * PROVED, and the proof is `lemma_prun_erase`: the witness that works for the
 * trace-aware convergence is the same number, and erasure turns `prun`'s first
 * component into `psteps`.
 *)
let lemma_pconverges_tr_forget (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (tr: list string) (x: pval v)
  : Lemma (requires pconverges_tr lk apply cf tr x)
          (ensures pconverges lk apply cf x)
  = eliminate exists (n: nat).
        (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr
    with
      (lemma_prun_erase lk apply n cf;
       introduce exists (m: nat). (psteps lk apply m cf).st == PDone x
       with n and ())

(**
 * **The converse direction, which is what the implication needs.** PROVED. Given
 * a value-only convergence, the run at that same fuel HAS a trace -- namely
 * `snd (prun lk apply n cf)` -- so the trace-aware convergence holds at it, and
 * a trace-aware ordering can be applied.
 *)
let lemma_pconverges_has_trace (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (x: pval v)
  : Lemma (requires pconverges lk apply cf x)
          (ensures exists (tr: list string). pconverges_tr lk apply cf tr x)
  = eliminate exists (n: nat). (psteps lk apply n cf).st == PDone x
    with
      (lemma_prun_erase lk apply n cf;
       assert (pconverges_tr lk apply cf (snd (prun lk apply n cf)) x);
       introduce exists (tr: list string). pconverges_tr lk apply cf tr x
       with (snd (prun lk apply n cf)) and ())

(**
 * **GATE CONDITION 4: the trace-aware ordering IMPLIES the value-only one.**
 * PROVED.
 *
 * This is what makes the promotion a promotion. Every law that B1.6 and B1.7
 * stated over `pobs_eq` is a consequence of the corresponding law over
 * `pobs_tr_eq`, so retargeting the five laws does not abandon a single one of
 * the obligations they carried -- it adds to them. If the implication had gone
 * the other way, or neither way, the retarget would have been a change of
 * subject rather than a strengthening, and it would have had to be argued
 * separately that the old claims still held.
 *)
let lemma_pobs_tr_le_forget (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (c1 c2: pcomp v cl)
  : Lemma (requires pobs_tr_le lk apply c1 c2)
          (ensures pobs_le lk apply c1 c2)
  = introduce forall (k: pstack v cl) (sto: pstore v cl) (n0: nat) (x: pval v).
      pconverges lk apply ({ st = PStep c1 k; store = sto; next = n0 }) x ==>
      pconverges lk apply ({ st = PStep c2 k; store = sto; next = n0 }) x
    with
      (introduce
         pconverges lk apply ({ st = PStep c1 k; store = sto; next = n0 }) x ==>
         pconverges lk apply ({ st = PStep c2 k; store = sto; next = n0 }) x
       with
         (lemma_pconverges_has_trace lk apply
            ({ st = PStep c1 k; store = sto; next = n0 }) x;
          eliminate exists (tr: list string).
              pconverges_tr lk apply ({ st = PStep c1 k; store = sto; next = n0 }) tr x
          with
            lemma_pconverges_tr_forget lk apply
              ({ st = PStep c2 k; store = sto; next = n0 }) tr x))

(** The same, for the equivalences. PROVED. *)
let lemma_pobs_tr_eq_forget (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (c1 c2: pcomp v cl)
  : Lemma (requires pobs_tr_eq lk apply c1 c2)
          (ensures pobs_eq lk apply c1 c2)
  = lemma_pobs_tr_le_forget lk apply c1 c2;
    lemma_pobs_tr_le_forget lk apply c2 c1

(* ------------------------------------------------------------------ *)
(*  B2b, FIRST: A SILENT-STEP CALCULUS, AND THE FIRST POSITIVE FACTS   *)
(*  ABOUT THE TRACE-AWARE RELATION                                     *)
(*                                                                     *)
(*  EVERYTHING THIS FILE ESTABLISHED ABOUT `pobs_tr_eq` BEFORE B2b WAS  *)
(*  NEGATIVE. `guard_trace_separates_residual_from_suspension` exhibits *)
(*  a pair the relation does NOT join, and no lemma exhibited a pair it *)
(*  does. That was a gap in the evidence and not a small one: a         *)
(*  relation that joined nothing but a term with itself would refute    *)
(*  all five laws, and it would refute them for a reason that had       *)
(*  nothing to do with weaving. Before a law is attempted it is worth   *)
(*  knowing the relation is loose enough to relate two DIFFERENT        *)
(*  programs at all.                                                    *)
(*                                                                     *)
(*  The three lemmas below settle that, and they are also the tool      *)
(*  every positive result in B2b is built from. `prun` is a function,   *)
(*  so the machine is deterministic, and the trace of a run is the      *)
(*  CONCATENATION of its steps' traces -- so a transition that emits    *)
(*  nothing relates the observations of the two configurations it joins *)
(*  IN BOTH DIRECTIONS, the witness shifting by exactly one unit of     *)
(*  fuel. Two programs that reach a COMMON configuration by silent      *)
(*  steps are therefore `pobs_tr_eq`, at every stack, store and         *)
(*  counter, and nothing about well-formedness is needed to see it.     *)
(*                                                                     *)
(*  What the calculus does NOT give is a bisimulation. It relates two   *)
(*  programs only when they CONVERGE ON ONE CONFIGURATION, so it        *)
(*  proves the administrative equations and no others. That limit is    *)
(*  worth stating because it is exactly the limit B2b ran into: the     *)
(*  five laws' two sides do not converge on one configuration, and the  *)
(*  finding recorded at `guard_ref_ops_refutes_left_identity` below is  *)
(*  that they cannot be made to.                                        *)
(* ------------------------------------------------------------------ *)

(** **A transition that emits nothing.** `pstep_tr` intercepts exactly one shape,
    so this is "the current node is not a `PEmit`" written in terms of what the
    instrument reports rather than in terms of the node -- which is the form the
    two lemmas below use it in, and which does not have to be revisited if
    another emitting node is ever added. *)
let psilent (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl) (cf: pconf v cl)
  : prop
  = PStep? cf.st /\ snd (pstep_tr lk apply cf) == []

(**
 * **One silent step shifts the fuel by one and leaves the trace alone.** PROVED,
 * by unfolding `prun` once.
 *
 * `n + 1` is not zero and the state is a `PStep`, so `prun` takes its stepping
 * branch; the event list is empty by hypothesis, and `[] @ tr` is `tr` by
 * `append`'s own first equation, so the pair is the pair of the shorter run from
 * the successor configuration -- state AND trace, not state alone.
 *)
let lemma_prun_silent_unroll (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (n: nat) (cf: pconf v cl)
  : Lemma (requires psilent lk apply cf)
          (ensures prun lk apply (n + 1) cf == prun lk apply n (pstep lk apply cf))
  = lemma_pstep_tr_erase lk apply cf

(**
 * **A silent step preserves the trace-aware observation, IN BOTH DIRECTIONS.**
 * PROVED.
 *
 * This is the one fact the positive side of B2b rests on, and the biconditional
 * is what makes it usable: an equivalence needs both orderings, and a lemma that
 * gave only one would have to be applied to a second, differently-oriented
 * configuration to get the other.
 *
 * The two halves are not symmetric in difficulty and it is worth saying why. The
 * `<==` half is the shift: a witness `m` from the successor becomes `m + 1` here.
 * The `==>` half additionally needs `n > 0`, and that comes from the hypothesis
 * `PStep? cf.st` -- `prun lk apply 0 cf` is `(cf, [])`, whose state is a `PStep`
 * and hence not a `PDone`, so no witness can be zero.
 *)
let lemma_pconverges_tr_silent (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (tr: list string) (x: pval v)
  : Lemma (requires psilent lk apply cf)
          (ensures (pconverges_tr lk apply cf tr x <==>
                    pconverges_tr lk apply (pstep lk apply cf) tr x))
  = introduce pconverges_tr lk apply cf tr x ==>
              pconverges_tr lk apply (pstep lk apply cf) tr x
    with
      (eliminate exists (n: nat).
           (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr
       with
         (assert (n > 0);
          lemma_prun_silent_unroll lk apply (n - 1) cf;
          introduce exists (m: nat).
              (fst (prun lk apply m (pstep lk apply cf))).st == PDone x /\
              snd (prun lk apply m (pstep lk apply cf)) == tr
          with (n - 1) and ()));
    introduce pconverges_tr lk apply (pstep lk apply cf) tr x ==>
              pconverges_tr lk apply cf tr x
    with
      (eliminate exists (m: nat).
           (fst (prun lk apply m (pstep lk apply cf))).st == PDone x /\
           snd (prun lk apply m (pstep lk apply cf)) == tr
       with
         (lemma_prun_silent_unroll lk apply m cf;
          introduce exists (n: nat).
              (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr
          with (m + 1) and ()))

(**
 * **A POSITIVE INHABITANT OF `pobs_tr_eq` AT TWO DIFFERENT PROGRAMS: the inner
 * monad's LEFT IDENTITY.** PROVED, and it is the first such fact in the file.
 *
 * `pbind (PVar x) f` and `f x` are distinct terms -- distinct constructors at the
 * head, for most `f` -- and the relation joins them. Two silent transitions do
 * it: the `POp` rule pushes `PBindF f`, and the `PVar` rule against that frame
 * runs `f x` on the stack the whole thing started on. The store and the counter
 * are untouched by both, which is why the statement holds at EVERY store and
 * counter rather than at a well-formed one: no allocation happens on either side,
 * so there is nothing for the two sides to disagree about.
 *
 * **That last sentence is the whole of the positive theory of this relation, and
 * its converse is the whole of the negative one.** `pobs_tr_le` fixes the store
 * and the counter at the START and compares the values at the END, and `pval`
 * contains `PCtxKey`, so a program that allocates a context and returns its
 * handle observes HOW MANY allocations preceded it. Two programs therefore stand
 * a chance under this relation only if they allocate the same number of contexts
 * -- see `guard_ref_ops_refutes_left_identity`, where the five laws fail on
 * exactly that count.
 *)
let lemma_pobs_tr_eq_pbind_left (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (x: pval v) (f: pval v -> pcomp v cl)
  : Lemma (ensures pobs_tr_eq lk apply (pbind (PVar x) f) (f x))
  = let c1 = pbind (PVar x) f in
    let c2 = f x in
    introduce forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
                     (tr: list string) (y: pval v).
      (pconverges_tr lk apply ({ st = PStep c1 k; store = sto; next = n0 }) tr y <==>
       pconverges_tr lk apply ({ st = PStep c2 k; store = sto; next = n0 }) tr y)
    with
      (let cf0 : pconf v cl = { st = PStep c1 k; store = sto; next = n0 } in
       let cf1 : pconf v cl =
         { st = PStep (PVar x) (PBindF f :: k); store = sto; next = n0 } in
       let cf2 : pconf v cl = { st = PStep c2 k; store = sto; next = n0 } in
       assert (pstep lk apply cf0 == cf1);
       assert (pstep lk apply cf1 == cf2);
       lemma_pconverges_tr_silent lk apply cf0 tr y;
       lemma_pconverges_tr_silent lk apply cf1 tr y)

(**
 * **A second positive inhabitant, at an ARBITRARY inner computation: splicing
 * nothing is doing nothing.** PROVED, by one silent step.
 *
 * It is worth having beside the left identity because `c` is universally
 * quantified: the relation joins `PSplice [] c` and `c` whatever `c` does --
 * emits, allocates, gets stuck, diverges -- so the positive evidence is not
 * confined to programs whose behaviour is known. It is also the degenerate case
 * of `enter_C` at the empty plan with no owner, which is the shape a law would
 * reduce to if a plan could have no owner; it cannot, so this is a fact about
 * `PSplice` and not about scopes.
 *)
let lemma_pobs_tr_eq_splice_nil (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (c: pcomp v cl)
  : Lemma (ensures pobs_tr_eq lk apply (PSplice [] c) c)
  = introduce forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
                     (tr: list string) (y: pval v).
      (pconverges_tr lk apply ({ st = PStep (PSplice [] c) k; store = sto; next = n0 })
                     tr y <==>
       pconverges_tr lk apply ({ st = PStep c k; store = sto; next = n0 }) tr y)
    with
      (let cf0 : pconf v cl =
         { st = PStep (PSplice [] c) k; store = sto; next = n0 } in
       let cf1 : pconf v cl = { st = PStep c k; store = sto; next = n0 } in
       assert (pstep lk apply cf0 == cf1);
       lemma_pconverges_tr_silent lk apply cf0 tr y)

(* ------------------------------------------------------------------ *)
(*  B2b, SECOND: THE TOOLS FOR A REFUTATION                            *)
(*                                                                     *)
(*  A negative result about `pobs_tr_eq` needs three things and they    *)
(*  are separated here so that a guard below reads as three lines       *)
(*  rather than as a proof. First, a RUN AT A NAMED FUEL is a           *)
(*  convergence -- the fuel occurs in the hypothesis and not in the     *)
(*  conclusion, which is the shape gate condition 3 demands. Second,    *)
(*  a configuration that converges to one value does NOT converge to    *)
(*  another, which is `lemma_pconverges_tr_unique` turned into the      *)
(*  refusal a counterexample needs. Third, one instance of the          *)
(*  ordering's universal is enough to refute it.                        *)
(*                                                                     *)
(*  All three are stated for an arbitrary `v`, `cl`, `lk` and `apply`,  *)
(*  so nothing about them is specific to the fixtures that use them.    *)
(* ------------------------------------------------------------------ *)

(** **A run at a named fuel IS a trace-aware convergence.** PROVED; the witness
    is the fuel. This is `lemma_fconverges_tr` freed of `pload`, because a law's
    quantification ranges over configurations that are not loaded programs. *)
let lemma_pconverges_tr_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (fuel: nat) (tr: list string) (x: pval v)
  : Lemma (requires (fst (prun lk apply fuel cf)).st == PDone x /\
                    snd (prun lk apply fuel cf) == tr)
          (ensures pconverges_tr lk apply cf tr x)
  = introduce exists (n: nat).
        (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr
    with fuel and ()

(** **A configuration that converges to `x1` REFUSES every other value.** PROVED,
    from uniqueness. The refused trace is arbitrary, because uniqueness fixes the
    value from the trace-aware convergence alone -- so a counterexample does not
    have to compute the trace it is refusing. *)
let lemma_pconverges_tr_refuse (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (fuel: nat) (x1: pval v) (tr2: list string) (x2: pval v)
  : Lemma (requires (fst (prun lk apply fuel cf)).st == PDone x1 /\ ~(x1 == x2))
          (ensures ~(pconverges_tr lk apply cf tr2 x2))
  = lemma_pconverges_tr_at lk apply cf fuel (snd (prun lk apply fuel cf)) x1;
    introduce pconverges_tr lk apply cf tr2 x2 ==> False
    with
      lemma_pconverges_tr_unique lk apply cf (snd (prun lk apply fuel cf)) tr2 x1 x2

(** **ONE configuration refutes the ordering.** PROVED, and it is the whole of
    what a counterexample has to supply: a stack, a store, a counter, a trace and
    a value at which the left side converges and the right side does not. *)
let lemma_not_pobs_tr_le (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (c1 c2: pcomp v cl)
    (k: pstack v cl) (sto: pstore v cl) (n0: nat) (tr: list string) (x: pval v)
  : Lemma (requires
             pconverges_tr lk apply ({ st = PStep c1 k; store = sto; next = n0 }) tr x /\
             ~(pconverges_tr lk apply ({ st = PStep c2 k; store = sto; next = n0 })
                             tr x))
          (ensures ~(pobs_tr_le lk apply c1 c2))
  = ()

(** Refuting either ordering refutes the equivalence. PROVED. *)
let lemma_not_pobs_tr_eq (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (c1 c2: pcomp v cl)
  : Lemma (requires ~(pobs_tr_le lk apply c1 c2))
          (ensures ~(pobs_tr_eq lk apply c1 c2))
  = ()

(* ================================================================== *)
(*  B2b.1 -- THE NOMINAL OBSERVATION.  PART 1: THE WORLD LAYER         *)
(*                                                                     *)
(*  THE DEFECT THIS REPAIRS, restated in one sentence: `pobs_tr_le`     *)
(*  fixes the store and the counter at the start and compares a final   *)
(*  `pval v`; `pval v` contains `PCtxKey i`; `palloc` hands out         *)
(*  `cf.next`; so THE NAME OF A FRESHLY ALLOCATED HANDLE IS             *)
(*  OBSERVABLE.  The block comment before the laws and                  *)
(*  `guard_ce_runs_differ` record the consequence: every law's left     *)
(*  side allocates a context and its right side does not, so a          *)
(*  continuation that allocates one of its own reports `PCtxKey 1`      *)
(*  against `PCtxKey 0` -- both traces empty, nothing forged, one       *)
(*  `pstep` from `pload`.                                               *)
(*                                                                     *)
(*  THE REPAIR IS NOT A WEAKENING OF THE TRACE.  Nothing below touches  *)
(*  `prun`, `pstep_tr` or `pconverges_tr`; the trace is still compared  *)
(*  by equality.  What changes is the comparison of the VALUE and of    *)
(*  the STORE: instead of raw equality on `PCtxKey`, a WORLD -- a       *)
(*  finite partial bijection between the two runs' keys -- says which   *)
(*  of the left run's names corresponds to which of the right run's.    *)
(*                                                                     *)
(*  A world is a partial BIJECTION and not merely a partial function.   *)
(*  `pwf_world`'s biconditional IS the aliasing clause: one key to one  *)
(*  partner, distinct keys to distinct partners, in both directions.    *)
(*  `guard_nom_eq_preserves_aliasing` below is that read out at the     *)
(*  value level, and it is what condition 3 asks for.                   *)
(*                                                                     *)
(*  THE ORDER OF THIS FILE IS DELIBERATE.  The NEGATIVE that refutes    *)
(*  the obvious wrong implementation -- re-anchoring, i.e. re-taking    *)
(*  the identity over the current store instead of carrying the         *)
(*  starting world plus one pair per allocation -- is proved BEFORE     *)
(*  any positive result below rests on the discipline it forbids.  It   *)
(*  catches a plausible mistake rather than confirming an intent, so it *)
(*  comes first: `guard_nom_no_reanchoring` and                         *)
(*  `guard_nom_reanchor_pins_the_garbage`.                             *)
(* ================================================================== *)

(** **A world**: a finite partial correspondence between the LEFT run's keys and
    the RIGHT run's.  It is a list and not a function for the same reason
    `pstore` is: the two lookup directions must be things an induction and an
    `assert_norm` can both reach. *)
type pworld = list (nat & nat)

let rec pwlookup_l (i: nat) (w: pworld) : Tot (option nat) (decreases w)
  = match w with
    | [] -> None
    | (a, b) :: r -> if a = i then Some b else pwlookup_l i r

let rec pwlookup_r (j: nat) (w: pworld) : Tot (option nat) (decreases w)
  = match w with
    | [] -> None
    | (a, b) :: r -> if b = j then Some a else pwlookup_r j r

(** One unfolding of each lookup, as a QUANTIFIED fact. The SMT encoding of a
    recursive function on lists does not reach under an outer `forall` on its
    own, and every world proof below needs it to. *)
let lemma_pwl_cons (i j: nat) (w: pworld)
  : Lemma (forall (a: nat).
             pwlookup_l a ((i, j) :: w) == (if i = a then Some j else pwlookup_l a w))
  = ()

let lemma_pwr_cons (i j: nat) (w: pworld)
  : Lemma (forall (b: nat).
             pwlookup_r b ((i, j) :: w) == (if j = b then Some i else pwlookup_r b w))
  = ()

(**
 * **A WORLD IS A PARTIAL BIJECTION**, and the biconditional is the whole of it.
 *
 * `pwlookup_l` is a partial function by construction -- first match wins. The
 * biconditional adds INJECTIVITY and makes the two directions agree, which is
 * exactly "aliasing is preserved": two handles are the same on the left iff
 * their partners are the same on the right.
 *)
let pwf_world (w: pworld) : prop
  = forall (i j: nat). (pwlookup_l i w == Some j) <==> (pwlookup_r j w == Some i)

(** **World extension**: `w'` decides everything `w` decided, and the same way.
    Never "`w'` contains `w` as a sublist" -- the relation is about what the two
    worlds SAY, so that a world may be reordered or rebuilt without breaking
    anything that depended on it. *)
let pwext (w' w: pworld) : prop
  = forall (i j: nat). pwlookup_l i w == Some j ==> pwlookup_l i w' == Some j

let lemma_pwext_refl (w: pworld) : Lemma (pwext w w) = ()

let lemma_pwext_trans (w3 w2 w1: pworld)
  : Lemma (requires pwext w3 w2 /\ pwext w2 w1) (ensures pwext w3 w1) = ()

(** Adding one correspondence, between two keys neither side has spoken for.
    This is the ONLY way any world below grows: one pair, per allocation. *)
let pwextend (i j: nat) (w: pworld) : pworld = (i, j) :: w

let lemma_pwextend_wf (i j: nat) (w: pworld)
  : Lemma (requires pwf_world w /\ pwlookup_l i w == None /\ pwlookup_r j w == None)
          (ensures pwf_world (pwextend i j w) /\ pwext (pwextend i j w) w /\
                   pwlookup_l i (pwextend i j w) == Some j)
  = lemma_pwl_cons i j w; lemma_pwr_cons i j w

(** Every key the world speaks for is below the respective counter. This is what
    makes a freshly allocated key on each side extend the world without
    colliding with anything already in it -- `palloc` hands out `cf.next`, and
    `pwbound` says the world has never mentioned it. *)
let pwbound (w: pworld) (n1 n2: nat) : prop
  = forall (i j: nat). pwlookup_l i w == Some j ==> i < n1 /\ j < n2

let lemma_pwbound_fresh (w: pworld) (n1 n2: nat)
  : Lemma (requires pwf_world w /\ pwbound w n1 n2)
          (ensures pwlookup_l n1 w == None /\ pwlookup_r n2 w == None)
  = ()

(** The dual, for siblings: everything this world speaks about was created at or
    after the two counters. See the sibling section below. *)
let pwabove (w: pworld) (n1 n2: nat) : prop
  = forall (i j: nat). pwlookup_l i w == Some j ==> i >= n1 /\ j >= n2

(* ---- Freshness of a store for a counter --------------------------- *)

(** The counter is fresh for the store, in the form the world layer uses it.
    `pconf_wf` is the same fact stated over `memP`; `lemma_wf_absent` above is
    the bridge, and `lemma_psfresh_of_conf_wf` below is that bridge packaged. *)
let psfresh (#v #cl: Type) (sto: pstore v cl) (n: nat) : prop
  = forall (i: nat). i >= n ==> pstore_lookup i sto == None

let lemma_psfresh_of_conf_wf (#v #cl: Type) (cf: pconf v cl)
  : Lemma (requires pconf_wf cf) (ensures psfresh cf.store cf.next)
  = introduce forall (i: nat). (i >= cf.next ==> pstore_lookup i cf.store == None)
    with (introduce _ ==> _ with lemma_wf_absent i cf.store cf.next)

let lemma_pstore_lookup_cons (#v #cl: Type) (j: nat) (cx: pctx v cl) (sto: pstore v cl)
  : Lemma (forall (i: nat).
             pstore_lookup i ((j, cx) :: sto) ==
               (if j = i then Some cx else pstore_lookup i sto))
  = ()

let lemma_psfresh_alloc (#v #cl: Type) (sto: pstore v cl) (n: nat) (cx: pctx v cl)
  : Lemma (requires psfresh sto n) (ensures psfresh ((n, cx) :: sto) (n + 1))
  = lemma_pstore_lookup_cons n cx sto

(* ---- THE ANCHOR --------------------------------------------------- *)

(**
 * **The anchor**: the identity on the keys the two sides START sharing.
 *
 * `panchor sto` pins every key of `sto` to ITSELF. It is what stops the repair
 * from identifying two distinct handles that were already public when the
 * comparison began: a world extending the anchor cannot send key 0 anywhere but
 * to key 0, because it already says so and `pwext` forbids revision.
 *)
let rec panchor (#v #cl: Type) (sto: pstore v cl) : Tot pworld (decreases sto)
  = match sto with
    | [] -> []
    | (i, _) :: r -> (i, i) :: panchor r

let rec lemma_panchor_l (#v #cl: Type) (i: nat) (sto: pstore v cl)
  : Lemma (ensures pwlookup_l i (panchor sto) ==
                     (if Some? (pstore_lookup i sto) then Some i else None))
          (decreases sto)
  = match sto with
    | [] -> ()
    | (j, _) :: r -> lemma_panchor_l i r

let rec lemma_panchor_r (#v #cl: Type) (j: nat) (sto: pstore v cl)
  : Lemma (ensures pwlookup_r j (panchor sto) ==
                     (if Some? (pstore_lookup j sto) then Some j else None))
          (decreases sto)
  = match sto with
    | [] -> ()
    | (i, _) :: r -> lemma_panchor_r j r

let lemma_panchor_wf (#v #cl: Type) (sto: pstore v cl)
  : Lemma (pwf_world (panchor sto))
  = FStar.Classical.forall_intro_2 (fun (i: nat) (s: pstore v cl) -> lemma_panchor_l i s);
    FStar.Classical.forall_intro_2 (fun (j: nat) (s: pstore v cl) -> lemma_panchor_r j s)

let lemma_panchor_bound (#v #cl: Type) (sto: pstore v cl) (n: nat)
  : Lemma (requires psfresh sto n) (ensures pwbound (panchor sto) n n)
  = FStar.Classical.forall_intro_2 (fun (i: nat) (s: pstore v cl) -> lemma_panchor_l i s)

(** The anchor pins, and pins to the identity. Stated separately because it is
    the fact conditions 2 and 3 are read off. *)
let lemma_panchor_pins (#v #cl: Type) (i: nat) (sto: pstore v cl)
  : Lemma (requires Some? (pstore_lookup i sto))
          (ensures pwlookup_l i (panchor sto) == Some i)
  = lemma_panchor_l i sto

(* ================================================================== *)
(*  THE NEGATIVE, FIRST: RE-ANCHORING IS UNSOUND                       *)
(*                                                                     *)
(*  The obvious implementation of "which names correspond" is to        *)
(*  re-take the identity over the CURRENT store at every step. It is    *)
(*  wrong, and wrong in a direction that no positive result would       *)
(*  reveal: it pins a DISCARDED GARBAGE key as a public name, and a     *)
(*  garbage key is exactly what the two sides of every law differ by.   *)
(*                                                                     *)
(*  These two guards are proved before anything positive rests on the   *)
(*  discipline they forbid.  The concrete instance, at the store the    *)
(*  counterexample's left run actually ends with, is                    *)
(*  `guard_nom_ce_not_a_reanchoring` in the B2b section below.          *)
(* ================================================================== *)

(**
 * **RE-ANCHORING, REFUTED IN GENERAL.** PROVED.
 *
 * If a store holds the key `i` at all, then any world under which the left's
 * `i` corresponds to a DIFFERENT right-hand key fails to extend that store's
 * anchor. So a world carried forward across an allocation the two sides do not
 * share can never be a re-anchoring of the left's store: the two are not merely
 * different, they are incompatible.
 *)
let guard_nom_no_reanchoring (#v #cl: Type) (i j: nat) (sto: pstore v cl) (w: pworld)
  : Lemma (requires Some? (pstore_lookup i sto) /\
                    pwlookup_l i w == Some j /\ ~(i == j))
          (ensures ~(pwext w (panchor sto)))
  = lemma_panchor_pins i sto

(**
 * **AND THE KEY IT WOULD PIN IS THE GARBAGE ONE.** PROVED.
 *
 * A store that has just taken one allocation the other side did not take holds
 * a key `n0` that no public handle names. Re-anchoring pins it -- as a PUBLIC
 * name, mapped to itself -- while the world the run carries is SILENT about it.
 * The two disagree on that key, so the carried world does not extend the
 * re-anchoring: they are not interchangeable bookkeeping.
 *)
let guard_nom_reanchor_pins_the_garbage
      (#v #cl: Type) (sto: pstore v cl) (n0: nat) (cx: pctx v cl) (w: pworld)
  : Lemma (requires psfresh sto n0 /\ pwbound w n0 n0)
          (ensures pwlookup_l n0 (panchor ((n0, cx) :: sto)) == Some n0 /\
                   pwlookup_l n0 w == None /\
                   ~(pwext w (panchor ((n0, cx) :: sto))))
  = lemma_pstore_lookup_cons n0 cx sto;
    lemma_panchor_pins n0 ((n0, cx) :: sto)

(** The anchor GROWS monotonically when the store grows by a fresh entry -- which
    is not licence to USE the grown one: `guard_nom_no_reanchoring` says what
    using it would cost. *)
let lemma_panchor_grows (#v #cl: Type) (sto: pstore v cl) (n0: nat) (cx: pctx v cl)
  : Lemma (requires psfresh sto n0)
          (ensures panchor ((n0, cx) :: sto) == (n0, n0) :: panchor sto /\
                   pwext (panchor ((n0, cx) :: sto)) (panchor sto))
  = introduce forall (i j: nat).
        (pwlookup_l i (panchor sto) == Some j ==>
         pwlookup_l i (panchor ((n0, cx) :: sto)) == Some j)
    with (introduce _ ==> _
          with (lemma_panchor_l i sto;
                lemma_pwl_cons n0 n0 (panchor sto)))

(* ================================================================== *)
(*  VALUES CORRESPOND                                                  *)
(* ================================================================== *)

(**
 * **`pval_rel`.** Payloads must be EQUAL -- the repair does not touch anything
 * a program could compute -- and handles correspond exactly when the world says
 * so. Note what is absent: no clause relates a payload to a handle, and none
 * relates handles the world is silent about. A forged or stale handle is a key
 * no world speaks for, so it is related to nothing, and that is condition 5.
 *)
let pval_rel (#v: Type) (w: pworld) (x1 x2: pval v) : prop
  = match x1, x2 with
    | PV a, PV b -> a == b
    | PCtxKey i, PCtxKey j -> pwlookup_l i w == Some j
    | _, _ -> False

let lemma_pval_rel_mono (#v: Type) (w' w: pworld) (x1 x2: pval v)
  : Lemma (requires pval_rel w x1 x2 /\ pwext w' w) (ensures pval_rel w' x1 x2)
  = match x1 with
    | PV _ -> (match x2 with | PV _ -> () | PCtxKey _ -> ())
    | PCtxKey _ -> (match x2 with | PV _ -> () | PCtxKey _ -> ())

let rec pvals_rel (#v: Type) (w: pworld) (xs1 xs2: list (pval v))
  : Tot prop (decreases xs1)
  = match xs1, xs2 with
    | [], [] -> True
    | a :: r1, b :: r2 -> pval_rel w a b /\ pvals_rel w r1 r2
    | _, _ -> False

let rec lemma_pvals_rel_mono (#v: Type) (w' w: pworld) (xs1 xs2: list (pval v))
  : Lemma (requires pvals_rel w xs1 xs2 /\ pwext w' w)
          (ensures pvals_rel w' xs1 xs2)
          (decreases xs1)
  = match xs1, xs2 with
    | a :: r1, b :: r2 -> lemma_pval_rel_mono w' w a b; lemma_pvals_rel_mono w' w r1 r2
    | _, _ -> ()

(**
 * **ALIASING IS PRESERVED, AT THE VALUE LEVEL.** PROVED, in BOTH directions.
 *
 * Left-to-right is functionality of `pwlookup_l`; the converse is injectivity,
 * and injectivity is exactly what `pwf_world`'s biconditional buys. This is
 * condition 3: the relation admits comparing two handles for equality, because
 * the answer cannot change under renaming.
 *)
let guard_nom_eq_preserves_aliasing (#v: Type) (w: pworld) (a1 a2 b1 b2: pval v)
  : Lemma (requires pwf_world w /\ pval_rel w a1 a2 /\ pval_rel w b1 b2)
          (ensures (a1 == b1) <==> (a2 == b2))
  = match a1, a2, b1, b2 with
    | PCtxKey i1, PCtxKey i2, PCtxKey j1, PCtxKey j2 ->
      assert (pwlookup_l i1 w == Some i2);
      assert (pwlookup_l j1 w == Some j2);
      assert (pwlookup_r i2 w == Some i1);
      assert (pwlookup_r j2 w == Some j1)
    | _, _, _, _ -> ()

(**
 * **TWO DISTINCT LIVE HANDLES ARE NOT COLLAPSED.** PROVED -- condition 2, at
 * the level of the world.
 *
 * If both keys are live in the starting store, the anchor pins each to itself,
 * and a world extending the anchor is a partial FUNCTION, so it cannot also
 * send the first to the second. B1.7's two-contexts-alive fixtures are safe
 * from the repair for this reason and no other.
 *)
let guard_nom_distinct_live_handles (#v #cl: Type)
      (i j: nat) (sto: pstore v cl) (w: pworld)
  : Lemma (requires Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j sto) /\
                    ~(i == j) /\ pwext w (panchor sto))
          (ensures ~(pval_rel #v w (PCtxKey i) (PCtxKey j)))
  = lemma_panchor_pins i sto

(**
 * **A HANDLE NO WORLD SPEAKS FOR IS RELATED TO NOTHING.** PROVED -- condition
 * 5, at the level of the world: there is no fallback to nearness, to numeric
 * proximity, or to anything else. A forged key is simply outside every world's
 * domain, and `pval_rel` has no clause for it.
 *)
let guard_nom_forged_handle_unrelated (#v: Type) (w: pworld) (i: nat) (x2: pval v)
  : Lemma (requires pwlookup_l i w == None)
          (ensures ~(pval_rel #v w (PCtxKey i) x2))
  = match x2 with | PV _ -> () | PCtxKey _ -> ()


(* ================================================================== *)
(*  B2b.1 -- PART 2: THE STEP-INDEXED, WORLD-INDEXED RELATION          *)
(*                                                                     *)
(*  REACHABILITY IS NOT COMPUTABLE HERE, and that is why the relation   *)
(*  has this shape rather than a simpler one.  A stored                 *)
(*  `PCtxRequests x resid post` carries a FUNCTION component            *)
(*  `post: pval v -> pcomp v cl`, and the keys `post` can return cannot *)
(*  be enumerated, so "the set of handles reachable from a public       *)
(*  handle" is not a set this module can compute and quotient by.       *)
(*  Instead relatedness is defined by WHAT THE TWO SIDES PRODUCE: two   *)
(*  computations are related at a world when they take related          *)
(*  arguments to related results AT EVERY FUTURE WORLD, and the world   *)
(*  is extended when a new handle surfaces.                             *)
(*                                                                     *)
(*  THE STEP INDEX is what makes that well founded across the function  *)
(*  components; it is NOT a transition count and never appears in any   *)
(*  statement about a run.  The LEXICOGRAPHIC second component orders   *)
(*  the auxiliary relations ABOVE `pcomp_rel` at the SAME index, which  *)
(*  is what lets a frame, a plan or a context speak about the           *)
(*  computations its function components produce without spending an    *)
(*  index -- exactly the `%[n;0]` / `%[n;1]` arrangement the scratch    *)
(*  model needed for `ctx_rel` over `comp_rel`.  The third component is *)
(*  a list length, for the two list relations, which recurse at their   *)
(*  own level and index.                                               *)
(*                                                                     *)
(*  `cl` IS ABSTRACT, so a clause is related to a clause by a relation  *)
(*  the boundary supplies: `pcl_rel_t`.  It is INDEXED BY THE STEP AND  *)
(*  BY THE WORLD because a clause is an opaque FFI closure in the       *)
(*  shipped machine and may therefore CAPTURE A LIVE HANDLE.  A         *)
(*  same-clause condition -- "the two sides hold the very same `cl`" -- *)
(*  is not merely inconvenient: no handle-capturing clause satisfies    *)
(*  any single-sided condition at all, for the same reason              *)
(*  `guard_nom_capture_not_single_sided` below records.  So `cl_rel` is *)
(*  DATA carried across the boundary, and the two equivariance          *)
(*  conditions are PROPERTIES OF IT.                                    *)
(* ================================================================== *)

(** The clause relation the boundary supplies: step- and world-indexed. *)
let pcl_rel_t (cl: Type) = nat -> pworld -> cl -> cl -> prop

(**
 * **Handler tables correspond when LOOKUP through them corresponds.** The
 * `handlers cl` type is abstract in `Hoop.Runtime.Handlers` and is taken as it
 * ships, so a structural relation on it is not available and would not be
 * wanted: what the machine does with a table is look a clause up in it, and two
 * tables that answer with corresponding clauses are indistinguishable to every
 * transition. The `kind` must agree exactly -- a `KFast` and a `KFull` are
 * dispatched differently, so relating them would be relating clauses that
 * BEHAVE differently.
 *)
let phandlers_rel (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                  (h1 h2: handlers cl) : prop
  = forall (eff op: string).
      (match lookup_handler h1 eff op, lookup_handler h2 eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
       | _, _ -> False)

let ptable_rel (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
               (t1 t2: ptable cl) : prop
  = t1.binds == t2.binds /\ phandlers_rel r n w t1.hs t2.hs

(* ---- The relation proper ------------------------------------------ *)

let rec pcomp_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                  (c1 c2: pcomp v cl)
  : GTot prop (decreases %[n; 0; 0])
  = if n = 0 then True
    else
      match c1, c2 with
      | PVar x1, PVar x2 -> pval_rel w x1 x2
      | POp a1 f1, POp a2 f2 ->
        pcomp_rel r (n - 1) w a1 a2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r (n - 1) w' (f1 y1) (f2 y2))
      | PPerform e1 o1 p1, PPerform e2 o2 p2 ->
        e1 == e2 /\ o1 == o2 /\ pvals_rel w p1 p2
      | PHandle t1 ret1 pv1 b1, PHandle t2 ret2 pv2 b2 ->
        ptable_rel r (n - 1) w t1 t2 /\ pv1 == pv2 /\
        pcomp_rel r (n - 1) w b1 b2 /\
        (match ret1, ret2 with
         | None, None -> True
         | Some g1, Some g2 ->
           (forall (w': pworld) (y1 y2: pval v).
              pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
              pcomp_rel r (n - 1) w' (g1 y1) (g2 y2))
         | _, _ -> False)
      | PSplice fs1 b1, PSplice fs2 b2 ->
        pframes_rel r (n - 1) w fs1 fs2 /\ pcomp_rel r (n - 1) w b1 b2
      | PEmit e1 b1, PEmit e2 b2 ->
        e1 == e2 /\ pcomp_rel r (n - 1) w b1 b2
      | PWeave oe1 oo1 is1 ow1 b1, PWeave oe2 oo2 is2 ow2 b2 ->
        oe1 == oe2 /\ oo1 == oo2 /\ pframes_rel r (n - 1) w is1 is2 /\
        powner_rel r (n - 1) w ow1 ow2 /\ pcomp_rel r (n - 1) w b1 b2
      | PEnterCtx pl1 b1, PEnterCtx pl2 b2 ->
        pplan_rel r (n - 1) w pl1 pl2 /\ pcomp_rel r (n - 1) w b1 b2
      | PExtendC pl1 h1 g1, PExtendC pl2 h2 g2 ->
        pplan_rel r (n - 1) w pl1 pl2 /\ pval_rel w h1 h2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r (n - 1) w' (g1 y1) (g2 y2))
      | PExtendCtxC pl1 h1 g1, PExtendCtxC pl2 h2 g2 ->
        pplan_rel r (n - 1) w pl1 pl2 /\ pval_rel w h1 h2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r (n - 1) w' (g1 y1) (g2 y2))
      | PResumeC pl1 h1 k1, PResumeC pl2 h2 k2 ->
        pplan_rel r (n - 1) w pl1 pl2 /\ pval_rel w h1 h2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r (n - 1) w' (k1 y1) (k2 y2))
      | PNewP l1 i1 b1, PNewP l2 i2 b2 ->
        l1 == l2 /\ pval_rel w i1 i2 /\ pcomp_rel r (n - 1) w b1 b2
      | PReadP l1, PReadP l2 -> l1 == l2
      | PWriteP l1 x1, PWriteP l2 x2 -> l1 == l2 /\ pval_rel w x1 x2
      | _, _ -> False

and powner_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
               (o1 o2: powner v cl)
  : GTot prop (decreases %[n; 1; 0])
  = if n = 0 then True
    else
      match o1, o2 with
      | POwner t1 ret1 pv1, POwner t2 ret2 pv2 ->
        ptable_rel r n w t1 t2 /\ pv1 == pv2 /\
        (match ret1, ret2 with
         | None, None -> True
         | Some g1, Some g2 ->
           (forall (w': pworld) (y1 y2: pval v).
              pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
              pcomp_rel r n w' (g1 y1) (g2 y2))
         | _, _ -> False)

and pframe_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
               (f1 f2: pframe v cl)
  : GTot prop (decreases %[n; 2; 0])
  = if n = 0 then True
    else
      match f1, f2 with
      | PBindF g1, PBindF g2 ->
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r n w' (g1 y1) (g2 y2))
      | PParamF l1 x1, PParamF l2 x2 -> l1 == l2 /\ pval_rel w x1 x2
      | PPromptF t1 ret1 pv1, PPromptF t2 ret2 pv2 ->
        ptable_rel r n w t1 t2 /\ pv1 == pv2 /\
        (match ret1, ret2 with
         | None, None -> True
         | Some g1, Some g2 ->
           (forall (w': pworld) (y1 y2: pval v).
              pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
              pcomp_rel r n w' (g1 y1) (g2 y2))
         | _, _ -> False)
      | PBoundaryF, PBoundaryF -> True
      | PSiteF g1, PSiteF g2 ->
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r n w' (g1 y1) (g2 y2))
      | PModeF m1 g1, PModeF m2 g2 ->
        m1 == m2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r n w' (g1 y1) (g2 y2))
      | PScopeF, PScopeF -> True
      | _, _ -> False

and pitem_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
              (i1 i2: plan_item v cl)
  : GTot prop (decreases %[n; 2; 1])
  = if n = 0 then True
    else
      match i1, i2 with
      | PIBind g1, PIBind g2 ->
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r n w' (g1 y1) (g2 y2))
      | PICell l1 x1, PICell l2 x2 -> l1 == l2 /\ pval_rel w x1 x2
      | PITransparent t1, PITransparent t2 -> ptable_rel r n w t1 t2
      | PIReenter t1 ret1, PIReenter t2 ret2 ->
        ptable_rel r n w t1 t2 /\
        (match ret1, ret2 with
         | None, None -> True
         | Some g1, Some g2 ->
           (forall (w': pworld) (y1 y2: pval v).
              pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
              pcomp_rel r n w' (g1 y1) (g2 y2))
         | _, _ -> False)
      | _, _ -> False

and pframes_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                (fs1 fs2: list (pframe v cl))
  : GTot prop (decreases %[n; 3; length fs1])
  = if n = 0 then True
    else
      match fs1, fs2 with
      | [], [] -> True
      | a1 :: t1, a2 :: t2 -> pframe_rel r n w a1 a2 /\ pframes_rel r n w t1 t2
      | _, _ -> False

and pitems_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
               (is1 is2: list (plan_item v cl))
  : GTot prop (decreases %[n; 3; length is1])
  = if n = 0 then True
    else
      match is1, is2 with
      | [], [] -> True
      | a1 :: t1, a2 :: t2 -> pitem_rel r n w a1 a2 /\ pitems_rel r n w t1 t2
      | _, _ -> False

and pplan_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
              (pl1 pl2: plan v cl)
  : GTot prop (decreases %[n; 4; 0])
  = if n = 0 then True
    else
      match pl1, pl2 with
      | Plan ls1 ow1, Plan ls2 ow2 ->
        pitems_rel r n w ls1 ls2 /\ powner_rel r n w ow1 ow2

(**
 * **CONTEXTS CORRESPOND BY WHAT THEY DO WHEN CONSUMED.** This is the clause
 * condition 4 rests on: two store entries whose contexts behave differently are
 * NOT related, at any world, because `post` must send related arguments to
 * related computations and the residual frames must correspond frame for frame.
 *
 * `PCtxDone` and `PCtxRequests` are kept apart, as they are in the machine. The
 * note on `pctx` records that the two are operationally the same in one
 * degenerate case; relating them would make the relation coarser than the
 * machine and is not done.
 *)
let pctx_rel (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
             (cx1 cx2: pctx v cl)
  : GTot prop
  = if n = 0 then True
    else
      match cx1, cx2 with
      | PCtxDone y1, PCtxDone y2 -> pval_rel w y1 y2
      | PCtxRequests x1 rs1 p1, PCtxRequests x2 rs2 p2 ->
        pval_rel w x1 x2 /\ pframes_rel r n w rs1 rs2 /\
        (forall (w': pworld) (y1 y2: pval v).
           pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel r n w' (p1 y1) (p2 y2))
      | _, _ -> False

(** The intersection of the approximants -- the relations the statements below
    are made of. `pcrel` is over computations, `pxrel` over contexts. *)
let pcrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (c1 c2: pcomp v cl) : GTot prop
  = forall (n: nat). pcomp_rel r n w c1 c2

let pxrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (cx1 cx2: pctx v cl) : GTot prop
  = forall (n: nat). pctx_rel r n w cx1 cx2

let pkrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (k1 k2: pstack v cl) : GTot prop
  = forall (n: nat). pframes_rel r n w k1 k2

(* ================================================================== *)
(*  KRIPKE MONOTONICITY                                                *)
(*                                                                     *)
(*  Every occurrence of `w` in the bodies above is either inside        *)
(*  `pval_rel` (monotone), inside `ptable_rel` (monotone if `r` is), or *)
(*  under a `forall w'` extending `w` (which only weakens as `w`        *)
(*  grows).  So the whole family is monotone, PROVIDED the clause       *)
(*  relation the boundary supplied is -- which is why `pcl_mono` is a   *)
(*  hypothesis and not an assumption.                                   *)
(* ================================================================== *)

let pcl_mono (#cl: Type) (r: pcl_rel_t cl) : prop
  = forall (n: nat) (w' w: pworld) (c1 c2: cl).
      r n w c1 c2 /\ pwext w' w ==> r n w' c1 c2

(** The second admissibility condition on the clause relation itself: downward
    closure in the step index. Like `pcl_mono` it constrains `r` and nothing
    else, so the boundary record carries it. It is needed at index ZERO and
    nowhere else -- `ptable_rel` is the one member of the family that is not
    trivial at `0`, so a table inverted out of a frame (which speaks only from
    index 1 up) has to be pushed down one notch. Both inhabited clause
    relations in this file ignore the index and satisfy it. *)
let pcl_down (#cl: Type) (r: pcl_rel_t cl) : prop
  = forall (n: nat) (w: pworld) (c1 c2: cl). r (n + 1) w c1 c2 ==> r n w c1 c2

let lemma_ptable_rel_mono (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                          (t1 t2: ptable cl)
  : Lemma (requires ptable_rel r n w t1 t2 /\ pwext w' w /\ pcl_mono r)
          (ensures ptable_rel r n w' t1 t2)
  = introduce forall (eff op: string).
        (match lookup_handler t1.hs eff op, lookup_handler t2.hs eff op with
         | None, None -> True
         | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w' f1.body f2.body
         | _, _ -> False)
    with (match lookup_handler t1.hs eff op, lookup_handler t2.hs eff op with
          | Some f1, Some f2 -> assert (r n w f1.body f2.body)
          | _, _ -> ())

let rec lemma_pcomp_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                             (c1 c2: pcomp v cl)
  : Lemma (requires pcomp_rel r n w c1 c2 /\ pwext w' w /\ pcl_mono r)
          (ensures pcomp_rel r n w' c1 c2)
          (decreases %[n; 0; 0])
  = if n = 0 then ()
    else
      match c1, c2 with
      | PVar x1, PVar x2 -> lemma_pval_rel_mono w' w x1 x2
      | POp a1 _, POp a2 _ -> lemma_pcomp_rel_mono r (n - 1) w' w a1 a2
      | PPerform _ _ p1, PPerform _ _ p2 -> lemma_pvals_rel_mono w' w p1 p2
      | PHandle t1 _ _ b1, PHandle t2 _ _ b2 ->
        lemma_ptable_rel_mono r (n - 1) w' w t1 t2;
        lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PSplice fs1 b1, PSplice fs2 b2 ->
        lemma_pframes_rel_mono r (n - 1) w' w fs1 fs2;
        lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PEmit _ b1, PEmit _ b2 -> lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PWeave _ _ is1 ow1 b1, PWeave _ _ is2 ow2 b2 ->
        lemma_pframes_rel_mono r (n - 1) w' w is1 is2;
        lemma_powner_rel_mono r (n - 1) w' w ow1 ow2;
        lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PEnterCtx pl1 b1, PEnterCtx pl2 b2 ->
        lemma_pplan_rel_mono r (n - 1) w' w pl1 pl2;
        lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PExtendC pl1 h1 _, PExtendC pl2 h2 _ ->
        lemma_pplan_rel_mono r (n - 1) w' w pl1 pl2;
        lemma_pval_rel_mono w' w h1 h2
      | PExtendCtxC pl1 h1 _, PExtendCtxC pl2 h2 _ ->
        lemma_pplan_rel_mono r (n - 1) w' w pl1 pl2;
        lemma_pval_rel_mono w' w h1 h2
      | PResumeC pl1 h1 _, PResumeC pl2 h2 _ ->
        lemma_pplan_rel_mono r (n - 1) w' w pl1 pl2;
        lemma_pval_rel_mono w' w h1 h2
      | PNewP _ i1 b1, PNewP _ i2 b2 ->
        lemma_pval_rel_mono w' w i1 i2;
        lemma_pcomp_rel_mono r (n - 1) w' w b1 b2
      | PWriteP _ x1, PWriteP _ x2 -> lemma_pval_rel_mono w' w x1 x2
      | _, _ -> ()

and lemma_powner_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                          (o1 o2: powner v cl)
  : Lemma (requires powner_rel r n w o1 o2 /\ pwext w' w /\ pcl_mono r)
          (ensures powner_rel r n w' o1 o2)
          (decreases %[n; 1; 0])
  = if n = 0 then ()
    else
      match o1, o2 with
      | POwner t1 _ _, POwner t2 _ _ -> lemma_ptable_rel_mono r n w' w t1 t2

and lemma_pframe_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                          (f1 f2: pframe v cl)
  : Lemma (requires pframe_rel r n w f1 f2 /\ pwext w' w /\ pcl_mono r)
          (ensures pframe_rel r n w' f1 f2)
          (decreases %[n; 2; 0])
  = if n = 0 then ()
    else
      match f1, f2 with
      | PParamF _ x1, PParamF _ x2 -> lemma_pval_rel_mono w' w x1 x2
      | PPromptF t1 _ _, PPromptF t2 _ _ -> lemma_ptable_rel_mono r n w' w t1 t2
      | _, _ -> ()

and lemma_pitem_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                         (i1 i2: plan_item v cl)
  : Lemma (requires pitem_rel r n w i1 i2 /\ pwext w' w /\ pcl_mono r)
          (ensures pitem_rel r n w' i1 i2)
          (decreases %[n; 2; 1])
  = if n = 0 then ()
    else
      match i1, i2 with
      | PICell _ x1, PICell _ x2 -> lemma_pval_rel_mono w' w x1 x2
      | PITransparent t1, PITransparent t2 -> lemma_ptable_rel_mono r n w' w t1 t2
      | PIReenter t1 _, PIReenter t2 _ -> lemma_ptable_rel_mono r n w' w t1 t2
      | _, _ -> ()

and lemma_pframes_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                           (fs1 fs2: list (pframe v cl))
  : Lemma (requires pframes_rel r n w fs1 fs2 /\ pwext w' w /\ pcl_mono r)
          (ensures pframes_rel r n w' fs1 fs2)
          (decreases %[n; 3; length fs1])
  = if n = 0 then ()
    else
      match fs1, fs2 with
      | a1 :: t1, a2 :: t2 ->
        lemma_pframe_rel_mono r n w' w a1 a2;
        lemma_pframes_rel_mono r n w' w t1 t2
      | _, _ -> ()

and lemma_pitems_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                          (is1 is2: list (plan_item v cl))
  : Lemma (requires pitems_rel r n w is1 is2 /\ pwext w' w /\ pcl_mono r)
          (ensures pitems_rel r n w' is1 is2)
          (decreases %[n; 3; length is1])
  = if n = 0 then ()
    else
      match is1, is2 with
      | a1 :: t1, a2 :: t2 ->
        lemma_pitem_rel_mono r n w' w a1 a2;
        lemma_pitems_rel_mono r n w' w t1 t2
      | _, _ -> ()

and lemma_pplan_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                         (pl1 pl2: plan v cl)
  : Lemma (requires pplan_rel r n w pl1 pl2 /\ pwext w' w /\ pcl_mono r)
          (ensures pplan_rel r n w' pl1 pl2)
          (decreases %[n; 4; 0])
  = if n = 0 then ()
    else
      match pl1, pl2 with
      | Plan ls1 ow1, Plan ls2 ow2 ->
        lemma_pitems_rel_mono r n w' w ls1 ls2;
        lemma_powner_rel_mono r n w' w ow1 ow2

let lemma_pctx_rel_mono (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w' w: pworld)
                        (cx1 cx2: pctx v cl)
  : Lemma (requires pctx_rel r n w cx1 cx2 /\ pwext w' w /\ pcl_mono r)
          (ensures pctx_rel r n w' cx1 cx2)
  = if n = 0 then ()
    else
      match cx1, cx2 with
      | PCtxDone y1, PCtxDone y2 -> lemma_pval_rel_mono w' w y1 y2
      | PCtxRequests x1 rs1 _, PCtxRequests x2 rs2 _ ->
        lemma_pval_rel_mono w' w x1 x2;
        lemma_pframes_rel_mono r n w' w rs1 rs2
      | _, _ -> ()

let lemma_pcrel_mono (#v #cl: Type) (r: pcl_rel_t cl) (w' w: pworld)
                     (c1 c2: pcomp v cl)
  : Lemma (requires pcrel r w c1 c2 /\ pwext w' w /\ pcl_mono r)
          (ensures pcrel r w' c1 c2)
  = introduce forall (n: nat). pcomp_rel r n w' c1 c2
    with lemma_pcomp_rel_mono r n w' w c1 c2

let lemma_pxrel_mono (#v #cl: Type) (r: pcl_rel_t cl) (w' w: pworld)
                     (cx1 cx2: pctx v cl)
  : Lemma (requires pxrel r w cx1 cx2 /\ pwext w' w /\ pcl_mono r)
          (ensures pxrel r w' cx1 cx2)
  = introduce forall (n: nat). pctx_rel r n w' cx1 cx2
    with lemma_pctx_rel_mono r n w' w cx1 cx2

let lemma_pkrel_mono (#v #cl: Type) (r: pcl_rel_t cl) (w' w: pworld)
                     (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2 /\ pwext w' w /\ pcl_mono r)
          (ensures pkrel r w' k1 k2)
  = introduce forall (n: nat). pframes_rel r n w' k1 k2
    with lemma_pframes_rel_mono r n w' w k1 k2

(* ================================================================== *)
(*  B2b.1 -- PART 3: STORES, AND ANCHOR-RELATIVE EQUIVARIANCE          *)
(* ================================================================== *)

(**
 * **Reading an entry, with a junk default rather than `Some?.v`.**
 *
 * `Some?.v` inside a `prop` typechecks -- the refinement is discharged by the
 * guarding `Some?` -- and then blocks SMT instantiation, because the proof term
 * the projector carries is not something the encoding can produce under a
 * quantifier. The junk is never consulted: every use below is guarded by
 * `Some?`.
 *)
let psget (#v #cl: Type) (i: nat) (sto: pstore v cl) : Tot (pctx v cl)
  = match pstore_lookup i sto with
    | Some cx -> cx
    | None -> PCtxDone (PCtxKey 0)

(**
 * **STORES CORRESPOND ON THE WORLD'S DOMAIN ONLY** -- condition 6.
 *
 * An entry that no public handle names is GARBAGE and is ignored. That is
 * exactly how the two sides of every law are permitted to hold DIFFERENT
 * NUMBERS of contexts: the extra one the left allocated is named by no handle
 * the world speaks for, so `psrel` never looks at it. Note that this is not
 * "small stores are related to large ones": an entry the world DOES name must
 * be present on both sides and the two must be `pxrel`-related.
 *
 * The `{:pattern}` is not decoration. Without it the trigger F* infers fires
 * only when both lookups already occur in the goal, and every store proof below
 * needs to go the other way -- from the world's domain to the two lookups.
 *)
let psrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (s1 s2: pstore v cl) : GTot prop
  = forall (i j: nat). {:pattern (pstore_lookup i s1); (pstore_lookup j s2)}
      pwlookup_l i w == Some j ==>
      (Some? (pstore_lookup i s1) /\ Some? (pstore_lookup j s2) /\
       pxrel r w (psget i s1) (psget j s2))

(* ---- ANCHOR-RELATIVE EQUIVARIANCE --------------------------------- *)

(**
 * **EQUIVARIANCE IS NOT INVARIANCE UNDER EVERY WORLD.  IT IS INVARIANCE UNDER
 * EVERY FUTURE WORLD EXTENDING THE CORRESPONDENCE THE CLOSURE ALREADY OWNS.**
 *
 * `pfn_rel_at w0 f1 f2` is the TWO-SIDED form, and the two-sidedness is
 * essential rather than a generalisation for its own sake: the two runs hold
 * DIFFERENT closures, each having captured the handles ITS OWN run allocated.
 * A one-sided condition -- one closure, related to itself -- cannot even state
 * that situation, and (see `guard_nom_capture_not_single_sided`) is FALSE of
 * every handle-capturing closure there is, so restricting to closures that
 * satisfy it would exclude handle capture outright.
 *
 * `w0` is the PROVENANCE the closure carries. It is not a syntactic mark: one
 * and the same term is equivariant at one anchor and not at another -- that is
 * `guard_nom_capture_vs_guess` below, and it is the discrimination a globally
 * quantified notion cannot make.
 *)
let pfn_rel_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld)
               (f1 f2: pval v -> pcomp v cl) : GTot prop
  = forall (w: pworld) (y1 y2: pval v).
      pwf_world w /\ pwext w w0 /\ pval_rel w y1 y2 ==> pcrel r w (f1 y1) (f2 y2)

(** The same, for a STACK -- which is what the ambient continuation is in this
    machine. `pobs_tr_le` plugs both sides into one arbitrary `k`, so the
    self-relation `pkrel_at w0 k k` is what the observation demands of it. *)
let pkrel_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld) (k1 k2: pstack v cl)
  : GTot prop
  = forall (w: pworld). pwf_world w /\ pwext w w0 ==> pkrel r w k1 k2

let pxrel_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld) (cx1 cx2: pctx v cl)
  : GTot prop
  = forall (w: pworld). pwf_world w /\ pwext w w0 ==> pxrel r w cx1 cx2

let pequivariant_k_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld) (k: pstack v cl)
  : GTot prop
  = pkrel_at r w0 k k

let pequivariant_ctx_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld) (cx: pctx v cl)
  : GTot prop
  = pxrel_at r w0 cx cx

(** A store is equivariant AT ITS OWN ANCHOR: every entry is self-related at
    every future world extending the identity on the store's own keys. *)
let pstore_equivariant_at (#v #cl: Type) (r: pcl_rel_t cl) (sto: pstore v cl)
  : GTot prop
  = forall (i: nat) (cx: pctx v cl).
      pstore_lookup i sto == Some cx ==> pequivariant_ctx_at r (panchor sto) cx

(** **The GLOBAL notion, kept only for comparison.** It quantifies over EVERY
    well-formed world, which is strictly more than the observation ever needs,
    and the excess is not free: it refuses every closure that captured a handle
    along with the ones that guessed a name. It is exactly the EMPTY-ANCHOR
    instance of the corrected notion -- so the correction is a genuine
    RELATIVISATION and not a different predicate. *)
let pequivariant_k (#v #cl: Type) (r: pcl_rel_t cl) (k: pstack v cl) : GTot prop
  = forall (w: pworld). pwf_world w ==> pkrel r w k k

let lemma_pglobal_is_empty_anchor (#v #cl: Type) (r: pcl_rel_t cl) (k: pstack v cl)
  : Lemma (pequivariant_k r k <==> pequivariant_k_at r [] k)
  = ()

(** Anchor-relative equivariance is WEAKER the larger the anchor, so the global
    notion implies every anchor-relative one. *)
let lemma_pglobal_implies_at (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld)
                             (k: pstack v cl)
  : Lemma (requires pequivariant_k r k) (ensures pequivariant_k_at r w0 k)
  = ()

(* ---- Kripke monotonicity of the `_at` forms ------------------------ *)

(** **Equivariance already owned at `w0` is still owned at every world extending
    `w0`.** So carrying a closure forward through allocations never invalidates
    its equivariance, and the hypothesis does not have to be re-established at
    each transition -- which is what makes the discipline "the starting world
    plus one pair per allocation" sufficient. *)
let lemma_pfn_rel_at_mono (#v #cl: Type) (r: pcl_rel_t cl) (w1 w0: pworld)
                          (f1 f2: pval v -> pcomp v cl)
  : Lemma (requires pfn_rel_at r w0 f1 f2 /\ pwext w1 w0)
          (ensures pfn_rel_at r w1 f1 f2)
  = introduce forall (w: pworld) (y1 y2: pval v).
        (pwf_world w /\ pwext w w1 /\ pval_rel w y1 y2 ==> pcrel r w (f1 y1) (f2 y2))
    with (introduce _ ==> _ with lemma_pwext_trans w w1 w0)

let lemma_pkrel_at_mono (#v #cl: Type) (r: pcl_rel_t cl) (w1 w0: pworld)
                        (k1 k2: pstack v cl)
  : Lemma (requires pkrel_at r w0 k1 k2 /\ pwext w1 w0)
          (ensures pkrel_at r w1 k1 k2)
  = introduce forall (w: pworld). (pwf_world w /\ pwext w w1 ==> pkrel r w k1 k2)
    with (introduce _ ==> _ with lemma_pwext_trans w w1 w0)

let lemma_pxrel_at_mono (#v #cl: Type) (r: pcl_rel_t cl) (w1 w0: pworld)
                        (cx1 cx2: pctx v cl)
  : Lemma (requires pxrel_at r w0 cx1 cx2 /\ pwext w1 w0)
          (ensures pxrel_at r w1 cx1 cx2)
  = introduce forall (w: pworld). (pwf_world w /\ pwext w w1 ==> pxrel r w cx1 cx2)
    with (introduce _ ==> _ with lemma_pwext_trans w w1 w0)

(* ---- The store lemmas the observation needs ------------------------ *)

(** An equivariant store is related to itself at its own anchor. PROVED. *)
let lemma_psrel_anchor_at (#v #cl: Type) (r: pcl_rel_t cl) (sto: pstore v cl)
  : Lemma (requires pstore_equivariant_at r sto)
          (ensures psrel r (panchor sto) sto sto)
  = lemma_panchor_wf sto;
    lemma_pwext_refl (panchor sto);
    introduce forall (i j: nat).
        (pwlookup_l i (panchor sto) == Some j ==>
         (Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j sto) /\
          pxrel r (panchor sto) (psget i sto) (psget j sto)))
    with (introduce _ ==> _
          with (lemma_panchor_l i sto;
                match pstore_lookup i sto with
                | Some cx ->
                  assert (j == i);
                  assert (pequivariant_ctx_at r (panchor sto) cx)
                | None -> ()))

(**
 * **THE EXTRA ENTRY ONE SIDE ALLOCATED IS GARBAGE.** PROVED, in both
 * directions: no public handle names it, so it does not appear in the anchor's
 * domain and the two stores are related despite differing in SIZE. This is the
 * fact that makes the counterexample's two runs comparable at all.
 *)
let lemma_psrel_garbage (#v #cl: Type) (r: pcl_rel_t cl) (sto: pstore v cl)
                        (n0: nat) (cx: pctx v cl)
  : Lemma (requires pstore_equivariant_at r sto /\ psfresh sto n0)
          (ensures psrel r (panchor sto) ((n0, cx) :: sto) sto /\
                   psrel r (panchor sto) sto ((n0, cx) :: sto))
  = lemma_psrel_anchor_at r sto;
    lemma_pstore_lookup_cons n0 cx sto;
    introduce forall (i j: nat).
        (pwlookup_l i (panchor sto) == Some j ==>
         (Some? (pstore_lookup i ((n0, cx) :: sto)) /\ Some? (pstore_lookup j sto) /\
          pxrel r (panchor sto) (psget i ((n0, cx) :: sto)) (psget j sto)))
    with (introduce _ ==> _
          with (lemma_panchor_l i sto;
                assert (Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j sto));
                assert (i < n0)));
    introduce forall (i j: nat).
        (pwlookup_l i (panchor sto) == Some j ==>
         (Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j ((n0, cx) :: sto)) /\
          pxrel r (panchor sto) (psget i sto) (psget j ((n0, cx) :: sto))))
    with (introduce _ ==> _
          with (lemma_panchor_l i sto;
                assert (Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j sto));
                assert (j < n0)))

(**
 * **A NEW HANDLE SURFACES ON EACH SIDE: THE WORLD IS EXTENDED BY EXACTLY THAT
 * ONE CORRESPONDENCE.** PROVED.
 *
 * This is the discipline in one lemma: the starting world, plus ONE explicit
 * pair per allocation, and nothing else. Aliasing survives because the
 * extension is a single pair with a fresh key on each side -- `pwbound` is what
 * says both are fresh, and `palloc` hands out exactly `cf.next`.
 *)
let lemma_psrel_alloc (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (s1 s2: pstore v cl) (m1 m2: nat) (cx1 cx2: pctx v cl)
  : Lemma (requires pwf_world w /\ psrel r w s1 s2 /\ pwbound w m1 m2 /\
                    pxrel r w cx1 cx2 /\ pcl_mono r)
          (ensures (let w' = pwextend m1 m2 w in
                    pwf_world w' /\ pwext w' w /\
                    pval_rel #v w' (PCtxKey m1) (PCtxKey m2) /\
                    psrel r w' ((m1, cx1) :: s1) ((m2, cx2) :: s2) /\
                    pwbound w' (m1 + 1) (m2 + 1)))
  = lemma_pwbound_fresh w m1 m2;
    lemma_pwextend_wf m1 m2 w;
    lemma_pwl_cons m1 m2 w;
    lemma_pstore_lookup_cons m1 cx1 s1;
    lemma_pstore_lookup_cons m2 cx2 s2;
    let w' = pwextend m1 m2 w in
    introduce forall (i j: nat).
        (pwlookup_l i w' == Some j ==>
         (Some? (pstore_lookup i ((m1, cx1) :: s1)) /\
          Some? (pstore_lookup j ((m2, cx2) :: s2)) /\
          pxrel r w' (psget i ((m1, cx1) :: s1)) (psget j ((m2, cx2) :: s2))))
    with (introduce _ ==> _
          with (if i = m1
                then begin
                  assert (j == m2);
                  assert (psget i ((m1, cx1) :: s1) == cx1);
                  assert (psget j ((m2, cx2) :: s2) == cx2);
                  lemma_pxrel_mono r w' w cx1 cx2
                end
                else begin
                  assert (pwlookup_l i w == Some j);
                  assert (j < m2);
                  assert (pstore_lookup i ((m1, cx1) :: s1) == pstore_lookup i s1);
                  assert (pstore_lookup j ((m2, cx2) :: s2) == pstore_lookup j s2);
                  assert (psget i ((m1, cx1) :: s1) == psget i s1);
                  assert (psget j ((m2, cx2) :: s2) == psget j s2);
                  assert (pxrel r w (psget i s1) (psget j s2));
                  lemma_pxrel_mono r w' w (psget i s1) (psget j s2)
                end))

(**
 * **THE EXTENSION ADDS EXACTLY ONE LEFT KEY.** PROVED. Every left key the
 * starting world was silent about -- the left run's garbage included -- STAYS
 * silent. This is "no re-anchoring", stated at the transition rather than at
 * the end of a run, and it is the positive counterpart of
 * `guard_nom_no_reanchoring`.
 *)
let guard_nom_alloc_extends_by_one_pair (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
      (s1 s2: pstore v cl) (m1 m2: nat) (cx1 cx2: pctx v cl)
  : Lemma (requires pwf_world w /\ psrel r w s1 s2 /\ pwbound w m1 m2 /\
                    pxrel r w cx1 cx2 /\ pcl_mono r)
          (ensures (let w' = pwextend m1 m2 w in
                    pwf_world w' /\ pwext w' w /\
                    psrel r w' ((m1, cx1) :: s1) ((m2, cx2) :: s2) /\
                    (forall (i: nat). pwlookup_l i w == None /\ ~(i == m1) ==>
                                      pwlookup_l i w' == None)))
  = lemma_psrel_alloc r w s1 s2 m1 m2 cx1 cx2;
    lemma_pwl_cons m1 m2 w

(* ================================================================== *)
(*  SIBLINGS: THE WORLD ALGEBRA                                        *)
(*                                                                     *)
(*  Nesting needs only `pwext`, which is a chain.  Two SIBLING          *)
(*  computations need a JOIN: two extensions of one anchor, chosen      *)
(*  independently, and one world above both.  That join is not always   *)
(*  defined.                                                            *)
(*                                                                     *)
(*  THE CHOICE THIS MODULE MAKES, and why.  `palloc` reads `cf.next`    *)
(*  from the ONE configuration and increments it, and `pstep` threads   *)
(*  that configuration through every rule -- there is no branch of this *)
(*  machine that restores a saved counter.  So the global store and     *)
(*  counter are modelled faithfully, and the natural discipline is the  *)
(*  first of the two the design allows: A SINGLE MONOTONE SUPPLY SHARED *)
(*  BY SIBLINGS.  `lemma_pwcompat_of_ranges` is that discipline's       *)
(*  payoff -- compatibility comes for free, because a later branch      *)
(*  allocates strictly above whatever an earlier one allocated -- and   *)
(*  `guard_nom_fork_no_join` is the check that the alternative, joining *)
(*  two independently chosen worlds after the fact, is NOT available:   *)
(*  two branches that begin at the SAME counter and discard different   *)
(*  amounts produce two worlds NO well-formed world extends.            *)
(* ================================================================== *)

let rec lemma_pwl_append (i: nat) (a b: pworld)
  : Lemma (ensures pwlookup_l i (a @ b) ==
                     (if Some? (pwlookup_l i a) then pwlookup_l i a else pwlookup_l i b))
          (decreases a)
  = match a with
    | [] -> ()
    | (p, q) :: rest -> if p = i then () else lemma_pwl_append i rest b

let rec lemma_pwr_append (j: nat) (a b: pworld)
  : Lemma (ensures pwlookup_r j (a @ b) ==
                     (if Some? (pwlookup_r j a) then pwlookup_r j a else pwlookup_r j b))
          (decreases a)
  = match a with
    | [] -> ()
    | (p, q) :: rest -> if q = j then () else lemma_pwr_append j rest b

(**
 * **COMPATIBILITY.** Two worlds are compatible when they never give one key two
 * different partners -- ON EITHER SIDE. The second clause is not implied by the
 * first: `[(11,10)]` and `[(10,10)]` agree on every LEFT key, their left
 * domains being disjoint, and still cannot be joined, because they disagree
 * about who owns the RIGHT key 10. That asymmetry is exactly the fork trap
 * below, so it gets its own clause.
 *)
let pwcompat (wA wB: pworld) : prop
  = (forall (i j1 j2: nat).
       pwlookup_l i wA == Some j1 /\ pwlookup_l i wB == Some j2 ==> j1 == j2) /\
    (forall (j i1 i2: nat).
       pwlookup_r j wA == Some i1 /\ pwlookup_r j wB == Some i2 ==> i1 == i2)

let pwunion (wA wB: pworld) : pworld = wA @ wB

(** **THE JOIN EXISTS EXACTLY WHEN THE TWO EXTENSIONS ARE COMPATIBLE.** PROVED.
    The union of two compatible well-formed worlds is well formed -- still a
    partial BIJECTION, so no aliasing was collapsed to obtain it -- and extends
    both. *)
let lemma_pwunion_wf (wA wB: pworld)
  : Lemma (requires pwf_world wA /\ pwf_world wB /\ pwcompat wA wB)
          (ensures pwf_world (pwunion wA wB) /\
                   pwext (pwunion wA wB) wA /\ pwext (pwunion wA wB) wB)
  = let w = pwunion wA wB in
    introduce forall (i j: nat).
        (pwlookup_l i w == Some j <==> pwlookup_r j w == Some i)
    with begin
      lemma_pwl_append i wA wB;
      lemma_pwr_append j wA wB;
      (match pwlookup_l i wA, pwlookup_r j wA with
       | Some _, _ -> ()
       | None, Some i' -> assert (pwlookup_l i' wA == Some j)
       | None, None -> ());
      (match pwlookup_r j wA, pwlookup_l i wA with
       | Some _, _ -> ()
       | None, Some j' -> assert (pwlookup_r j' wA == Some i)
       | None, None -> ())
    end;
    introduce forall (i j: nat). (pwlookup_l i wA == Some j ==> pwlookup_l i w == Some j)
    with (introduce _ ==> _ with lemma_pwl_append i wA wB);
    introduce forall (i j: nat). (pwlookup_l i wB == Some j ==> pwlookup_l i w == Some j)
    with (introduce _ ==> _ with lemma_pwl_append i wA wB)

(** **AND COMPATIBILITY IS NECESSARY, NOT MERELY SUFFICIENT.** PROVED. If ANY
    well-formed world extends both, the two were compatible to begin with. So
    `pwcompat` is not a convenient side condition chosen to make a proof go
    through -- it is exactly the reconcilability of two sibling extensions. *)
let lemma_pwcompat_necessary (wA wB w: pworld)
  : Lemma (requires pwf_world wA /\ pwf_world wB /\ pwf_world w /\
                    pwext w wA /\ pwext w wB)
          (ensures pwcompat wA wB)
  = introduce forall (j i1 i2: nat).
        (pwlookup_r j wA == Some i1 /\ pwlookup_r j wB == Some i2 ==> i1 == i2)
    with (introduce _ ==> _
          with begin
            assert (pwlookup_l i1 wA == Some j);
            assert (pwlookup_l i2 wB == Some j);
            assert (pwlookup_l i1 w == Some j);
            assert (pwlookup_l i2 w == Some j);
            assert (pwlookup_r j w == Some i1);
            assert (pwlookup_r j w == Some i2)
          end)

(** **A MONOTONE ALLOCATOR MAKES SIBLINGS COMPATIBLE FOR FREE.** PROVED. If the
    first branch's extension mentions only names below the counters the second
    branch started from, and the second's mentions only names at or above them,
    compatibility holds VACUOUSLY: the two never speak about the same name at
    all, on either side. `lemma_alloc_monotone` is what makes this machine's
    allocator satisfy the hypothesis. *)
let lemma_pwcompat_of_ranges (wA wB: pworld) (n1 n2: nat)
  : Lemma (requires pwf_world wA /\ pwf_world wB /\ pwbound wA n1 n2 /\ pwabove wB n1 n2)
          (ensures pwcompat wA wB)
  = introduce forall (j i1 i2: nat).
        (pwlookup_r j wA == Some i1 /\ pwlookup_r j wB == Some i2 ==> i1 == i2)
    with (introduce _ ==> _
          with begin
            assert (pwlookup_l i1 wA == Some j);
            assert (pwlookup_l i2 wB == Some j)
          end)

(** **TWO SIBLING CLOSURES, ANCHORED AT TWO INDEPENDENT EXTENSIONS OF ONE
    ANCHOR, ARE BOTH USABLE AT THE JOIN.** PROVED, and the proof is monotone
    extension twice: neither closure is re-anchored and neither is re-proved at
    its creation site. *)
let guard_nom_siblings_reconcile (#v #cl: Type) (r: pcl_rel_t cl)
      (w0 wA wB: pworld) (fA1 fA2 fB1 fB2: pval v -> pcomp v cl)
  : Lemma (requires pwf_world wA /\ pwf_world wB /\ pwext wA w0 /\ pwext wB w0 /\
                    pwcompat wA wB /\
                    pfn_rel_at r wA fA1 fA2 /\ pfn_rel_at r wB fB1 fB2)
          (ensures (let w = pwunion wA wB in
                    pwf_world w /\ pwext w w0 /\ pwext w wA /\ pwext w wB /\
                    pfn_rel_at r w fA1 fA2 /\ pfn_rel_at r w fB1 fB2))
  = lemma_pwunion_wf wA wB;
    let w = pwunion wA wB in
    lemma_pwext_trans w wA w0;
    lemma_pfn_rel_at_mono r w wA fA1 fA2;
    lemma_pfn_rel_at_mono r w wB fB1 fB2

(** The two worlds a RESET allocator produces: branch A discards one allocation
    and then allocates the one that matters, so the left's key 11 corresponds to
    the right's 10; branch B, beginning at the SAME counter, must send the
    left's 10 to the right's 10. *)
let pw_fork_A : pworld = [(11, 10)]
let pw_fork_B : pworld = [(10, 10)]

let guard_nom_fork_worlds_are_each_fine ()
  : Lemma (pwf_world pw_fork_A /\ pwf_world pw_fork_B)
  = ()

(**
 * **NO WELL-FORMED WORLD EXTENDS BOTH.** PROVED. The obstruction is not size or
 * freshness: the two branches disagree about WHO OWNS the right-hand name 10,
 * and a world is a bijection, so it cannot hold both opinions. Joining world
 * witnesses after the fact is therefore not a repair -- which is why this
 * module threads one monotone supply instead.
 *)
let guard_nom_fork_no_join (w: pworld)
  : Lemma (requires pwf_world w /\ pwext w pw_fork_A /\ pwext w pw_fork_B)
          (ensures False)
  = assert_norm (pwlookup_l 11 pw_fork_A == Some 10);
    assert_norm (pwlookup_l 10 pw_fork_B == Some 10);
    assert (pwlookup_l 11 w == Some 10);
    assert (pwlookup_l 10 w == Some 10);
    assert (pwlookup_r 10 w == Some 11);
    assert (pwlookup_r 10 w == Some 10)

let guard_nom_fork_incompatible ()
  : Lemma (~(pwcompat pw_fork_A pw_fork_B))
  = introduce pwcompat pw_fork_A pw_fork_B ==> False
    with (lemma_pwunion_wf pw_fork_A pw_fork_B;
          guard_nom_fork_no_join (pwunion pw_fork_A pw_fork_B))

(** **THE CONTRAST, IN ONE STATEMENT.** PROVED. Same two branches, same garbage
    disciplines; the ONLY difference is whether the second branch started from
    the counter the first left behind or from the counter the first started
    from. In the first case the join exists; in the second no join exists at
    all. *)
let pw_fork_B_mono : pworld = [(12, 11)]

let guard_nom_fork_the_contrast ()
  : Lemma (pwcompat pw_fork_A pw_fork_B_mono /\
           pwf_world (pwunion pw_fork_A pw_fork_B_mono) /\
           pwext (pwunion pw_fork_A pw_fork_B_mono) pw_fork_A /\
           pwext (pwunion pw_fork_A pw_fork_B_mono) pw_fork_B_mono /\
           ~(pwcompat pw_fork_A pw_fork_B) /\
           (forall (w: pworld). pwf_world w /\ pwext w pw_fork_A ==>
                                ~(pwext w pw_fork_B)))
  = lemma_pwunion_wf pw_fork_A pw_fork_B_mono;
    guard_nom_fork_incompatible ();
    introduce forall (w: pworld). (pwf_world w /\ pwext w pw_fork_A ==>
                                   ~(pwext w pw_fork_B))
    with (introduce _ ==> _
          with (introduce pwext w pw_fork_B ==> False
                with guard_nom_fork_no_join w))

(* ================================================================== *)
(*  THE BOUNDARY RECORD FOR `cl`                                       *)
(*                                                                     *)
(*  `cl` is abstract here and an OPAQUE FFI CLOSURE in the shipped      *)
(*  machine, so a clause can CAPTURE A LIVE HANDLE.  What crosses the   *)
(*  boundary is therefore a RELATION on clauses -- data -- together     *)
(*  with two PROPERTIES OF IT: that the lookup respects it, and that    *)
(*  the interpreter respects it.  Neither property can be phrased over  *)
(*  ONE clause value: see `guard_nom_capture_not_single_sided`.         *)
(* ================================================================== *)

let pclrel (#cl: Type) (r: pcl_rel_t cl) (w: pworld) (c1 c2: cl) : GTot prop
  = forall (n: nat). r n w c1 c2

(** **The lookup respects the table relation.** Two related tables answer the
    same question with clauses of the same KIND and related bodies, or both
    refuse. This is what lets a transition dispatch on either side and stay in
    the relation. *)
let plookup_equivariant (#cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl) : GTot prop
  = forall (n: nat) (w: pworld) (t1 t2: ptable cl) (eff op: string).
      ptable_rel r n w t1 t2 ==>
      (match lk t1 eff op, lk t2 eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
       | _, _ -> False)

(** **The interpreter respects the clause relation.** Two RELATED clauses --
    which in general are two DIFFERENT values, each having captured what its own
    run allocated -- applied to related payloads and related continuations,
    produce related computations. *)
let papply_equivariant (#v #cl: Type) (r: pcl_rel_t cl) (apply: papply_t v cl)
  : GTot prop
  = forall (w: pworld) (c1 c2: cl) (p1 p2: list (pval v))
           (k1 k2: pval v -> pcomp v cl).
      pwf_world w /\ pclrel r w c1 c2 /\ pvals_rel w p1 p2 /\ pfn_rel_at r w k1 k2 ==>
      pcrel r w (apply c1 p1 k1) (apply c2 p2 k2)

(**
 * **THE BOUNDARY, AS ONE RECORD.** `b_rel` is DATA; `b_mono`, `b_down`,
 * `b_lookup` and `b_apply_eq` are properties OF it, carried as `squash`es so
 * that a boundary is a thing one hands over rather than a set of hypotheses one
 * restates at every use.
 *
 * `b_mono` and `b_down` are admissibility conditions on `b_rel` ALONE -- they
 * mention neither `b_lk` nor `b_apply` -- and the fundamental theorem and the
 * observation corollary derived from it both need them, so both live in the
 * record rather than travelling as loose hypotheses that a future use site
 * could forget.
 *)
noeq
type pboundary (v: Type) (cl: Type) = {
  b_rel: pcl_rel_t cl;
  b_lk: plookup_t cl;
  b_apply: papply_t v cl;
  b_mono: squash (pcl_mono b_rel);
  b_down: squash (pcl_down b_rel);
  b_lookup: squash (plookup_equivariant b_rel b_lk);
  b_apply_eq: squash (papply_equivariant b_rel b_apply);
}

(**
 * **A SINGLE-SIDED CONDITION EXCLUDES HANDLE CAPTURE.** PROVED, and this is why
 * the boundary carries a relation rather than a predicate.
 *
 * Take any closure that returns a handle it captured, `fun _ -> PVar (PCtxKey
 * i)`. The one-sided condition -- the closure related to ITSELF, at every well
 * formed world -- forces the world to pin `i` to itself. But a legal world may
 * send `i` to `i + 1`, and then it does not. So the condition is FALSE of every
 * handle-capturing closure there is: restricting a boundary to closures
 * satisfying it does not merely fail to relate two captures, it throws capture
 * out altogether.
 *
 * The anchor-relative notion admits exactly what the global one refuses:
 * `guard_nom_capture_vs_guess` below is the SAME TERM receiving opposite
 * verdicts at two anchors.
 *)
let pkcap (#v #cl: Type) (i: nat) : pval v -> pcomp v cl
  = fun _ -> PVar (PCtxKey i)

let guard_nom_capture_not_single_sided (#v #cl: Type) (r: pcl_rel_t cl) (i: nat)
  : Lemma (~(pfn_rel_at r ([] <: pworld) (pkcap #v #cl i) (pkcap #v #cl i)))
  = let w : pworld = [(i, i + 1)] in
    assert (pwlookup_l i w == Some (i + 1));
    assert (pwf_world w);
    assert (pval_rel #v w (PCtxKey i) (PCtxKey (i + 1)));
    introduce pfn_rel_at r ([] <: pworld) (pkcap #v #cl i) (pkcap #v #cl i) ==> False
    with begin
      assert (pcrel r w (pkcap #v #cl i (PCtxKey i)) (pkcap #v #cl i (PCtxKey (i + 1))));
      assert (pcomp_rel r 1 w (PVar (PCtxKey #v i)) (PVar (PCtxKey #v i)))
    end

(* ================================================================== *)
(*  B2b.1 -- PART 4: THE NOMINAL OBSERVATION                           *)
(* ================================================================== *)

(**
 * **Convergence to a trace, a value AND A FINAL STORE.**
 *
 * `pconverges_tr` does not expose the store, and the nominal comparison needs
 * it: the two sides are permitted to differ in the number of contexts they
 * hold, and "differ only in garbage" is a statement about the FINAL stores. It
 * is the same existential over `prun` with one more projection read off, so
 * nothing about the run or the trace changes -- `lemma_pnconverges_forget`
 * below proves it implies `pconverges_tr` at the same trace and value.
 *)
let pnconverges (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                (cf: pconf v cl) (tr: list string) (x: pval v) (sto': pstore v cl)
  : GTot prop
  = exists (n: nat).
      (fst (prun lk apply n cf)).st == PDone x /\
      snd (prun lk apply n cf) == tr /\
      (fst (prun lk apply n cf)).store == sto'

let lemma_pnconverges_forget (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (tr: list string) (x: pval v) (sto': pstore v cl)
  : Lemma (requires pnconverges lk apply cf tr x sto')
          (ensures pconverges_tr lk apply cf tr x)
  = eliminate exists (n: nat).
        (fst (prun lk apply n cf)).st == PDone x /\
        snd (prun lk apply n cf) == tr /\
        (fst (prun lk apply n cf)).store == sto'
    with
      (introduce exists (m: nat).
           (fst (prun lk apply m cf)).st == PDone x /\ snd (prun lk apply m cf) == tr
       with n and ())

(** **At most one trace, one value and one store.** PROVED, from
    `lemma_prun_stable` alone and by exactly the argument
    `lemma_pconverges_tr_unique` uses: the smaller witness has already settled,
    so stability carries its whole result -- configuration and trace together --
    forward to the larger. *)
let lemma_pnconverges_unique (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (tr1 tr2: list string) (x1 x2: pval v) (s1 s2: pstore v cl)
  : Lemma (requires pnconverges lk apply cf tr1 x1 s1 /\ pnconverges lk apply cf tr2 x2 s2)
          (ensures tr1 == tr2 /\ x1 == x2 /\ s1 == s2)
  = eliminate exists (n1: nat).
        (fst (prun lk apply n1 cf)).st == PDone x1 /\
        snd (prun lk apply n1 cf) == tr1 /\
        (fst (prun lk apply n1 cf)).store == s1
    with
      (eliminate exists (n2: nat).
           (fst (prun lk apply n2 cf)).st == PDone x2 /\
           snd (prun lk apply n2 cf) == tr2 /\
           (fst (prun lk apply n2 cf)).store == s2
       with
         (if n1 <= n2
          then lemma_prun_stable lk apply n1 (n2 - n1) cf
          else lemma_prun_stable lk apply n2 (n1 - n2) cf))

(** A run at a named fuel IS a nominal convergence. PROVED; the witness is the
    fuel, exactly as in `lemma_pconverges_tr_at`. *)
let lemma_pnconverges_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (cf: pconf v cl) (fuel: nat) (tr: list string) (x: pval v) (sto': pstore v cl)
  : Lemma (requires (fst (prun lk apply fuel cf)).st == PDone x /\
                    snd (prun lk apply fuel cf) == tr /\
                    (fst (prun lk apply fuel cf)).store == sto')
          (ensures pnconverges lk apply cf tr x sto')
  = introduce exists (n: nat).
        (fst (prun lk apply n cf)).st == PDone x /\
        snd (prun lk apply n cf) == tr /\
        (fst (prun lk apply n cf)).store == sto'
    with fuel and ()

(**
 * **THE NOMINAL OBSERVATION.**
 *
 * Read it against `pobs_tr_le`, which it replaces at the value comparison and
 * NOWHERE ELSE:
 *
 *   - both sides still start in the SAME configuration -- same stack, same
 *     store, same counter -- so an implementation still cannot pass by
 *     allocating differently;
 *   - **the trace must still match EXACTLY**, by equality, on the same
 *     `pconverges_tr` machinery. Nothing here weakens it, and
 *     `guard_nom_trace_not_weakened` is the check;
 *   - the two final VALUES correspond under a world `w` instead of being equal;
 *   - `w` EXTENDS `panchor sto`, the identity on the keys both sides already
 *     shared, so a handle that was ALREADY PUBLIC keeps its own name. This is
 *     what stops the repair from identifying two distinct live handles;
 *   - `w` is a partial BIJECTION, so aliasing and the order in which handles
 *     were selected are preserved;
 *   - the two final STORES correspond ON `w`'S DOMAIN ONLY, so entries no
 *     public handle names are garbage and are ignored -- which is how the two
 *     sides may hold different NUMBERS of contexts;
 *   - the counter is not mentioned anywhere, on either side;
 *   - the ambient stack and the initial store are quantified over, but only
 *     among the EQUIVARIANT ones, and the equivariance demanded is
 *     ANCHOR-RELATIVE: only at worlds extending `panchor sto`, the
 *     correspondence the stack and the store already own. A stack that returns
 *     a handle it CAPTURED from the ambient store is admitted; one that returns
 *     a name it GUESSED is not.
 *
 * The step count is NOT mentioned either: each side's is existentially
 * quantified inside `pnconverges`, independently, so no law can acquire a
 * per-law transition offset.
 *)
let pnobs_tr_le (#v #cl: Type) (b: pboundary v cl) (c1 c2: pcomp v cl) : GTot prop
  = forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
           (tr: list string) (x1: pval v) (s1': pstore v cl).
      (pequivariant_k_at b.b_rel (panchor sto) k /\
       pstore_equivariant_at b.b_rel sto /\
       psfresh sto n0 /\
       pnconverges b.b_lk b.b_apply
                   ({ st = PStep c1 k; store = sto; next = n0 }) tr x1 s1') ==>
      (exists (x2: pval v) (s2': pstore v cl) (w: pworld).
         pnconverges b.b_lk b.b_apply
                     ({ st = PStep c2 k; store = sto; next = n0 }) tr x2 s2' /\
         pwf_world w /\ pwext w (panchor sto) /\
         pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2')

let pnobs_tr_eq (#v #cl: Type) (b: pboundary v cl) (c1 c2: pcomp v cl) : GTot prop
  = pnobs_tr_le b c1 c2 /\ pnobs_tr_le b c2 c1

(**
 * **THE TRACE IS NOT WEAKENED.** PROVED, and it is the one thing about this
 * definition that has to be checkable rather than argued: the trace `tr` the
 * antecedent's convergence carries is the SAME `tr` the consequent's
 * convergence must carry, so a right-hand side that emits one event more, one
 * fewer, or the same events in another order does not satisfy the relation
 * however the world is chosen.
 *)
let guard_nom_trace_not_weakened (#v #cl: Type) (b: pboundary v cl)
    (c1 c2: pcomp v cl) (k: pstack v cl) (sto: pstore v cl) (n0: nat)
    (tr1 tr2: list string) (x1 x2: pval v) (s1' s2': pstore v cl)
  : Lemma (requires pnobs_tr_le b c1 c2 /\
                    pequivariant_k_at b.b_rel (panchor sto) k /\
                    pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
                    pnconverges b.b_lk b.b_apply
                                ({ st = PStep c1 k; store = sto; next = n0 })
                                tr1 x1 s1' /\
                    pnconverges b.b_lk b.b_apply
                                ({ st = PStep c2 k; store = sto; next = n0 })
                                tr2 x2 s2')
          (ensures tr1 == tr2)
  = eliminate exists (y2: pval v) (t2: pstore v cl) (w: pworld).
        (pnconverges b.b_lk b.b_apply
                     ({ st = PStep c2 k; store = sto; next = n0 }) tr1 y2 t2 /\
         pwf_world w /\ pwext w (panchor sto) /\
         pval_rel w x1 y2 /\ psrel b.b_rel w s1' t2)
    with
      lemma_pnconverges_unique b.b_lk b.b_apply
        ({ st = PStep c2 k; store = sto; next = n0 }) tr1 tr2 y2 x2 t2 s2'

(**
 * **ONE CONFIGURATION IS ENOUGH TO ESTABLISH AN INSTANCE.** The shape a
 * positive result takes: at a given equivariant stack and store, exhibit the
 * right-hand run and the world. Nothing else has to be supplied -- in
 * particular no step count, since `pnconverges` hides both sides' independently.
 *)
let lemma_pnobs_at (#v #cl: Type) (b: pboundary v cl) (c1 c2: pcomp v cl)
    (k: pstack v cl) (sto: pstore v cl) (n0: nat)
    (tr: list string) (x1 x2: pval v) (s1' s2': pstore v cl) (w: pworld)
  : Lemma (requires pnconverges b.b_lk b.b_apply
                                ({ st = PStep c2 k; store = sto; next = n0 })
                                tr x2 s2' /\
                    pwf_world w /\ pwext w (panchor sto) /\
                    pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2')
          (ensures (exists (y2: pval v) (t2: pstore v cl) (ww: pworld).
                      pnconverges b.b_lk b.b_apply
                                  ({ st = PStep c2 k; store = sto; next = n0 })
                                  tr y2 t2 /\
                      pwf_world ww /\ pwext ww (panchor sto) /\
                      pval_rel ww x1 y2 /\ psrel b.b_rel ww s1' t2))
  = introduce exists (y2: pval v) (t2: pstore v cl) (ww: pworld).
        (pnconverges b.b_lk b.b_apply
                     ({ st = PStep c2 k; store = sto; next = n0 }) tr y2 t2 /\
         pwf_world ww /\ pwext ww (panchor sto) /\
         pval_rel ww x1 y2 /\ psrel b.b_rel ww s1' t2)
    with x2 s2' w and ()

(* ================================================================== *)
(*  B2b.2 -- THE FUNDAMENTAL THEOREM                                   *)
(*                                                                     *)
(*  WHAT B2b.1 LEFT, IN ONE SENTENCE.  It proved the repaired           *)
(*  relation's consequent for the former counterexamples at ONE         *)
(*  CONCRETE CONFIGURATION EACH, with hand-written witnesses: the       *)
(*  right-hand run by `assert_norm`, the world written down as a        *)
(*  literal, the store correspondence checked entry by entry.  What it  *)
(*  did not prove is `pnobs_tr_le`, whose universal quantification over *)
(*  EVERY equivariant ambient stack and EVERY equivariant initial store *)
(*  cannot be reached that way.  Reaching it needs a simulation over    *)
(*  `pstep` for the whole machine, and that is what this section is.    *)
(*                                                                     *)
(*  THE SHAPE, in two theorems and nothing else:                        *)
(*                                                                     *)
(*    - `lemma_pstep_tr_compat` -- ONE STEP.  Two configurations        *)
(*      related at `w` step to two configurations related at a world    *)
(*      EXTENDING `w`, emitting the SAME event list.  It is a case      *)
(*      analysis on the node, dispatched to one lemma per rule.         *)
(*                                                                     *)
(*    - `lemma_prun_compat` -- THE RUN.  The same, for `prun` at any    *)
(*      fuel, by induction on the fuel.                                 *)
(*                                                                     *)
(*  and then `lemma_pnobs_tr_le_of_crel`, which is the observation      *)
(*  read off the second: two computations related at every well-formed  *)
(*  world satisfy `pnobs_tr_le`, at every equivariant stack and store   *)
(*  the definition quantifies over.                                     *)
(*                                                                     *)
(*  WHAT THE THEOREM DOES NOT DO, and each is a constraint an earlier   *)
(*  gate established rather than a preference:                          *)
(*                                                                     *)
(*    - IT NEVER RE-ANCHORS.  The world handed back is a `pwext` of the *)
(*      world handed in, built from it by ONE `pwextend` per `palloc`   *)
(*      and by nothing else.  Nothing is ever computed from a final     *)
(*      store; `guard_nom_no_reanchoring` says what that would cost.    *)
(*                                                                     *)
(*    - IT RELATES NO TRANSITION COUNTS.  Both sides are run at the     *)
(*      SAME fuel and the induction is on that fuel, so no `+3` and no  *)
(*      per-rule offset can appear anywhere.  The counts stay           *)
(*      existentially quantified inside `pnconverges`, independently on *)
(*      each side, exactly as B2b.1 left them.                          *)
(*                                                                     *)
(*    - IT IS NEVER STATED OVER `fapply`.  The two theorems take an     *)
(*      ARBITRARY clause relation, lookup and interpreter satisfying    *)
(*      the conditions a `pboundary` carries, and the observation       *)
(*      corollary takes an ARBITRARY `pboundary`.                       *)
(*      `fapply` is PROVED not equivariant, and neither                 *)
(*      equivariance nor `fapply` is bent to accommodate that: the      *)
(*      counterexample corollary below runs the two programs under a    *)
(*      DIFFERENT interpreter and checks -- by running both machines -- *)
(*      that the runs are literally the same, which they are because    *)
(*      neither performs an operation.                                  *)
(*                                                                     *)
(*  ONE HYPOTHESIS IS NEW, AND `pboundary` NOW CARRIES IT:              *)
(*  `pcl_down`, downward closure of the clause relation in the step     *)
(*  index.  It is needed at index ZERO and nowhere else -- `ptable_rel` *)
(*  is the one member of the family that is not trivially true there,   *)
(*  so a table inverted out of a frame, which speaks only from index 1  *)
(*  up, has to be pushed down one notch.  Both clause relations this    *)
(*  file inhabits ignore the index and satisfy it.                      *)
(*                                                                     *)
(*  It is a field, `b_down`, and not a loose hypothesis, for the same   *)
(*  reason `b_mono` is: it constrains the RELATION alone, mentioning    *)
(*  neither the lookup nor the interpreter, and both the fundamental    *)
(*  theorem and the observation corollary need it.  Outside the record  *)
(*  it could be forgotten at a use site; inside it, a caller holding a  *)
(*  boundary can apply the theorem with nothing further to discharge.   *)
(*  It adds no trusted assumption: it is PROVED of both `fcl_rel` and   *)
(*  `ncl_rel`.                                                          *)
(*                                                                     *)
(*  The lemmas stated at a BARE relation -- `lemma_pstep_tr_compat`,    *)
(*  `lemma_prun_compat` -- keep `pcl_down r` as an explicit hypothesis. *)
(*  They are deliberately not stated at a `pboundary`, so that the two  *)
(*  transition theorems can be read, and used, without one.             *)
(*                                                                     *)
(*  TWO PROOF-ENGINEERING FACTS THAT COST HOURS AND ARE RECORDED SO     *)
(*  THEY NEED NOT COST THEM AGAIN.                                      *)
(*                                                                     *)
(*    1. A `GTot prop` DEFINITION IS AN ATOM IN A HYPOTHESIS.  A GOAL   *)
(*       mentioning `psrel r w s1 s2` unfolds; a HYPOTHESIS mentioning  *)
(*       it does not, and the quantifier inside it -- `{:pattern}` and  *)
(*       all -- is invisible to the solver.  The `_unfold` casts below  *)
(*       are the remedy, and they are accepted BY CONVERSION with no    *)
(*       proof obligation whatever.                                     *)
(*                                                                     *)
(*    2. `plookup_equivariant` AND `papply_equivariant` HAVE NO USABLE  *)
(*       INFERRED TRIGGER.  Every use fails with `incomplete            *)
(*       quantifiers`, at any fuel and any rlimit.  Neither definition  *)
(*       is touched: `plookup_eq_p` and `papply_eq_p` are the same      *)
(*       propositions with an explicit `{:pattern}`, and the casts into *)
(*       them are conversions.                                          *)
(*                                                                     *)
(*  NOTHING IN THIS SECTION RAISES `rlimit` OR ADDS A `#push-options`.  *)
(* ================================================================== *)


(* ================================================================== *)
(*  THE TWO BOUNDARY CONDITIONS, WITH A TRIGGER                        *)
(*                                                                     *)
(*  `plookup_equivariant` and `papply_equivariant` quantify over        *)
(*  variables that occur only under a `match` scrutinee or only inside  *)
(*  an auxiliary relation, and the trigger F* infers for such a         *)
(*  quantifier never fires: every attempt to USE either condition       *)
(*  fails with `incomplete quantifiers`, at any fuel and any rlimit.    *)
(*  Neither definition is touched.  What is added is the SAME           *)
(*  proposition carrying an explicit `{:pattern}`, together with a cast *)
(*  from the original -- and the cast is accepted BY CONVERSION, with   *)
(*  no proof obligation at all, because a pattern is an annotation on   *)
(*  a quantifier and not a change to it.                                *)
(* ================================================================== *)

let plookup_eq_p (#cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl) : GTot prop
  = forall (n: nat) (w: pworld) (t1 t2: ptable cl) (eff op: string).
      {:pattern (lk t1 eff op); (lk t2 eff op); (ptable_rel r n w t1 t2)}
      ptable_rel r n w t1 t2 ==>
      (match lk t1 eff op, lk t2 eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
       | _, _ -> False)

let lk_patterned (#cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                 (h: squash (plookup_equivariant r lk))
  : squash (plookup_eq_p r lk)
  = h

let papply_eq_p (#v #cl: Type) (r: pcl_rel_t cl) (apply: papply_t v cl) : GTot prop
  = forall (w: pworld) (c1 c2: cl) (p1 p2: list (pval v))
           (k1 k2: pval v -> pcomp v cl).
      {:pattern (apply c1 p1 k1); (apply c2 p2 k2); (pclrel r w c1 c2)}
      pwf_world w /\ pclrel r w c1 c2 /\ pvals_rel w p1 p2 /\ pfn_rel_at r w k1 k2 ==>
      pcrel r w (apply c1 p1 k1) (apply c2 p2 k2)

let apply_patterned (#v #cl: Type) (r: pcl_rel_t cl) (apply: papply_t v cl)
                    (h: squash (papply_equivariant r apply))
  : squash (papply_eq_p r apply)
  = h

(* ---- index-free wrappers ------------------------------------------ *)

let ptrel (#cl: Type) (r: pcl_rel_t cl) (w: pworld) (t1 t2: ptable cl) : GTot prop
  = forall (n: nat). ptable_rel r n w t1 t2

let pfrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (f1 f2: pframe v cl) : GTot prop
  = forall (n: nat). pframe_rel r n w f1 f2

let pirel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (i1 i2: plan_item v cl) : GTot prop
  = forall (n: nat). pitem_rel r n w i1 i2

let plsrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
           (is1 is2: list (plan_item v cl)) : GTot prop
  = forall (n: nat). pitems_rel r n w is1 is2

let porel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (o1 o2: powner v cl) : GTot prop
  = forall (n: nat). powner_rel r n w o1 o2

let pplrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (pl1 pl2: plan v cl) : GTot prop
  = forall (n: nat). pplan_rel r n w pl1 pl2

(* ---- stacks: nil and cons ----------------------------------------- *)

let lemma_pkrel_nil (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
  : Lemma (pkrel r w ([] <: pstack v cl) ([] <: pstack v cl))
  = introduce forall (n: nat). pframes_rel r n w ([] <: pstack v cl) ([] <: pstack v cl)
    with ()

let lemma_pkrel_cons (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (f1 f2: pframe v cl) (k1 k2: pstack v cl)
  : Lemma (requires pfrel r w f1 f2 /\ pkrel r w k1 k2)
          (ensures pkrel r w (f1 :: k1) (f2 :: k2))
  = introduce forall (n: nat). pframes_rel r n w (f1 :: k1) (f2 :: k2)
    with (if n = 0 then () else (assert (pframe_rel r n w f1 f2);
                                 assert (pframes_rel r n w k1 k2)))

let lemma_pkrel_cons_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (f1 f2: pframe v cl) (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w (f1 :: k1) (f2 :: k2))
          (ensures pfrel r w f1 f2 /\ pkrel r w k1 k2)
  = introduce forall (n: nat). pframe_rel r n w f1 f2
    with (if n = 0 then () else assert (pframes_rel r n w (f1 :: k1) (f2 :: k2)));
    introduce forall (n: nat). pframes_rel r n w k1 k2
    with (if n = 0 then () else assert (pframes_rel r n w (f1 :: k1) (f2 :: k2)))

(** Related stacks have the same shape: nil against cons is not related. *)
let lemma_pkrel_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2)
          (ensures Nil? k1 == Nil? k2)
  = assert (pframes_rel r 1 w k1 k2)

let rec lemma_pkrel_append (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (a1 a2 b1 b2: pstack v cl)
  : Lemma (requires pkrel r w a1 a2 /\ pkrel r w b1 b2)
          (ensures pkrel r w (a1 @ b1) (a2 @ b2))
          (decreases a1)
  = match a1, a2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      lemma_pkrel_append r w t1 t2 b1 b2;
      lemma_pkrel_cons r w f1 f2 (t1 @ b1) (t2 @ b2)
    | _, _ -> lemma_pkrel_shape r w a1 a2

(** `ptable_rel` inherits the clause relation's downward closure. PROVED, and it
    is the only place index 0 is ever reached from above. *)
let lemma_ptable_rel_down (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                          (t1 t2: ptable cl)
  : Lemma (requires ptable_rel r (n + 1) w t1 t2 /\ pcl_down r)
          (ensures ptable_rel r n w t1 t2)
  = introduce forall (eff op: string).
        (match lookup_handler t1.hs eff op, lookup_handler t2.hs eff op with
         | None, None -> True
         | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
         | _, _ -> False)
    with (match lookup_handler t1.hs eff op, lookup_handler t2.hs eff op with
          | Some f1, Some f2 -> assert (r (n + 1) w f1.body f2.body)
          | _, _ -> ())

(* ---- return clauses ------------------------------------------------ *)

let pretrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
            (ret1 ret2: option (pval v -> pcomp v cl)) : GTot prop
  = match ret1, ret2 with
    | None, None -> True
    | Some g1, Some g2 -> pfn_rel_at r w g1 g2
    | _, _ -> False

(* ---- frames, constructed and inverted ------------------------------ *)

let lemma_pfrel_bind (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfn_rel_at r w g1 g2)
          (ensures pfrel r w (PBindF g1) (PBindF g2))
  = introduce forall (n: nat). pframe_rel r n w (PBindF g1) (PBindF g2)
    with (if n = 0 then ()
          else introduce forall (w': pworld) (y1 y2: pval v).
                   (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                    pcomp_rel r n w' (g1 y1) (g2 y2))
               with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2))))

let lemma_pfrel_bind_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfrel r w (PBindF g1) (PBindF g2))
          (ensures pfn_rel_at r w g1 g2)
  = introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with (if n = 0 then ()
                     else assert (pframe_rel r n w (PBindF g1) (PBindF g2))))

let lemma_pfrel_site (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfn_rel_at r w g1 g2)
          (ensures pfrel r w (PSiteF g1) (PSiteF g2))
  = introduce forall (n: nat). pframe_rel r n w (PSiteF g1) (PSiteF g2)
    with (if n = 0 then ()
          else introduce forall (w': pworld) (y1 y2: pval v).
                   (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                    pcomp_rel r n w' (g1 y1) (g2 y2))
               with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2))))

let lemma_pfrel_site_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfrel r w (PSiteF g1) (PSiteF g2))
          (ensures pfn_rel_at r w g1 g2)
  = introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with (if n = 0 then ()
                     else assert (pframe_rel r n w (PSiteF g1) (PSiteF g2))))

let lemma_pfrel_mode (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (m: weave_mode) (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfn_rel_at r w g1 g2)
          (ensures pfrel r w (PModeF m g1) (PModeF m g2))
  = introduce forall (n: nat). pframe_rel r n w (PModeF m g1) (PModeF m g2)
    with (if n = 0 then ()
          else introduce forall (w': pworld) (y1 y2: pval v).
                   (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                    pcomp_rel r n w' (g1 y1) (g2 y2))
               with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2))))

let lemma_pfrel_mode_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (m1 m2: weave_mode) (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfrel r w (PModeF m1 g1) (PModeF m2 g2))
          (ensures m1 == m2 /\ pfn_rel_at r w g1 g2)
  = assert (pframe_rel r 1 w (PModeF m1 g1) (PModeF m2 g2));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with (if n = 0 then ()
                     else assert (pframe_rel r n w (PModeF m1 g1) (PModeF m2 g2))))

let lemma_pfrel_param (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (l: string) (x1 x2: pval v)
  : Lemma (requires pval_rel w x1 x2)
          (ensures pfrel #v #cl r w (PParamF l x1) (PParamF l x2))
  = introduce forall (n: nat). pframe_rel #v #cl r n w (PParamF l x1) (PParamF l x2)
    with ()

let lemma_pfrel_param_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                          (l1 l2: string) (x1 x2: pval v)
  : Lemma (requires pfrel #v #cl r w (PParamF l1 x1) (PParamF l2 x2))
          (ensures l1 == l2 /\ pval_rel w x1 x2)
  = assert (pframe_rel #v #cl r 1 w (PParamF l1 x1) (PParamF l2 x2))

let lemma_pfrel_prompt (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                       (pv: prompt_provenance)
  : Lemma (requires ptrel r w t1 t2 /\ pretrel r w ret1 ret2)
          (ensures pfrel r w (PPromptF t1 ret1 pv) (PPromptF t2 ret2 pv))
  = introduce forall (n: nat). pframe_rel r n w (PPromptF t1 ret1 pv) (PPromptF t2 ret2 pv)
    with (if n = 0 then ()
          else begin
            assert (ptable_rel r n w t1 t2);
            match ret1, ret2 with
            | Some g1, Some g2 ->
              introduce forall (w': pworld) (y1 y2: pval v).
                  (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                   pcomp_rel r n w' (g1 y1) (g2 y2))
              with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2)))
            | _, _ -> ()
          end)

let lemma_pfrel_prompt_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                           (pv1 pv2: prompt_provenance)
  : Lemma (requires pfrel r w (PPromptF t1 ret1 pv1) (PPromptF t2 ret2 pv2) /\ pcl_down r)
          (ensures ptrel r w t1 t2 /\ pretrel r w ret1 ret2 /\ pv1 == pv2)
  = assert (pframe_rel r 1 w (PPromptF t1 ret1 pv1) (PPromptF t2 ret2 pv2));
    assert (ptable_rel r 1 w t1 t2);
    introduce forall (n: nat). ptable_rel r n w t1 t2
    with (if n = 0
          then lemma_ptable_rel_down r 0 w t1 t2
          else assert (pframe_rel r n w (PPromptF t1 ret1 pv1) (PPromptF t2 ret2 pv2)));
    match ret1, ret2 with
    | Some g1, Some g2 ->
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
      with (introduce _ ==> _
            with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
                 with (if n = 0 then ()
                       else assert (pframe_rel r n w (PPromptF t1 ret1 pv1)
                                                     (PPromptF t2 ret2 pv2))))
    | _, _ -> ()

let lemma_pfrel_boundary (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
  : Lemma (pfrel #v #cl r w PBoundaryF PBoundaryF)
  = introduce forall (n: nat). pframe_rel #v #cl r n w PBoundaryF PBoundaryF with ()

let lemma_pfrel_scope (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
  : Lemma (pfrel #v #cl r w PScopeF PScopeF)
  = introduce forall (n: nat). pframe_rel #v #cl r n w PScopeF PScopeF with ()

(* ---- computations: the shape, and the components ------------------- *)

(** Related computations are the SAME NODE. Read off index 1, where every
    mismatched pair is `False`. *)
let lemma_pcrel_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (c1 c2: pcomp v cl)
  : Lemma (requires pcrel r w c1 c2) (ensures pcomp_rel r 1 w c1 c2)
  = ()

let lemma_pcrel_var (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (x1 x2: pval v)
  : Lemma (requires pval_rel w x1 x2)
          (ensures pcrel #v #cl r w (PVar x1) (PVar x2))
  = introduce forall (n: nat). pcomp_rel #v #cl r n w (PVar x1) (PVar x2) with ()

let lemma_pcrel_var_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (x1 x2: pval v)
  : Lemma (requires pcrel #v #cl r w (PVar x1) (PVar x2))
          (ensures pval_rel w x1 x2)
  = assert (pcomp_rel #v #cl r 1 w (PVar x1) (PVar x2))

let lemma_pcrel_op_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (a1 a2: pcomp v cl) (f1 f2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w (POp a1 f1) (POp a2 f2))
          (ensures pcrel r w a1 a2 /\ pfn_rel_at r w f1 f2)
  = introduce forall (n: nat). pcomp_rel r n w a1 a2
    with assert (pcomp_rel r (n + 1) w (POp a1 f1) (POp a2 f2));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (f1 y1) (f2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (f1 y1) (f2 y2)
               with assert (pcomp_rel r (n + 1) w (POp a1 f1) (POp a2 f2)))

let lemma_pcrel_perform_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                            (e1 o1 e2 o2: string) (p1 p2: list (pval v))
  : Lemma (requires pcrel #v #cl r w (PPerform e1 o1 p1) (PPerform e2 o2 p2))
          (ensures e1 == e2 /\ o1 == o2 /\ pvals_rel w p1 p2)
  = assert (pcomp_rel #v #cl r 1 w (PPerform e1 o1 p1) (PPerform e2 o2 p2))

let lemma_pcrel_handle_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                           (pv1 pv2: prompt_provenance) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2))
          (ensures ptrel r w t1 t2 /\ pv1 == pv2 /\ pcrel r w b1 b2 /\
                   pretrel r w ret1 ret2)
  = assert (pcomp_rel r 1 w (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2));
    introduce forall (n: nat). ptable_rel r n w t1 t2
    with assert (pcomp_rel r (n + 1) w (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2));
    match ret1, ret2 with
    | Some g1, Some g2 ->
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
      with (introduce _ ==> _
            with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
                 with assert (pcomp_rel r (n + 1) w
                                (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2)))
    | _, _ -> ()

let lemma_pcrel_splice (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (fs1 fs2: pstack v cl) (b1 b2: pcomp v cl)
  : Lemma (requires pkrel r w fs1 fs2 /\ pcrel r w b1 b2)
          (ensures pcrel r w (PSplice fs1 b1) (PSplice fs2 b2))
  = introduce forall (n: nat). pcomp_rel r n w (PSplice fs1 b1) (PSplice fs2 b2)
    with (if n = 0 then ()
          else (assert (pframes_rel r (n - 1) w fs1 fs2);
                assert (pcomp_rel r (n - 1) w b1 b2)))

let lemma_pcrel_splice_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (fs1 fs2: pstack v cl) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PSplice fs1 b1) (PSplice fs2 b2))
          (ensures pkrel r w fs1 fs2 /\ pcrel r w b1 b2)
  = introduce forall (n: nat). pframes_rel r n w fs1 fs2
    with assert (pcomp_rel r (n + 1) w (PSplice fs1 b1) (PSplice fs2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PSplice fs1 b1) (PSplice fs2 b2))

let lemma_pcrel_emit_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (e1 e2: string) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PEmit e1 b1) (PEmit e2 b2))
          (ensures e1 == e2 /\ pcrel r w b1 b2)
  = assert (pcomp_rel r 1 w (PEmit e1 b1) (PEmit e2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PEmit e1 b1) (PEmit e2 b2))

let lemma_pcrel_weave_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                          (e1 o1 e2 o2: string) (is1 is2: pstack v cl)
                          (ow1 ow2: powner v cl) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2))
          (ensures e1 == e2 /\ o1 == o2 /\ pkrel r w is1 is2 /\ porel r w ow1 ow2 /\
                   pcrel r w b1 b2)
  = assert (pcomp_rel r 1 w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2));
    introduce forall (n: nat). pframes_rel r n w is1 is2
    with assert (pcomp_rel r (n + 1) w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2));
    introduce forall (n: nat). powner_rel r n w ow1 ow2
    with assert (pcomp_rel r (n + 1) w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2))

let lemma_pcrel_enterctx_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                             (pl1 pl2: plan v cl) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PEnterCtx pl1 b1) (PEnterCtx pl2 b2))
          (ensures pplrel r w pl1 pl2 /\ pcrel r w b1 b2)
  = introduce forall (n: nat). pplan_rel r n w pl1 pl2
    with assert (pcomp_rel r (n + 1) w (PEnterCtx pl1 b1) (PEnterCtx pl2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PEnterCtx pl1 b1) (PEnterCtx pl2 b2))

let lemma_pcrel_extendc_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                            (pl1 pl2: plan v cl) (h1 h2: pval v)
                            (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w (PExtendC pl1 h1 g1) (PExtendC pl2 h2 g2))
          (ensures pplrel r w pl1 pl2 /\ pval_rel w h1 h2 /\ pfn_rel_at r w g1 g2)
  = assert (pcomp_rel r 1 w (PExtendC pl1 h1 g1) (PExtendC pl2 h2 g2));
    introduce forall (n: nat). pplan_rel r n w pl1 pl2
    with assert (pcomp_rel r (n + 1) w (PExtendC pl1 h1 g1) (PExtendC pl2 h2 g2));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with assert (pcomp_rel r (n + 1) w (PExtendC pl1 h1 g1) (PExtendC pl2 h2 g2)))

let lemma_pcrel_extendctxc_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                               (pl1 pl2: plan v cl) (h1 h2: pval v)
                               (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w (PExtendCtxC pl1 h1 g1) (PExtendCtxC pl2 h2 g2))
          (ensures pplrel r w pl1 pl2 /\ pval_rel w h1 h2 /\ pfn_rel_at r w g1 g2)
  = assert (pcomp_rel r 1 w (PExtendCtxC pl1 h1 g1) (PExtendCtxC pl2 h2 g2));
    introduce forall (n: nat). pplan_rel r n w pl1 pl2
    with assert (pcomp_rel r (n + 1) w (PExtendCtxC pl1 h1 g1) (PExtendCtxC pl2 h2 g2));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with assert (pcomp_rel r (n + 1) w
                              (PExtendCtxC pl1 h1 g1) (PExtendCtxC pl2 h2 g2)))

let lemma_pcrel_resumec_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                            (pl1 pl2: plan v cl) (h1 h2: pval v)
                            (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w (PResumeC pl1 h1 g1) (PResumeC pl2 h2 g2))
          (ensures pplrel r w pl1 pl2 /\ pval_rel w h1 h2 /\ pfn_rel_at r w g1 g2)
  = assert (pcomp_rel r 1 w (PResumeC pl1 h1 g1) (PResumeC pl2 h2 g2));
    introduce forall (n: nat). pplan_rel r n w pl1 pl2
    with assert (pcomp_rel r (n + 1) w (PResumeC pl1 h1 g1) (PResumeC pl2 h2 g2));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with assert (pcomp_rel r (n + 1) w (PResumeC pl1 h1 g1) (PResumeC pl2 h2 g2)))

let lemma_pcrel_newp_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (l1 l2: string) (i1 i2: pval v) (b1 b2: pcomp v cl)
  : Lemma (requires pcrel r w (PNewP l1 i1 b1) (PNewP l2 i2 b2))
          (ensures l1 == l2 /\ pval_rel w i1 i2 /\ pcrel r w b1 b2)
  = assert (pcomp_rel r 1 w (PNewP l1 i1 b1) (PNewP l2 i2 b2));
    introduce forall (n: nat). pcomp_rel r n w b1 b2
    with assert (pcomp_rel r (n + 1) w (PNewP l1 i1 b1) (PNewP l2 i2 b2))

let lemma_pcrel_readp_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (l1 l2: string)
  : Lemma (requires pcrel #v #cl r w (PReadP l1) (PReadP l2)) (ensures l1 == l2)
  = assert (pcomp_rel #v #cl r 1 w (PReadP l1) (PReadP l2))

let lemma_pcrel_writep_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (l1 l2: string) (x1 x2: pval v)
  : Lemma (requires pcrel #v #cl r w (PWriteP l1 x1) (PWriteP l2 x2))
          (ensures l1 == l2 /\ pval_rel w x1 x2)
  = assert (pcomp_rel #v #cl r 1 w (PWriteP l1 x1) (PWriteP l2 x2))

(* ---- owners, items and plans --------------------------------------- *)

let lemma_porel_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                    (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                    (pv1 pv2: prompt_provenance)
  : Lemma (requires porel r w (POwner t1 ret1 pv1) (POwner t2 ret2 pv2) /\ pcl_down r)
          (ensures ptrel r w t1 t2 /\ pretrel r w ret1 ret2 /\ pv1 == pv2)
  = assert (powner_rel r 1 w (POwner t1 ret1 pv1) (POwner t2 ret2 pv2));
    assert (ptable_rel r 1 w t1 t2);
    introduce forall (n: nat). ptable_rel r n w t1 t2
    with (if n = 0
          then lemma_ptable_rel_down r 0 w t1 t2
          else assert (powner_rel r n w (POwner t1 ret1 pv1) (POwner t2 ret2 pv2)));
    match ret1, ret2 with
    | Some g1, Some g2 ->
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
      with (introduce _ ==> _
            with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
                 with (if n = 0 then ()
                       else assert (powner_rel r n w (POwner t1 ret1 pv1)
                                                     (POwner t2 ret2 pv2))))
    | _, _ -> ()

let lemma_pplrel_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (ls1 ls2: list (plan_item v cl)) (ow1 ow2: powner v cl)
  : Lemma (requires pplrel r w (Plan ls1 ow1) (Plan ls2 ow2))
          (ensures plsrel r w ls1 ls2 /\ porel r w ow1 ow2)
  = introduce forall (n: nat). pitems_rel r n w ls1 ls2
    with (if n = 0 then () else assert (pplan_rel r n w (Plan ls1 ow1) (Plan ls2 ow2)));
    introduce forall (n: nat). powner_rel r n w ow1 ow2
    with (if n = 0 then () else assert (pplan_rel r n w (Plan ls1 ow1) (Plan ls2 ow2)))

let lemma_plsrel_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (is1 is2: list (plan_item v cl))
  : Lemma (requires plsrel r w is1 is2) (ensures Nil? is1 == Nil? is2)
  = assert (pitems_rel r 1 w is1 is2)

let lemma_plsrel_cons_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                          (i1 i2: plan_item v cl) (t1 t2: list (plan_item v cl))
  : Lemma (requires plsrel r w (i1 :: t1) (i2 :: t2))
          (ensures pirel r w i1 i2 /\ plsrel r w t1 t2)
  = introduce forall (n: nat). pitem_rel r n w i1 i2
    with (if n = 0 then () else assert (pitems_rel r n w (i1 :: t1) (i2 :: t2)));
    introduce forall (n: nat). pitems_rel r n w t1 t2
    with (if n = 0 then () else assert (pitems_rel r n w (i1 :: t1) (i2 :: t2)))

let lemma_plsrel_cons (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (i1 i2: plan_item v cl) (t1 t2: list (plan_item v cl))
  : Lemma (requires pirel r w i1 i2 /\ plsrel r w t1 t2)
          (ensures plsrel r w (i1 :: t1) (i2 :: t2))
  = introduce forall (n: nat). pitems_rel r n w (i1 :: t1) (i2 :: t2)
    with (if n = 0 then () else (assert (pitem_rel r n w i1 i2);
                                 assert (pitems_rel r n w t1 t2)))

let lemma_plsrel_nil (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
  : Lemma (plsrel r w ([] <: list (plan_item v cl)) ([] <: list (plan_item v cl)))
  = introduce forall (n: nat).
      pitems_rel r n w ([] <: list (plan_item v cl)) ([] <: list (plan_item v cl))
    with ()

(* ---- items, constructed and inverted ------------------------------- *)

let lemma_pirel_bind (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pfn_rel_at r w g1 g2) (ensures pirel r w (PIBind g1) (PIBind g2))
  = introduce forall (n: nat). pitem_rel r n w (PIBind g1) (PIBind g2)
    with (if n = 0 then ()
          else introduce forall (w': pworld) (y1 y2: pval v).
                   (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                    pcomp_rel r n w' (g1 y1) (g2 y2))
               with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2))))

let lemma_pirel_bind_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pirel r w (PIBind g1) (PIBind g2)) (ensures pfn_rel_at r w g1 g2)
  = introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
               with (if n = 0 then ()
                     else assert (pitem_rel r n w (PIBind g1) (PIBind g2))))

let lemma_pirel_cell (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                     (l: string) (x1 x2: pval v)
  : Lemma (requires pval_rel w x1 x2)
          (ensures pirel #v #cl r w (PICell l x1) (PICell l x2))
  = introduce forall (n: nat). pitem_rel #v #cl r n w (PICell l x1) (PICell l x2) with ()

let lemma_pirel_cell_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (l1 l2: string) (x1 x2: pval v)
  : Lemma (requires pirel #v #cl r w (PICell l1 x1) (PICell l2 x2))
          (ensures l1 == l2 /\ pval_rel w x1 x2)
  = assert (pitem_rel #v #cl r 1 w (PICell l1 x1) (PICell l2 x2))

let lemma_pirel_transparent (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                            (t1 t2: ptable cl)
  : Lemma (requires ptrel r w t1 t2)
          (ensures pirel #v #cl r w (PITransparent t1) (PITransparent t2))
  = introduce forall (n: nat). pitem_rel #v #cl r n w (PITransparent t1) (PITransparent t2)
    with (if n = 0 then () else assert (ptable_rel r n w t1 t2))

let lemma_pirel_transparent_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                (t1 t2: ptable cl)
  : Lemma (requires pirel #v #cl r w (PITransparent t1) (PITransparent t2) /\ pcl_down r)
          (ensures ptrel r w t1 t2)
  = assert (pitem_rel #v #cl r 1 w (PITransparent t1) (PITransparent t2));
    introduce forall (n: nat). ptable_rel r n w t1 t2
    with (if n = 0
          then lemma_ptable_rel_down r 0 w t1 t2
          else assert (pitem_rel #v #cl r n w (PITransparent t1) (PITransparent t2)))

let lemma_pirel_reenter (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                        (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
  : Lemma (requires ptrel r w t1 t2 /\ pretrel r w ret1 ret2)
          (ensures pirel r w (PIReenter t1 ret1) (PIReenter t2 ret2))
  = introduce forall (n: nat). pitem_rel r n w (PIReenter t1 ret1) (PIReenter t2 ret2)
    with (if n = 0 then ()
          else begin
            assert (ptable_rel r n w t1 t2);
            match ret1, ret2 with
            | Some g1, Some g2 ->
              introduce forall (w': pworld) (y1 y2: pval v).
                  (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                   pcomp_rel r n w' (g1 y1) (g2 y2))
              with (introduce _ ==> _ with assert (pcrel r w' (g1 y1) (g2 y2)))
            | _, _ -> ()
          end)

let lemma_pirel_reenter_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                            (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
  : Lemma (requires pirel r w (PIReenter t1 ret1) (PIReenter t2 ret2) /\ pcl_down r)
          (ensures ptrel r w t1 t2 /\ pretrel r w ret1 ret2)
  = assert (pitem_rel r 1 w (PIReenter t1 ret1) (PIReenter t2 ret2));
    introduce forall (n: nat). ptable_rel r n w t1 t2
    with (if n = 0
          then lemma_ptable_rel_down r 0 w t1 t2
          else assert (pitem_rel r n w (PIReenter t1 ret1) (PIReenter t2 ret2)));
    match ret1, ret2 with
    | Some g1, Some g2 ->
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (g1 y1) (g2 y2))
      with (introduce _ ==> _
            with introduce forall (n: nat). pcomp_rel r n w' (g1 y1) (g2 y2)
                 with (if n = 0 then ()
                       else assert (pitem_rel r n w (PIReenter t1 ret1)
                                                    (PIReenter t2 ret2))))
    | _, _ -> ()

let lemma_pirel_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (i1 i2: plan_item v cl)
  : Lemma (requires pirel r w i1 i2) (ensures pitem_rel r 1 w i1 i2)
  = ()

(* ---- the three projections of a plan ------------------------------- *)

let lemma_owner_frame_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                          (o1 o2: powner v cl)
  : Lemma (requires porel r w o1 o2 /\ pcl_down r)
          (ensures pfrel r w (owner_frame o1) (owner_frame o2))
  = match o1, o2 with
    | POwner t1 ret1 pv1, POwner t2 ret2 pv2 ->
      lemma_porel_inv r w t1 t2 ret1 ret2 pv1 pv2;
      lemma_pfrel_prompt r w t1 t2 ret1 ret2 pv1

let rec lemma_enter_layer_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                     (ls1 ls2: list (plan_item v cl))
  : Lemma (requires plsrel r w ls1 ls2 /\ pcl_down r)
          (ensures pkrel r w (enter_layer_frames ls1) (enter_layer_frames ls2))
          (decreases ls1)
  = match ls1, ls2 with
    | [], [] -> lemma_pkrel_nil #v #cl r w
    | i1 :: t1, i2 :: t2 ->
      lemma_plsrel_cons_inv r w i1 i2 t1 t2;
      lemma_pirel_shape r w i1 i2;
      lemma_enter_layer_frames_rel r w t1 t2;
      (match i1, i2 with
       | PIBind _, PIBind _ -> ()
       | PICell l x1, PICell l2 x2 ->
         lemma_pirel_cell_inv r w l l2 x1 x2;
         lemma_pfrel_param #v #cl r w l x1 x2;
         lemma_pkrel_cons r w (PParamF l x1) (PParamF l2 x2)
                              (enter_layer_frames t1) (enter_layer_frames t2)
       | PITransparent tb1, PITransparent tb2 ->
         lemma_pirel_transparent_inv #v #cl r w tb1 tb2;
         lemma_pfrel_prompt #v #cl r w tb1 tb2 None None PMono;
         lemma_pkrel_cons r w (PPromptF tb1 None PMono) (PPromptF tb2 None PMono)
                              (enter_layer_frames t1) (enter_layer_frames t2)
       | PIReenter tb1 rc1, PIReenter tb2 rc2 ->
         lemma_pirel_reenter_inv r w tb1 tb2 rc1 rc2;
         lemma_pfrel_prompt r w tb1 tb2 rc1 rc2 PFamily;
         lemma_pkrel_cons r w (PPromptF tb1 rc1 PFamily) (PPromptF tb2 rc2 PFamily)
                              (enter_layer_frames t1) (enter_layer_frames t2)
       | _, _ -> ())
    | _, _ -> lemma_plsrel_shape r w ls1 ls2

let rec lemma_resume_layer_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                      (ls1 ls2: list (plan_item v cl))
  : Lemma (requires plsrel r w ls1 ls2 /\ pcl_down r)
          (ensures pkrel r w (resume_layer_frames ls1) (resume_layer_frames ls2))
          (decreases ls1)
  = match ls1, ls2 with
    | [], [] -> lemma_pkrel_nil #v #cl r w
    | i1 :: t1, i2 :: t2 ->
      lemma_plsrel_cons_inv r w i1 i2 t1 t2;
      lemma_pirel_shape r w i1 i2;
      lemma_resume_layer_frames_rel r w t1 t2;
      (match i1, i2 with
       | PIBind g1, PIBind g2 ->
         lemma_pirel_bind_inv r w g1 g2;
         lemma_pfrel_bind r w g1 g2;
         lemma_pkrel_cons r w (PBindF g1) (PBindF g2)
                              (resume_layer_frames t1) (resume_layer_frames t2)
       | PICell l x1, PICell l2 x2 ->
         lemma_pirel_cell_inv r w l l2 x1 x2;
         lemma_pfrel_param #v #cl r w l x1 x2;
         lemma_pkrel_cons r w (PParamF l x1) (PParamF l2 x2)
                              (resume_layer_frames t1) (resume_layer_frames t2)
       | PITransparent tb1, PITransparent tb2 ->
         lemma_pirel_transparent_inv #v #cl r w tb1 tb2;
         lemma_pfrel_prompt #v #cl r w tb1 tb2 None None PMono;
         lemma_pkrel_cons r w (PPromptF tb1 None PMono) (PPromptF tb2 None PMono)
                              (resume_layer_frames t1) (resume_layer_frames t2)
       | PIReenter tb1 rc1, PIReenter tb2 rc2 ->
         lemma_pirel_reenter_inv r w tb1 tb2 rc1 rc2;
         lemma_pfrel_prompt r w tb1 tb2 rc1 rc2 PFamily;
         lemma_pkrel_cons r w (PPromptF tb1 rc1 PFamily) (PPromptF tb2 rc2 PFamily)
                              (resume_layer_frames t1) (resume_layer_frames t2)
       | _, _ -> ())
    | _, _ -> lemma_plsrel_shape r w ls1 ls2

let rec lemma_protocol_layer_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                        (ls1 ls2: list (plan_item v cl))
  : Lemma (requires plsrel r w ls1 ls2 /\ pcl_down r)
          (ensures pkrel r w (protocol_layer_frames ls1) (protocol_layer_frames ls2))
          (decreases ls1)
  = match ls1, ls2 with
    | [], [] -> lemma_pkrel_nil #v #cl r w
    | i1 :: t1, i2 :: t2 ->
      lemma_plsrel_cons_inv r w i1 i2 t1 t2;
      lemma_pirel_shape r w i1 i2;
      lemma_protocol_layer_frames_rel r w t1 t2;
      (match i1, i2 with
       | PIBind g1, PIBind g2 ->
         lemma_pirel_bind_inv r w g1 g2;
         lemma_pfrel_site r w g1 g2;
         lemma_pkrel_cons r w (PSiteF g1) (PSiteF g2)
                              (protocol_layer_frames t1) (protocol_layer_frames t2)
       | PICell l x1, PICell l2 x2 ->
         lemma_pirel_cell_inv r w l l2 x1 x2;
         lemma_pfrel_param #v #cl r w l x1 x2;
         lemma_pkrel_cons r w (PParamF l x1) (PParamF l2 x2)
                              (protocol_layer_frames t1) (protocol_layer_frames t2)
       | PITransparent tb1, PITransparent tb2 ->
         lemma_pirel_transparent_inv #v #cl r w tb1 tb2;
         lemma_pfrel_prompt #v #cl r w tb1 tb2 None None PMono;
         lemma_pkrel_cons r w (PPromptF tb1 None PMono) (PPromptF tb2 None PMono)
                              (protocol_layer_frames t1) (protocol_layer_frames t2)
       | PIReenter tb1 rc1, PIReenter tb2 rc2 ->
         lemma_pirel_reenter_inv r w tb1 tb2 rc1 rc2;
         lemma_pfrel_prompt r w tb1 tb2 rc1 rc2 PFamily;
         lemma_pkrel_cons r w (PPromptF tb1 rc1 PFamily) (PPromptF tb2 rc2 PFamily)
                              (protocol_layer_frames t1) (protocol_layer_frames t2)
       | _, _ -> ())
    | _, _ -> lemma_plsrel_shape r w ls1 ls2

let lemma_plan_enter_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                (pl1 pl2: plan v cl)
  : Lemma (requires pplrel r w pl1 pl2 /\ pcl_down r)
          (ensures pkrel r w (plan_enter_frames pl1) (plan_enter_frames pl2))
  = match pl1, pl2 with
    | Plan ls1 ow1, Plan ls2 ow2 ->
      lemma_pplrel_inv r w ls1 ls2 ow1 ow2;
      lemma_enter_layer_frames_rel r w ls1 ls2;
      lemma_owner_frame_rel r w ow1 ow2;
      lemma_pkrel_nil #v #cl r w;
      lemma_pkrel_cons r w (owner_frame ow1) (owner_frame ow2) [] [];
      lemma_pkrel_append r w (enter_layer_frames ls1) (enter_layer_frames ls2)
                             [owner_frame ow1] [owner_frame ow2]

let lemma_plan_resume_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                 (pl1 pl2: plan v cl)
  : Lemma (requires pplrel r w pl1 pl2 /\ pcl_down r)
          (ensures pkrel r w (plan_resume_frames pl1) (plan_resume_frames pl2))
  = match pl1, pl2 with
    | Plan ls1 ow1, Plan ls2 ow2 ->
      lemma_pplrel_inv r w ls1 ls2 ow1 ow2;
      lemma_resume_layer_frames_rel r w ls1 ls2;
      lemma_owner_frame_rel r w ow1 ow2;
      lemma_pkrel_nil #v #cl r w;
      lemma_pkrel_cons r w (owner_frame ow1) (owner_frame ow2) [] [];
      lemma_pkrel_append r w (resume_layer_frames ls1) (resume_layer_frames ls2)
                             [owner_frame ow1] [owner_frame ow2]

let lemma_plan_protocol_frames_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                                   (pl1 pl2: plan v cl)
  : Lemma (requires pplrel r w pl1 pl2 /\ pcl_down r)
          (ensures pkrel r w (plan_protocol_frames pl1) (plan_protocol_frames pl2))
  = match pl1, pl2 with
    | Plan ls1 ow1, Plan ls2 ow2 ->
      lemma_pplrel_inv r w ls1 ls2 ow1 ow2;
      lemma_protocol_layer_frames_rel r w ls1 ls2;
      lemma_owner_frame_rel r w ow1 ow2;
      lemma_pkrel_nil #v #cl r w;
      lemma_pkrel_cons r w (owner_frame ow1) (owner_frame ow2) [] [];
      lemma_pkrel_append r w (protocol_layer_frames ls1) (protocol_layer_frames ls2)
                             [owner_frame ow1] [owner_frame ow2]

(* ---- what two related tables agree about --------------------------- *)

(** **Two related tables block the same effects, AS A SET.** PROVED, from
    `blocking_effects`' own refinement, which pins it as a set through
    `lookup_handler` -- exactly what `ptable_rel` compares. Set and not list:
    the refinement fixes membership and not order, so two `handlers` that answer
    every lookup alike may still report the labels in a different order, and no
    proof can close that gap. *)
let lemma_blocking_effects_agree (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                                 (t1 t2: ptable cl)
  : Lemma (requires ptable_rel r n w t1 t2)
          (ensures (forall (e: string).
                      mem e (blocking_effects t1.hs) <==> mem e (blocking_effects t2.hs)))
  = introduce forall (e: string).
        (mem e (blocking_effects t1.hs) <==> mem e (blocking_effects t2.hs))
    with begin
      introduce mem e (blocking_effects t1.hs) ==> mem e (blocking_effects t2.hs)
      with (eliminate exists (op: string) (found: found_clause cl).
                (lookup_handler t1.hs e op == Some found /\ found.kind =!= KFast)
            with (match lookup_handler t2.hs e op with
                  | Some f2 ->
                    introduce exists (o: string) (f: found_clause cl).
                        (lookup_handler t2.hs e o == Some f /\ f.kind =!= KFast)
                    with op f2 and ()
                  | None -> ()));
      introduce mem e (blocking_effects t2.hs) ==> mem e (blocking_effects t1.hs)
      with (eliminate exists (op: string) (found: found_clause cl).
                (lookup_handler t2.hs e op == Some found /\ found.kind =!= KFast)
            with (match lookup_handler t1.hs e op with
                  | Some f1 ->
                    introduce exists (o: string) (f: found_clause cl).
                        (lookup_handler t1.hs e o == Some f /\ f.kind =!= KFast)
                    with op f1 and ()
                  | None -> ()))
    end

(** Hence they agree on BORROWABILITY -- which is a `bool`, so here the
    set-level agreement is enough for an equality. *)
let lemma_borrowable_agree (#cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                           (t1 t2: ptable cl)
  : Lemma (requires ptable_rel r n w t1 t2)
          (ensures borrowable t1.hs == borrowable t2.hs)
  = lemma_blocking_effects_agree r n w t1 t2;
    (match blocking_effects t1.hs with
     | [] -> (match blocking_effects t2.hs with
              | [] -> ()
              | a :: rest -> assert (mem a (blocking_effects t2.hs)))
     | a :: rest ->
       assert (mem a (blocking_effects t1.hs));
       (match blocking_effects t2.hs with
        | [] -> ()
        | b :: rest2 -> ()))

(** And therefore on the CLASSIFICATION of a prompt. PROVED: `classify_prompt`
    reads the provenance, whether there is a return clause, and borrowability,
    and related tables and return clauses agree on all three. *)
let lemma_classify_agree (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
                         (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                         (pv: prompt_provenance)
  : Lemma (requires ptable_rel r n w t1 t2 /\ pretrel r w ret1 ret2)
          (ensures classify_prompt pv t1 ret1 == classify_prompt pv t2 ret2)
  = lemma_borrowable_agree r n w t1 t2

(* ---- rejections ---------------------------------------------------- *)

(**
 * **Rejections correspond.** Equality everywhere except the blocking labels of
 * an `UnborrowableScope`, which are compared AS A SET.
 *
 * That is not a weakening chosen for convenience: `blocking_effects` is pinned
 * by its refinement as a SET, so two tables that answer every lookup alike may
 * report the labels in different orders, and `plan_layers` puts the list it is
 * given into the rejection verbatim. An equality here would be a proposition
 * about `Hoop.Runtime.Handlers`' representation that the interface does not
 * fix. A rejection is terminal and is not a `PDone`, so nothing the nominal
 * observation looks at can see the difference either way.
 *)
let prej_rel (j1 j2: rejection) : prop
  = match j1, j2 with
    | ClauseKindMismatch e1 o1 x1 a1, ClauseKindMismatch e2 o2 x2 a2 ->
      e1 == e2 /\ o1 == o2 /\ x1 == x2 /\ a1 == a2
    | UnborrowableScope e1 o1 b1, UnborrowableScope e2 o2 b2 ->
      e1 == e2 /\ o1 == o2 /\ (forall (s: string). mem s b1 <==> mem s b2)
    | _, _ -> False

(* ---- building the plan --------------------------------------------- *)

let pfailrel (f1 f2: plan_failure) : prop
  = match f1, f2 with
    | MonomorphicLayer b1, MonomorphicLayer b2 ->
      forall (s: string). mem s b1 <==> mem s b2

let rec lemma_plan_layers_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                              (is1 is2: pstack v cl)
  : Lemma (requires pkrel r w is1 is2 /\ pcl_down r)
          (ensures (match plan_layers is1, plan_layers is2 with
                    | Inl e1, Inl e2 -> pfailrel e1 e2
                    | Inr ls1, Inr ls2 -> plsrel r w ls1 ls2
                    | _, _ -> False))
          (decreases is1)
  = match is1, is2 with
    | [], [] -> lemma_plsrel_nil #v #cl r w
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_plan_layers_rel r w t1 t2;
      (match f1, f2 with
       | PBindF g1, PBindF g2 ->
         lemma_pfrel_bind_inv r w g1 g2;
         lemma_pirel_bind r w g1 g2;
         (match plan_layers t1, plan_layers t2 with
          | Inr ls1, Inr ls2 -> lemma_plsrel_cons r w (PIBind g1) (PIBind g2) ls1 ls2
          | _, _ -> ())
       | PParamF l x1, PParamF l2 x2 ->
         lemma_pfrel_param_inv r w l l2 x1 x2;
         lemma_pirel_cell #v #cl r w l x1 x2;
         (match plan_layers t1, plan_layers t2 with
          | Inr ls1, Inr ls2 -> lemma_plsrel_cons r w (PICell l x1) (PICell l2 x2) ls1 ls2
          | _, _ -> ())
       | PPromptF tb1 rc1 pv1, PPromptF tb2 rc2 pv2 ->
         lemma_pfrel_prompt_inv r w tb1 tb2 rc1 rc2 pv1 pv2;
         assert (ptable_rel r 1 w tb1 tb2);
         lemma_classify_agree r 1 w tb1 tb2 rc1 rc2 pv1;
         (match classify_prompt pv1 tb1 rc1 with
          | Monomorphic -> lemma_blocking_effects_agree r 1 w tb1 tb2
          | ContextTransparent ->
            lemma_pirel_transparent #v #cl r w tb1 tb2;
            (match plan_layers t1, plan_layers t2 with
             | Inr ls1, Inr ls2 ->
               lemma_plsrel_cons r w (PITransparent tb1) (PITransparent tb2) ls1 ls2
             | _, _ -> ())
          | Family ->
            lemma_pirel_reenter r w tb1 tb2 rc1 rc2;
            (match plan_layers t1, plan_layers t2 with
             | Inr ls1, Inr ls2 ->
               lemma_plsrel_cons r w (PIReenter tb1 rc1) (PIReenter tb2 rc2) ls1 ls2
             | _, _ -> ()))
       | _, _ -> ())
    | _, _ -> lemma_pkrel_shape r w is1 is2

let lemma_plan_of_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (is1 is2: pstack v cl) (o1 o2: powner v cl)
  : Lemma (requires pkrel r w is1 is2 /\ porel r w o1 o2 /\ pcl_down r)
          (ensures (match plan_of is1 o1, plan_of is2 o2 with
                    | Inl e1, Inl e2 -> pfailrel e1 e2
                    | Inr pl1, Inr pl2 -> pplrel r w pl1 pl2
                    | _, _ -> False))
  = lemma_plan_layers_rel r w is1 is2;
    match plan_layers is1, plan_layers is2 with
    | Inr ls1, Inr ls2 ->
      introduce forall (n: nat). pplan_rel r n w (Plan ls1 o1) (Plan ls2 o2)
      with (if n = 0 then () else (assert (pitems_rel r n w ls1 ls2);
                                   assert (powner_rel r n w o1 o2)))
    | _, _ -> ()

(* ================================================================== *)
(*  THE FOUR STACK SEARCHES, COMPATIBLE                                *)
(*                                                                     *)
(*  Each is a walk down the stack, so each compatibility proof is one   *)
(*  induction over `pframes_rel`, which recurses at the SAME index --   *)
(*  no step is spent on the tail of a stack.                            *)
(* ================================================================== *)

(** **The prompt search.** Two related stacks stop at corresponding frames, with
    clauses of the same KIND and RELATED bodies, and split into related captured
    and remaining segments. The lookup's equivariance is where the boundary's
    `b_lookup` is spent. *)
(** The boundary's lookup condition, INSTANTIATED. It is a `forall` with no
    `{:pattern}`, so the trigger F* infers does not fire on a goal that already
    holds the two tables; the elimination is written out once here and every use
    below goes through it. *)
let lemma_lookup_equivariant_at (#cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                                (n: nat) (w: pworld) (t1 t2: ptable cl) (eff op: string)
  : Lemma (requires plookup_equivariant r lk /\ ptable_rel r n w t1 t2)
          (ensures (match lk t1 eff op, lk t2 eff op with
                    | None, None -> True
                    | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
                    | _, _ -> False))
  = lk_patterned r lk ()

let lemma_lk_rel (#cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl) (w: pworld)
                 (t1 t2: ptable cl) (eff op: string)
  : Lemma (requires ptrel r w t1 t2 /\ plookup_equivariant r lk)
          (ensures (match lk t1 eff op, lk t2 eff op with
                    | None, None -> True
                    | Some c1, Some c2 -> c1.kind == c2.kind /\ pclrel r w c1.body c2.body
                    | _, _ -> False))
  = lemma_lookup_equivariant_at r lk 1 w t1 t2 eff op;
    match lk t1 eff op, lk t2 eff op with
    | Some c1, Some c2 ->
      introduce forall (n: nat). r n w c1.body c2.body
      with lemma_lookup_equivariant_at r lk n w t1 t2 eff op
    | _, _ -> ()


let rec lemma_pfind_prompt_rel (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                               (w: pworld) (eff op: string) (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2 /\ plookup_equivariant r lk /\ pcl_down r)
          (ensures (match pfind_prompt lk eff op k1, pfind_prompt lk eff op k2 with
                    | None, None -> True
                    | Some (cap1, c1, b1), Some (cap2, c2, b2) ->
                      pkrel r w cap1 cap2 /\ pkrel r w b1 b2 /\
                      c1.kind == c2.kind /\ pclrel r w c1.body c2.body
                    | _, _ -> False))
          (decreases k1)
  = match k1, k2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_pfind_prompt_rel r lk w eff op t1 t2;
      (match f1, f2 with
       | PPromptF tb1 rc1 pv1, PPromptF tb2 rc2 pv2 ->
         lemma_pfrel_prompt_inv r w tb1 tb2 rc1 rc2 pv1 pv2;
         lemma_lk_rel r lk w tb1 tb2 eff op;
         (match lk tb1 eff op, lk tb2 eff op with
          | Some c1, Some c2 ->
            lemma_pkrel_nil #v #cl r w;
            lemma_pkrel_cons r w f1 f2 [] []
          | None, None ->
            (match pfind_prompt lk eff op t1, pfind_prompt lk eff op t2 with
             | Some (cap1, _, _), Some (cap2, _, _) -> lemma_pkrel_cons r w f1 f2 cap1 cap2
             | _, _ -> ())
          | _, _ -> ())
       | _, _ ->
         (match pfind_prompt lk eff op t1, pfind_prompt lk eff op t2 with
          | Some (cap1, _, _), Some (cap2, _, _) -> lemma_pkrel_cons r w f1 f2 cap1 cap2
          | _, _ -> ()))
    | _, _ -> lemma_pkrel_shape r w k1 k2

(** **The cell search.** *)
let rec lemma_pfind_param_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                              (l: string) (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2)
          (ensures (match pfind_param l k1, pfind_param l k2 with
                    | None, None -> True
                    | Some x1, Some x2 -> pval_rel w x1 x2
                    | _, _ -> False))
          (decreases k1)
  = match k1, k2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_pfind_param_rel r w l t1 t2;
      (match f1, f2 with
       | PParamF l1 x1, PParamF l2 x2 -> lemma_pfrel_param_inv r w l1 l2 x1 x2
       | _, _ -> ())
    | _, _ -> lemma_pkrel_shape r w k1 k2

(** **The cell write.** The stack it rebuilds is related frame for frame. *)
let rec lemma_pset_param_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                             (l: string) (x1 x2: pval v) (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2 /\ pval_rel w x1 x2)
          (ensures (match pset_param l x1 k1, pset_param l x2 k2 with
                    | None, None -> True
                    | Some k1', Some k2' -> pkrel r w k1' k2'
                    | _, _ -> False))
          (decreases k1)
  = match k1, k2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_pset_param_rel r w l x1 x2 t1 t2;
      (match f1, f2 with
       | PParamF l1 y1, PParamF l2 y2 ->
         lemma_pfrel_param_inv r w l1 l2 y1 y2;
         if l1 = l
         then (lemma_pfrel_param #v #cl r w l x1 x2;
               lemma_pkrel_cons r w (PParamF l x1) (PParamF l x2) t1 t2)
         else (match pset_param l x1 t1, pset_param l x2 t2 with
               | Some r1, Some r2 -> lemma_pkrel_cons r w f1 f2 r1 r2
               | _, _ -> ())
       | _, _ ->
         (match pset_param l x1 t1, pset_param l x2 t2 with
          | Some r1, Some r2 -> lemma_pkrel_cons r w f1 f2 r1 r2
          | _, _ -> ()))
    | _, _ -> lemma_pkrel_shape r w k1 k2

(** **The mode search.** Corresponding answers: the same mode, and responders
    that send related values to related computations. *)
let rec lemma_pfind_mode_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                             (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2)
          (ensures (match pfind_mode k1, pfind_mode k2 with
                    | None, None -> True
                    | Some (m1, g1), Some (m2, g2) -> m1 == m2 /\ pfn_rel_at r w g1 g2
                    | _, _ -> False))
          (decreases k1)
  = match k1, k2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_pfind_mode_rel r w t1 t2;
      (match f1, f2 with
       | PModeF m1 g1, PModeF m2 g2 -> lemma_pfrel_mode_inv r w m1 m2 g1 g2
       | _, _ -> ())
    | _, _ -> lemma_pkrel_shape r w k1 k2

(** **The scope cut.** Both sides cut at the same position, and both halves are
    related. *)
let rec lemma_pcut_scope_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                             (k1 k2: pstack v cl)
  : Lemma (requires pkrel r w k1 k2)
          (ensures (match pcut_scope k1, pcut_scope k2 with
                    | None, None -> True
                    | Some (a1, b1), Some (a2, b2) -> pkrel r w a1 a2 /\ pkrel r w b1 b2
                    | _, _ -> False))
          (decreases k1)
  = match k1, k2 with
    | [], [] -> ()
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      lemma_pcut_scope_rel r w t1 t2;
      (match f1, f2 with
       | PScopeF, PScopeF -> lemma_pkrel_nil #v #cl r w
       | _, _ ->
         (match pcut_scope t1, pcut_scope t2 with
          | Some (a1, _), Some (a2, _) -> lemma_pkrel_cons r w f1 f2 a1 a2
          | _, _ -> ()))
    | _, _ -> lemma_pkrel_shape r w k1 k2

(* ================================================================== *)
(*  CONTEXTS, THE STORE, AND THE OPERATIONS ON THEM                    *)
(* ================================================================== *)

let lemma_pcrel_op (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                   (a1 a2: pcomp v cl) (f1 f2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w a1 a2 /\ pfn_rel_at r w f1 f2)
          (ensures pcrel r w (POp a1 f1) (POp a2 f2))
  = introduce forall (n: nat). pcomp_rel r n w (POp a1 f1) (POp a2 f2)
    with (if n = 0 then ()
          else begin
            assert (pcomp_rel r (n - 1) w a1 a2);
            introduce forall (w': pworld) (y1 y2: pval v).
                (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                 pcomp_rel r (n - 1) w' (f1 y1) (f2 y2))
            with (introduce _ ==> _ with assert (pcrel r w' (f1 y1) (f2 y2)))
          end)

(** `pbind` is `POp`, so binding preserves the relation. *)
let lemma_pcrel_pbind (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (a1 a2: pcomp v cl) (f1 f2: pval v -> pcomp v cl)
  : Lemma (requires pcrel r w a1 a2 /\ pfn_rel_at r w f1 f2)
          (ensures pcrel r w (pbind a1 f1) (pbind a2 f2))
  = lemma_pcrel_op r w a1 a2 f1 f2

(** Applying an equivariant function pair, as a call rather than as a trigger. *)
let lemma_pfn_apply (#v #cl: Type) (r: pcl_rel_t cl) (w0 w: pworld)
                    (f1 f2: pval v -> pcomp v cl) (y1 y2: pval v)
  : Lemma (requires pfn_rel_at r w0 f1 f2 /\ pwf_world w /\ pwext w w0 /\ pval_rel w y1 y2)
          (ensures pcrel r w (f1 y1) (f2 y2))
  = ()

(* ---- contexts ------------------------------------------------------ *)

let lemma_pxrel_done (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (y1 y2: pval v)
  : Lemma (requires pval_rel w y1 y2)
          (ensures pxrel #v #cl r w (PCtxDone y1) (PCtxDone y2))
  = introduce forall (n: nat). pctx_rel #v #cl r n w (PCtxDone y1) (PCtxDone y2) with ()

let lemma_pxrel_requests (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                         (x1 x2: pval v) (rs1 rs2: pstack v cl)
                         (p1 p2: pval v -> pcomp v cl)
  : Lemma (requires pval_rel w x1 x2 /\ pkrel r w rs1 rs2 /\ pfn_rel_at r w p1 p2)
          (ensures pxrel r w (PCtxRequests x1 rs1 p1) (PCtxRequests x2 rs2 p2))
  = introduce forall (n: nat).
      pctx_rel r n w (PCtxRequests x1 rs1 p1) (PCtxRequests x2 rs2 p2)
    with (if n = 0 then ()
          else begin
            assert (pframes_rel r n w rs1 rs2);
            introduce forall (w': pworld) (y1 y2: pval v).
                (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                 pcomp_rel r n w' (p1 y1) (p2 y2))
            with (introduce _ ==> _ with assert (pcrel r w' (p1 y1) (p2 y2)))
          end)

let lemma_pxrel_requests_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                             (x1 x2: pval v) (rs1 rs2: pstack v cl)
                             (p1 p2: pval v -> pcomp v cl)
  : Lemma (requires pxrel r w (PCtxRequests x1 rs1 p1) (PCtxRequests x2 rs2 p2))
          (ensures pval_rel w x1 x2 /\ pkrel r w rs1 rs2 /\ pfn_rel_at r w p1 p2)
  = assert (pctx_rel r 1 w (PCtxRequests x1 rs1 p1) (PCtxRequests x2 rs2 p2));
    introduce forall (n: nat). pframes_rel r n w rs1 rs2
    with (if n = 0 then ()
          else assert (pctx_rel r n w (PCtxRequests x1 rs1 p1) (PCtxRequests x2 rs2 p2)));
    introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> pcrel r w' (p1 y1) (p2 y2))
    with (introduce _ ==> _
          with introduce forall (n: nat). pcomp_rel r n w' (p1 y1) (p2 y2)
               with (if n = 0 then ()
                     else assert (pctx_rel r n w (PCtxRequests x1 rs1 p1)
                                                 (PCtxRequests x2 rs2 p2))))

let lemma_pxrel_done_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (y1 y2: pval v)
  : Lemma (requires pxrel #v #cl r w (PCtxDone y1) (PCtxDone y2))
          (ensures pval_rel w y1 y2)
  = assert (pctx_rel #v #cl r 1 w (PCtxDone y1) (PCtxDone y2))

let lemma_pxrel_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (cx1 cx2: pctx v cl)
  : Lemma (requires pxrel r w cx1 cx2) (ensures pctx_rel r 1 w cx1 cx2)
  = ()

(* ---- resolving a handle -------------------------------------------- *)

(** **Resolution corresponds.** PROVED. A handle the world speaks for resolves on
    BOTH sides, to related contexts; a payload resolves on neither. There is no
    third case, because `pval_rel` has no clause relating a payload to a handle
    and none relating a handle no world speaks for. *)
let lemma_presolve_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (s1 s2: pstore v cl) (h1 h2: pval v)
  : Lemma (requires psrel r w s1 s2 /\ pval_rel w h1 h2)
          (ensures (match presolve s1 h1, presolve s2 h2 with
                    | None, None -> True
                    | Some cx1, Some cx2 -> pxrel r w cx1 cx2
                    | _, _ -> False))
  = match h1, h2 with
    | PCtxKey i, PCtxKey j ->
      assert (pwlookup_l i w == Some j);
      // `psrel`'s quantifier answers to the `psget` pair and to nothing else: a
      // goal that names only the two `Some?`s does not instantiate it. So the
      // relatedness of the two entries is asked for FIRST, and their presence
      // comes back with it.
      assert (pxrel r w (psget i s1) (psget j s2))
    | _, _ -> ()

(* ---- the continuation handed to a clause --------------------------- *)

let lemma_pkont_of_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (cap1 cap2: pstack v cl)
  : Lemma (requires pkrel r w cap1 cap2 /\ pcl_mono r)
          (ensures pfn_rel_at r w (pkont_of cap1) (pkont_of cap2))
  = introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
         pcrel r w' (pkont_of cap1 y1) (pkont_of cap2 y2))
    with (introduce _ ==> _
          with (lemma_pkrel_mono r w' w cap1 cap2;
                lemma_pcrel_var r w' y1 y2;
                lemma_pcrel_splice r w' cap1 cap2 (PVar y1) (PVar y2)))

(* ---- driving a residual, and the three consuming meanings ---------- *)

let lemma_ctx_drive_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (m: weave_mode)
                        (cx1 cx2: pctx v cl) (f1 f2: pval v -> pcomp v cl)
  : Lemma (requires pxrel r w cx1 cx2 /\ pfn_rel_at r w f1 f2 /\ pcl_mono r)
          (ensures pcrel r w (ctx_drive m cx1 f1) (ctx_drive m cx2 f2))
  = lemma_pxrel_shape r w cx1 cx2;
    match cx1, cx2 with
    | PCtxDone y1, PCtxDone y2 ->
      lemma_pxrel_done_inv r w y1 y2;
      lemma_pcrel_var r w y1 y2
    | PCtxRequests x1 rs1 p1, PCtxRequests x2 rs2 p2 ->
      lemma_pxrel_requests_inv r w x1 x2 rs1 rs2 p1 p2;
      let resp1 = (fun (z: pval v) -> pbind (p1 z) f1) in
      let resp2 = (fun (z: pval v) -> pbind (p2 z) f2) in
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcrel r w' (resp1 y1) (resp2 y2))
      with (introduce _ ==> _
            with (lemma_pfn_apply r w w' p1 p2 y1 y2;
                  lemma_pfn_rel_at_mono r w' w f1 f2;
                  lemma_pcrel_pbind r w' (p1 y1) (p2 y2) f1 f2));
      lemma_pfrel_mode r w m resp1 resp2;
      lemma_pkrel_nil #v #cl r w;
      lemma_pkrel_cons r w (PModeF m resp1) (PModeF m resp2) [] [];
      lemma_pkrel_append r w rs1 rs2 [PModeF m resp1] [PModeF m resp2];
      lemma_pcrel_var r w x1 x2;
      lemma_pcrel_splice r w (rs1 @ [PModeF m resp1]) (rs2 @ [PModeF m resp2])
                             (PVar x1) (PVar x2);
      // `assert_norm` and not `assert`, for the reason recorded at
      // `lemma_ctx_drive_answers_head`: `ctx_drive` BUILDS the responder lambda,
      // and a lambda occurring inside a definition gets an SMT encoding of its
      // own, so the equality with the same lambda written here is not something
      // Z3 can see. Normalising both sides makes the two terms identical.
      assert_norm (ctx_drive m (PCtxRequests x1 rs1 p1) f1
                   == PSplice (rs1 @ [PModeF m resp1]) (PVar x1));
      assert_norm (ctx_drive m (PCtxRequests x2 rs2 p2) f2
                   == PSplice (rs2 @ [PModeF m resp2]) (PVar x2))
    | _, _ -> ()

let lemma_extend_C_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (pl1 pl2: plan v cl) (cx1 cx2: pctx v cl)
                       (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pxrel r w cx1 cx2 /\ pfn_rel_at r w g1 g2 /\ pcl_mono r)
          (ensures pcrel r w (extend_C pl1 cx1 g1) (extend_C pl2 cx2 g2))
  = lemma_ctx_drive_rel r w MExtend cx1 cx2 g1 g2

let lemma_resume_C_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                       (pl1 pl2: plan v cl) (cx1 cx2: pctx v cl)
                       (k1 k2: pval v -> pcomp v cl)
  : Lemma (requires pxrel r w cx1 cx2 /\ pfn_rel_at r w k1 k2 /\ pcl_mono r)
          (ensures pcrel r w (resume_C pl1 cx1 k1) (resume_C pl2 cx2 k2))
  = lemma_ctx_drive_rel r w MResume cx1 cx2 k1 k2

let lemma_extend_ctx_C_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                           (pl1 pl2: plan v cl) (cx1 cx2: pctx v cl)
                           (g1 g2: pval v -> pcomp v cl)
  : Lemma (requires pxrel r w cx1 cx2 /\ pfn_rel_at r w g1 g2 /\ pcl_mono r)
          (ensures pxrel r w (extend_ctx_C pl1 cx1 g1) (extend_ctx_C pl2 cx2 g2))
  = lemma_pxrel_shape r w cx1 cx2;
    match cx1, cx2 with
    | PCtxDone y1, PCtxDone y2 ->
      lemma_pxrel_done_inv r w y1 y2;
      lemma_pxrel_done #v #cl r w y1 y2
    | PCtxRequests x1 rs1 p1, PCtxRequests x2 rs2 p2 ->
      lemma_pxrel_requests_inv r w x1 x2 rs1 rs2 p1 p2;
      let q1 = (fun (z: pval v) -> pbind (p1 z) g1) in
      let q2 = (fun (z: pval v) -> pbind (p2 z) g2) in
      introduce forall (w': pworld) (y1 y2: pval v).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcrel r w' (q1 y1) (q2 y2))
      with (introduce _ ==> _
            with (lemma_pfn_apply r w w' p1 p2 y1 y2;
                  lemma_pfn_rel_at_mono r w' w g1 g2;
                  lemma_pcrel_pbind r w' (p1 y1) (p2 y2) g1 g2));
      lemma_pxrel_requests r w x1 x2 rs1 rs2 q1 q2
    | _, _ -> ()

let lemma_enter_C_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                      (pl1 pl2: plan v cl) (c1 c2: pcomp v cl)
  : Lemma (requires pplrel r w pl1 pl2 /\ pcrel r w c1 c2 /\ pcl_down r)
          (ensures pcrel r w (enter_C pl1 c1) (enter_C pl2 c2))
  = lemma_plan_enter_frames_rel r w pl1 pl2;
    lemma_pcrel_splice r w (plan_enter_frames pl1) (plan_enter_frames pl2) c1 c2

(* ================================================================== *)
(*  CONFIGURATIONS                                                     *)
(* ================================================================== *)

let pstrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (st1 st2: pstate v cl)
  : GTot prop
  = match st1, st2 with
    | PDone x1, PDone x2 -> pval_rel w x1 x2
    | PStep c1 k1, PStep c2 k2 -> pcrel r w c1 c2 /\ pkrel r w k1 k2
    | PPaused x1 rs1, PPaused x2 rs2 -> pval_rel w x1 x2 /\ pkrel r w rs1 rs2
    | PStuck e1 o1, PStuck e2 o2 -> e1 == e2 /\ o1 == o2
    | PRejected j1, PRejected j2 -> prej_rel j1 j2
    | _, _ -> False

let pcfrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (cf1 cf2: pconf v cl)
  : GTot prop
  = pstrel r w cf1.st cf2.st /\ psrel r w cf1.store cf2.store /\
    pwbound w cf1.next cf2.next

(**
 * **Unfolding a hypothesis, by conversion.**
 *
 * A `GTot prop` definition applied to arguments is an ATOM to the SMT encoding:
 * a goal mentioning it unfolds, but a HYPOTHESIS mentioning it does not, and
 * every quantifier inside it is invisible. That is not a limit of this
 * development -- it is why `psrel`'s own `{:pattern}` cannot fire from a folded
 * hypothesis. The cast below is accepted BY CONVERSION, with no proof
 * obligation, and puts the body in the context where the solver can see it.
 *)
let pcfrel_unfold (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (cf1 cf2: pconf v cl)
                  (h: squash (pcfrel r w cf1 cf2))
  : squash (pstrel r w cf1.st cf2.st /\ psrel r w cf1.store cf2.store /\
            pwbound w cf1.next cf2.next)
  = h

let pstrel_unfold (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (st1 st2: pstate v cl)
                  (h: squash (pstrel r w st1 st2))
  : squash (match st1, st2 with
            | PDone x1, PDone x2 -> pval_rel w x1 x2
            | PStep c1 k1, PStep c2 k2 -> pcrel r w c1 c2 /\ pkrel r w k1 k2
            | PPaused x1 rs1, PPaused x2 rs2 -> pval_rel w x1 x2 /\ pkrel r w rs1 rs2
            | PStuck e1 o1, PStuck e2 o2 -> e1 == e2 /\ o1 == o2
            | PRejected j1, PRejected j2 -> prej_rel j1 j2
            | _, _ -> False)
  = h

(** The conclusion of the transition theorem, named so that the rule-by-rule
    lemmas and the dispatcher speak of one symbol. *)
let pstep_compat_at (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                    (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
  : GTot prop
  = snd (pstep_tr lk apply cf1) == snd (pstep_tr lk apply cf2) /\
    (exists (w': pworld).
       pwf_world w' /\ pwext w' w /\
       pcfrel r w' (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))

let pstep_compat_unfold (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                        (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                        (h: squash (pstep_compat_at r lk apply w cf1 cf2))
  : squash (snd (pstep_tr lk apply cf1) == snd (pstep_tr lk apply cf2) /\
            (exists (w': pworld).
               pwf_world w' /\ pwext w' w /\
               pcfrel r w' (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2))))
  = h

(* ================================================================== *)
(*  THE TRANSITION, RULE BY RULE                                       *)
(* ================================================================== *)

(** A terminal state is a fixed point of the transition, and the trace it emits
    is empty, so relatedness is carried across unchanged. *)
let lemma_step_terminal (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                        (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w /\ pcfrel r w cf1 cf2 /\
                    ~(PStep? cf1.st) /\ ~(PStep? cf2.st))
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pwext_refl w;
    assert (fst (pstep_tr lk apply cf1) == cf1);
    assert (fst (pstep_tr lk apply cf2) == cf2);
    introduce exists (w': pworld).
        (pwf_world w' /\ pwext w' w /\
         pcfrel r w' (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))
    with w and ()

(** The shared tail of every rule that neither allocates nor emits: exhibit the
    two successor configurations and the relation at the SAME world. *)
let lemma_step_same_world (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                          (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w /\
                    snd (pstep_tr lk apply cf1) == snd (pstep_tr lk apply cf2) /\
                    pcfrel r w (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pwext_refl w;
    introduce exists (w': pworld).
        (pwf_world w' /\ pwext w' w /\
         pcfrel r w' (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))
    with w and ()

let lemma_step_new_world (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                         (apply: papply_t v cl) (w w1: pworld) (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w1 /\ pwext w1 w /\
                    snd (pstep_tr lk apply cf1) == snd (pstep_tr lk apply cf2) /\
                    pcfrel r w1 (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = introduce exists (w': pworld).
        (pwf_world w' /\ pwext w' w /\
         pcfrel r w' (fst (pstep_tr lk apply cf1)) (fst (pstep_tr lk apply cf2)))
    with w1 and ()

(* ---- POp: push a bind frame ---------------------------------------- *)

let lemma_step_op (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                  (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                  (a1 a2: pcomp v cl) (f1 f2: pval v -> pcomp v cl)
                  (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (POp a1 f1) k1 /\ cf2.st == PStep (POp a2 f2) k2 /\
                    pcrel r w (POp a1 f1) (POp a2 f2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_op_inv r w a1 a2 f1 f2;
    lemma_pfrel_bind r w f1 f2;
    lemma_pkrel_cons r w (PBindF f1) (PBindF f2) k1 k2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PHandle: push a prompt frame ---------------------------------- *)

let lemma_step_handle (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                      (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                      (t1 t2: ptable cl) (ret1 ret2: option (pval v -> pcomp v cl))
                      (pv1 pv2: prompt_provenance) (b1 b2: pcomp v cl)
                      (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PHandle t1 ret1 pv1 b1) k1 /\
                    cf2.st == PStep (PHandle t2 ret2 pv2 b2) k2 /\
                    pcrel r w (PHandle t1 ret1 pv1 b1) (PHandle t2 ret2 pv2 b2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_handle_inv r w t1 t2 ret1 ret2 pv1 pv2 b1 b2;
    lemma_pfrel_prompt r w t1 t2 ret1 ret2 pv1;
    lemma_pkrel_cons r w (PPromptF t1 ret1 pv1) (PPromptF t2 ret2 pv2) k1 k2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PEmit: the one rule that emits --------------------------------- *)

let lemma_step_emit (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                    (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                    (e1 e2: string) (b1 b2: pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PEmit e1 b1) k1 /\ cf2.st == PStep (PEmit e2 b2) k2 /\
                    pcrel r w (PEmit e1 b1) (PEmit e2 b2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_emit_inv r w e1 e2 b1 b2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PSplice: push the captured frames ------------------------------ *)

let lemma_step_splice (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                      (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                      (fs1 fs2: pstack v cl) (b1 b2: pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PSplice fs1 b1) k1 /\
                    cf2.st == PStep (PSplice fs2 b2) k2 /\
                    pcrel r w (PSplice fs1 b1) (PSplice fs2 b2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_splice_inv r w fs1 fs2 b1 b2;
    lemma_pkrel_append r w fs1 fs2 k1 k2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PNewP: push a cell -------------------------------------------- *)

let lemma_step_newp (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                    (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                    (l1 l2: string) (i1 i2: pval v) (b1 b2: pcomp v cl)
                    (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PNewP l1 i1 b1) k1 /\
                    cf2.st == PStep (PNewP l2 i2 b2) k2 /\
                    pcrel r w (PNewP l1 i1 b1) (PNewP l2 i2 b2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_newp_inv r w l1 l2 i1 i2 b1 b2;
    lemma_pfrel_param #v #cl r w l1 i1 i2;
    lemma_pkrel_cons r w (PParamF l1 i1) (PParamF l2 i2) k1 k2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PReadP / PWriteP: the cell searches ---------------------------- *)

let lemma_step_readp (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                     (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                     (l1 l2: string) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PReadP l1) k1 /\ cf2.st == PStep (PReadP l2) k2 /\
                    pcrel #v #cl r w (PReadP l1) (PReadP l2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_readp_inv #v #cl r w l1 l2;
    lemma_pfind_param_rel r w l1 k1 k2;
    (match pfind_param l1 k1, pfind_param l2 k2 with
     | Some x1, Some x2 -> lemma_pcrel_var r w x1 x2
     | _, _ -> ());
    lemma_step_same_world r lk apply w cf1 cf2

let lemma_step_writep (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                      (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                      (l1 l2: string) (x1 x2: pval v) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PWriteP l1 x1) k1 /\
                    cf2.st == PStep (PWriteP l2 x2) k2 /\
                    pcrel #v #cl r w (PWriteP l1 x1) (PWriteP l2 x2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_writep_inv #v #cl r w l1 l2 x1 x2;
    lemma_pset_param_rel r w l1 x1 x2 k1 k2;
    lemma_pcrel_var r w x1 x2;
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PEnterCtx: production, four frames ----------------------------- *)

let lemma_step_enterctx (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                        (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                        (pl1 pl2: plan v cl) (b1 b2: pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_down r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PEnterCtx pl1 b1) k1 /\
                    cf2.st == PStep (PEnterCtx pl2 b2) k2 /\
                    pcrel r w (PEnterCtx pl1 b1) (PEnterCtx pl2 b2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_enterctx_inv r w pl1 pl2 b1 b2;
    lemma_plan_protocol_frames_rel r w pl1 pl2;
    lemma_pfrel_scope #v #cl r w;
    lemma_pkrel_cons r w PScopeF PScopeF k1 k2;
    lemma_pkrel_append r w (plan_protocol_frames pl1) (plan_protocol_frames pl2)
                           (PScopeF :: k1) (PScopeF :: k2);
    lemma_pfrel_boundary #v #cl r w;
    lemma_pkrel_cons r w PBoundaryF PBoundaryF
                         (plan_protocol_frames pl1 @ (PScopeF :: k1))
                         (plan_protocol_frames pl2 @ (PScopeF :: k2));
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PPerform: dispatch, and the clause interpreter ----------------- *)

let lemma_step_perform (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                       (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                       (e1 o1 e2 o2: string) (p1 p2: list (pval v))
                       (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\ pcl_down r /\
                    plookup_equivariant r lk /\ papply_equivariant r apply /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PPerform e1 o1 p1) k1 /\
                    cf2.st == PStep (PPerform e2 o2 p2) k2 /\
                    pcrel #v #cl r w (PPerform e1 o1 p1) (PPerform e2 o2 p2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_perform_inv #v #cl r w e1 o1 e2 o2 p1 p2;
    lemma_pfind_prompt_rel r lk w e1 o1 k1 k2;
    apply_patterned r apply ();
    (match pfind_prompt lk e1 o1 k1, pfind_prompt lk e2 o2 k2 with
     | Some (cap1, c1, b1), Some (cap2, c2, b2) ->
       lemma_pkont_of_rel r w cap1 cap2;
       (match c1.kind with
        | KScoped -> ()
        | _ -> assert (pcrel r w (apply c1.body p1 (pkont_of cap1))
                                 (apply c2.body p2 (pkont_of cap2))))
     | _, _ -> ());
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PWeave: build the plan, or refuse ------------------------------ *)

let lemma_step_weave (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                     (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                     (e1 o1 e2 o2: string) (is1 is2: pstack v cl)
                     (ow1 ow2: powner v cl) (b1 b2: pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_down r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PWeave e1 o1 is1 ow1 b1) k1 /\
                    cf2.st == PStep (PWeave e2 o2 is2 ow2 b2) k2 /\
                    pcrel r w (PWeave e1 o1 is1 ow1 b1) (PWeave e2 o2 is2 ow2 b2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_weave_inv r w e1 o1 e2 o2 is1 is2 ow1 ow2 b1 b2;
    lemma_plan_of_rel r w is1 is2 ow1 ow2;
    (match plan_of is1 ow1, plan_of is2 ow2 with
     | Inr pl1, Inr pl2 -> lemma_enter_C_rel r w pl1 pl2 b1 b2
     | _, _ -> ());
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PExtendC / PResumeC: resolve, then appeal to the meaning ------- *)

let lemma_step_extendc (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                       (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                       (pl1 pl2: plan v cl) (h1 h2: pval v)
                       (g1 g2: pval v -> pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PExtendC pl1 h1 g1) k1 /\
                    cf2.st == PStep (PExtendC pl2 h2 g2) k2 /\
                    pcrel r w (PExtendC pl1 h1 g1) (PExtendC pl2 h2 g2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_extendc_inv r w pl1 pl2 h1 h2 g1 g2;
    lemma_presolve_rel r w cf1.store cf2.store h1 h2;
    (match presolve cf1.store h1, presolve cf2.store h2 with
     | Some cx1, Some cx2 -> lemma_extend_C_rel r w pl1 pl2 cx1 cx2 g1 g2
     | _, _ -> ());
    lemma_step_same_world r lk apply w cf1 cf2

let lemma_step_resumec (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                       (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                       (pl1 pl2: plan v cl) (h1 h2: pval v)
                       (g1 g2: pval v -> pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PResumeC pl1 h1 g1) k1 /\
                    cf2.st == PStep (PResumeC pl2 h2 g2) k2 /\
                    pcrel r w (PResumeC pl1 h1 g1) (PResumeC pl2 h2 g2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_resumec_inv r w pl1 pl2 h1 h2 g1 g2;
    lemma_presolve_rel r w cf1.store cf2.store h1 h2;
    (match presolve cf1.store h1, presolve cf2.store h2 with
     | Some cx1, Some cx2 -> lemma_resume_C_rel r w pl1 pl2 cx1 cx2 g1 g2
     | _, _ -> ());
    lemma_step_same_world r lk apply w cf1 cf2

(* ---- PExtendCtxC: resolve, and ALLOCATE ----------------------------- *)

let lemma_step_extendctxc (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                          (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                          (pl1 pl2: plan v cl) (h1 h2: pval v)
                          (g1 g2: pval v -> pcomp v cl) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PExtendCtxC pl1 h1 g1) k1 /\
                    cf2.st == PStep (PExtendCtxC pl2 h2 g2) k2 /\
                    pcrel r w (PExtendCtxC pl1 h1 g1) (PExtendCtxC pl2 h2 g2) /\
                    pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_extendctxc_inv r w pl1 pl2 h1 h2 g1 g2;
    lemma_presolve_rel r w cf1.store cf2.store h1 h2;
    match presolve cf1.store h1, presolve cf2.store h2 with
    | Some cx1, Some cx2 ->
      lemma_extend_ctx_C_rel r w pl1 pl2 cx1 cx2 g1 g2;
      let n1 = cf1.next in
      let n2 = cf2.next in
      let d1 = extend_ctx_C pl1 cx1 g1 in
      let d2 = extend_ctx_C pl2 cx2 g2 in
      let w1 = pwextend n1 n2 w in
      lemma_psrel_alloc r w cf1.store cf2.store n1 n2 d1 d2;
      lemma_pkrel_mono r w1 w k1 k2;
      lemma_pcrel_var #v #cl r w1 (PCtxKey n1) (PCtxKey n2);
      lemma_step_new_world r lk apply w w1 cf1 cf2
    | _, _ -> lemma_step_same_world r lk apply w cf1 cf2

(* ---- The value rules, and production -------------------------------- *)

let lemma_pfn_rel_at_pvar (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
  : Lemma (pfn_rel_at #v #cl r w (PVar #v #cl) (PVar #v #cl))
  = introduce forall (w': pworld) (y1 y2: pval v).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
         pcrel #v #cl r w' (PVar y1) (PVar y2))
    with (introduce _ ==> _ with lemma_pcrel_var #v #cl r w' y1 y2)

(**
 * **PRODUCTION CORRESPONDS, AND THE WORLD GROWS BY EXACTLY ONE PAIR.** PROVED.
 *
 * Both sides cut at the same position (`lemma_pcut_scope_rel`), so both store a
 * residual of the same shape and both go on under related stacks. The world
 * handed back is the world handed in plus the single pair `(cf1.next, cf2.next)`
 * -- never anything computed from either final store.
 *)
let lemma_pyield_compat (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                        (x1 x2: pval v) (hd1 hd2: pframe v cl)
                        (rest1 rest2: pstack v cl) (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\ pval_rel w x1 x2 /\
                    pfrel r w hd1 hd2 /\ pkrel r w rest1 rest2 /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next)
          (ensures (exists (w': pworld).
                      pwf_world w' /\ pwext w' w /\
                      pcfrel r w' (pyield x1 hd1 rest1 cf1) (pyield x2 hd2 rest2 cf2)))
  = lemma_pcut_scope_rel r w rest1 rest2;
    lemma_pwext_refl w;
    match pcut_scope rest1, pcut_scope rest2 with
    | None, None ->
      lemma_pkrel_cons r w hd1 hd2 rest1 rest2;
      introduce exists (w': pworld).
          (pwf_world w' /\ pwext w' w /\
           pcfrel r w' (pyield x1 hd1 rest1 cf1) (pyield x2 hd2 rest2 cf2))
      with w and ()
    | Some (a1, b1), Some (a2, b2) ->
      let n1 = cf1.next in
      let n2 = cf2.next in
      let w1 = pwextend n1 n2 w in
      lemma_pkrel_cons r w hd1 hd2 a1 a2;
      lemma_pfn_rel_at_pvar #v #cl r w;
      lemma_pxrel_requests r w x1 x2 (hd1 :: a1) (hd2 :: a2) (PVar #v #cl) (PVar #v #cl);
      lemma_psrel_alloc r w cf1.store cf2.store n1 n2
                        (PCtxRequests x1 (hd1 :: a1) (PVar #v #cl))
                        (PCtxRequests x2 (hd2 :: a2) (PVar #v #cl));
      lemma_pkrel_mono r w1 w b1 b2;
      lemma_pcrel_var #v #cl r w1 (PCtxKey n1) (PCtxKey n2);
      introduce exists (w': pworld).
          (pwf_world w' /\ pwext w' w /\
           pcfrel r w' (pyield x1 hd1 rest1 cf1) (pyield x2 hd2 rest2 cf2))
      with w1 and ()
    | _, _ -> ()

let lemma_step_of_exists (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                         (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
  : Lemma (requires snd (pstep_tr lk apply cf1) == snd (pstep_tr lk apply cf2) /\
                    (exists (w': pworld).
                       pwf_world w' /\ pwext w' w /\
                       pcfrel r w' (fst (pstep_tr lk apply cf1))
                                   (fst (pstep_tr lk apply cf2))))
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = ()

(** The boundary arm, standalone: with a consumer in scope the value goes to
    that consumer's responder; with none, the scope YIELDS and a context is
    allocated on both sides. *)
let lemma_step_var_boundary (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                            (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                            (x1 x2: pval v) (t1 t2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PVar x1) (PBoundaryF :: t1) /\
                    cf2.st == PStep (PVar x2) (PBoundaryF :: t2) /\
                    pval_rel w x1 x2 /\ pkrel r w t1 t2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pwext_refl w;
    lemma_pfind_mode_rel r w t1 t2;
    match pfind_mode t1, pfind_mode t2 with
    | None, None ->
      lemma_pfrel_boundary #v #cl r w;
      lemma_pyield_compat r w x1 x2 PBoundaryF PBoundaryF t1 t2 cf1 cf2;
      lemma_step_of_exists r lk apply w cf1 cf2
    | Some (m1, g1), Some (m2, g2) ->
      lemma_pfn_apply r w w g1 g2 x1 x2;
      lemma_step_same_world r lk apply w cf1 cf2
    | _, _ -> ()

(** The recorded perform-site arm, standalone: under `MResume` the site's own
    continuation fires, under `MExtend` it is skipped, and with no consumer in
    scope the scope yields exactly as at a boundary. *)
let lemma_step_var_site (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                        (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                        (x1 x2: pval v) (g1 g2: pval v -> pcomp v cl)
                        (t1 t2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PVar x1) (PSiteF g1 :: t1) /\
                    cf2.st == PStep (PVar x2) (PSiteF g2 :: t2) /\
                    pval_rel w x1 x2 /\ pfn_rel_at r w g1 g2 /\ pkrel r w t1 t2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pwext_refl w;
    lemma_pfind_mode_rel r w t1 t2;
    match pfind_mode t1, pfind_mode t2 with
    | None, None ->
      lemma_pfrel_site r w g1 g2;
      lemma_pyield_compat r w x1 x2 (PSiteF g1) (PSiteF g2) t1 t2 cf1 cf2;
      lemma_step_of_exists r lk apply w cf1 cf2
    | Some (m1, _), Some (m2, _) ->
      (match m1 with
       | MResume -> lemma_pfn_apply r w w g1 g2 x1 x2
       | MExtend -> lemma_pcrel_var #v #cl r w x1 x2);
      lemma_step_same_world r lk apply w cf1 cf2
    | _, _ -> ()

(**
 * **THE VALUE RULES.** PROVED, all eight arms.
 *
 * Related stacks have related HEAD FRAMES, so the two runs take the same arm;
 * the two searches the protocol arms perform (`pfind_mode`, and `pcut_scope`
 * inside `pyield`) answer correspondingly; and the two arms that ALLOCATE --
 * the scope floor and production -- extend the world by one pair.
 *)
let lemma_step_var (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                   (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
                   (x1 x2: pval v) (k1 k2: pstack v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\ pcl_down r /\
                    psrel r w cf1.store cf2.store /\ pwbound w cf1.next cf2.next /\
                    cf1.st == PStep (PVar x1) k1 /\ cf2.st == PStep (PVar x2) k2 /\
                    pcrel #v #cl r w (PVar x1) (PVar x2) /\ pkrel r w k1 k2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = lemma_pcrel_var_inv #v #cl r w x1 x2;
    lemma_pkrel_shape r w k1 k2;
    lemma_pwext_refl w;
    match k1, k2 with
    | [], [] -> lemma_step_same_world r lk apply w cf1 cf2
    | f1 :: t1, f2 :: t2 ->
      lemma_pkrel_cons_inv r w f1 f2 t1 t2;
      assert (pframe_rel r 1 w f1 f2);
      (match f1, f2 with
       | PBindF g1, PBindF g2 ->
         lemma_pfrel_bind_inv r w g1 g2;
         lemma_pfn_apply r w w g1 g2 x1 x2;
         lemma_step_same_world r lk apply w cf1 cf2
       | PParamF _ _, PParamF _ _ ->
         lemma_pcrel_var #v #cl r w x1 x2;
         lemma_step_same_world r lk apply w cf1 cf2
       | PModeF _ _, PModeF _ _ ->
         lemma_pcrel_var #v #cl r w x1 x2;
         lemma_step_same_world r lk apply w cf1 cf2
       | PScopeF, PScopeF ->
         let n1 = cf1.next in
         let n2 = cf2.next in
         let w1 = pwextend n1 n2 w in
         lemma_pxrel_done #v #cl r w x1 x2;
         lemma_psrel_alloc r w cf1.store cf2.store n1 n2 (PCtxDone x1) (PCtxDone x2);
         lemma_pkrel_mono r w1 w t1 t2;
         lemma_pcrel_var #v #cl r w1 (PCtxKey n1) (PCtxKey n2);
         lemma_step_new_world r lk apply w w1 cf1 cf2
       | PBoundaryF, PBoundaryF ->
         lemma_step_var_boundary r lk apply w cf1 cf2 x1 x2 t1 t2
       | PSiteF g1, PSiteF g2 ->
         lemma_pfrel_site_inv r w g1 g2;
         lemma_step_var_site r lk apply w cf1 cf2 x1 x2 g1 g2 t1 t2
       | PPromptF tb1 rc1 pv1, PPromptF tb2 rc2 pv2 ->
         lemma_pfrel_prompt_inv r w tb1 tb2 rc1 rc2 pv1 pv2;
         (match rc1, rc2 with
          | Some g1, Some g2 -> lemma_pfn_apply r w w g1 g2 x1 x2
          | None, None -> lemma_pcrel_var #v #cl r w x1 x2
          | _, _ -> ());
         lemma_step_same_world r lk apply w cf1 cf2
       | _, _ -> ())
    | _, _ -> ()

(* ================================================================== *)
(*  CONDITION 1: THE TRANSITION TAKES RELATED CONFIGURATIONS TO         *)
(*  RELATED CONFIGURATIONS                                              *)
(* ================================================================== *)

(**
 * **TRANSITION COMPATIBILITY.** PROVED.
 *
 * Two configurations related at `w` step to two configurations related at a
 * world EXTENDING `w`, and the two steps emit the SAME event list. The world is
 * `w` itself except at the three rules that allocate -- the scope floor,
 * production, and `bindScope` -- where it is `w` plus exactly one pair.
 *
 * No transition count appears: this is one step against one step, and the
 * dispatcher is a case analysis on the node, not on a number.
 *)
let lemma_pstep_tr_compat (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                          (apply: papply_t v cl) (w: pworld) (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\ pcl_down r /\
                    plookup_equivariant r lk /\ papply_equivariant r apply /\
                    pcfrel r w cf1 cf2)
          (ensures pstep_compat_at r lk apply w cf1 cf2)
  = pcfrel_unfold r w cf1 cf2 ();
    pstrel_unfold r w cf1.st cf2.st ();
    match cf1.st, cf2.st with
    | PStep c1 k1, PStep c2 k2 ->
      assert (pcomp_rel r 1 w c1 c2);
      (match c1, c2 with
       | PVar x1, PVar x2 -> lemma_step_var r lk apply w cf1 cf2 x1 x2 k1 k2
       | POp a1 f1, POp a2 f2 -> lemma_step_op r lk apply w cf1 cf2 a1 a2 f1 f2 k1 k2
       | PPerform e1 o1 p1, PPerform e2 o2 p2 ->
         lemma_step_perform r lk apply w cf1 cf2 e1 o1 e2 o2 p1 p2 k1 k2
       | PHandle t1 rc1 pv1 b1, PHandle t2 rc2 pv2 b2 ->
         lemma_step_handle r lk apply w cf1 cf2 t1 t2 rc1 rc2 pv1 pv2 b1 b2 k1 k2
       | PSplice fs1 b1, PSplice fs2 b2 ->
         lemma_step_splice r lk apply w cf1 cf2 fs1 fs2 b1 b2 k1 k2
       | PEmit e1 b1, PEmit e2 b2 -> lemma_step_emit r lk apply w cf1 cf2 e1 e2 b1 b2 k1 k2
       | PWeave e1 o1 is1 ow1 b1, PWeave e2 o2 is2 ow2 b2 ->
         lemma_step_weave r lk apply w cf1 cf2 e1 o1 e2 o2 is1 is2 ow1 ow2 b1 b2 k1 k2
       | PEnterCtx pl1 b1, PEnterCtx pl2 b2 ->
         lemma_step_enterctx r lk apply w cf1 cf2 pl1 pl2 b1 b2 k1 k2
       | PExtendC pl1 h1 g1, PExtendC pl2 h2 g2 ->
         lemma_step_extendc r lk apply w cf1 cf2 pl1 pl2 h1 h2 g1 g2 k1 k2
       | PExtendCtxC pl1 h1 g1, PExtendCtxC pl2 h2 g2 ->
         lemma_step_extendctxc r lk apply w cf1 cf2 pl1 pl2 h1 h2 g1 g2 k1 k2
       | PResumeC pl1 h1 g1, PResumeC pl2 h2 g2 ->
         lemma_step_resumec r lk apply w cf1 cf2 pl1 pl2 h1 h2 g1 g2 k1 k2
       | PNewP l1 i1 b1, PNewP l2 i2 b2 ->
         lemma_step_newp r lk apply w cf1 cf2 l1 l2 i1 i2 b1 b2 k1 k2
       | PReadP l1, PReadP l2 -> lemma_step_readp r lk apply w cf1 cf2 l1 l2 k1 k2
       | PWriteP l1 y1, PWriteP l2 y2 ->
         lemma_step_writep r lk apply w cf1 cf2 l1 l2 y1 y2 k1 k2
       | _, _ -> ())
    | PDone _, PDone _ -> lemma_step_terminal r lk apply w cf1 cf2
    | PPaused _ _, PPaused _ _ -> lemma_step_terminal r lk apply w cf1 cf2
    | PStuck _ _, PStuck _ _ -> lemma_step_terminal r lk apply w cf1 cf2
    | PRejected _, PRejected _ -> lemma_step_terminal r lk apply w cf1 cf2
    | _, _ -> ()

(* ================================================================== *)
(*  CONDITION 2: ONE STEP LIFTS TO A FINITE RUN                        *)
(* ================================================================== *)

(**
 * **THE FUNDAMENTAL THEOREM.** PROVED.
 *
 * Related configurations, run for THE SAME FUEL, produce the SAME TRACE and two
 * configurations related at a world extending the one they started in.
 *
 * Three things this statement does NOT do, each deliberate:
 *
 *   - it never re-anchors: the world handed back is a `pwext` of the world
 *     handed in, built from it by one `pwextend` per allocation, and nothing is
 *     ever computed from a final store;
 *   - it relates no transition counts: both sides are run at the SAME fuel and
 *     the induction is on that fuel, so no offset can appear -- and the fuel is
 *     not observable, since `pnconverges` quantifies it away independently on
 *     each side;
 *   - it says nothing about termination. If one side diverges so does the
 *     other, and the two unfinished configurations are still related.
 *)
let rec lemma_prun_compat (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                          (apply: papply_t v cl) (fuel: nat) (w: pworld)
                          (cf1 cf2: pconf v cl)
  : Lemma (requires pwf_world w /\ pcl_mono r /\ pcl_down r /\
                    plookup_equivariant r lk /\ papply_equivariant r apply /\
                    pcfrel r w cf1 cf2)
          (ensures snd (prun lk apply fuel cf1) == snd (prun lk apply fuel cf2) /\
                   (exists (w': pworld).
                      pwf_world w' /\ pwext w' w /\
                      pcfrel r w' (fst (prun lk apply fuel cf1))
                                  (fst (prun lk apply fuel cf2))))
          (decreases fuel)
  = lemma_pwext_refl w;
    pcfrel_unfold r w cf1 cf2 ();
    pstrel_unfold r w cf1.st cf2.st ();
    if fuel = 0
    then introduce exists (w': pworld).
             (pwf_world w' /\ pwext w' w /\
              pcfrel r w' (fst (prun lk apply fuel cf1)) (fst (prun lk apply fuel cf2)))
         with w and ()
    else begin
      let f1r : nat = fuel - 1 in
      match cf1.st, cf2.st with
      | PStep c1 k1, PStep c2 k2 ->
        lemma_pstep_tr_compat r lk apply w cf1 cf2;
        pstep_compat_unfold r lk apply w cf1 cf2 ();
        let d1 = fst (pstep_tr lk apply cf1) in
        let d2 = fst (pstep_tr lk apply cf2) in
        eliminate exists (w1: pworld). (pwf_world w1 /\ pwext w1 w /\ pcfrel r w1 d1 d2)
        with (lemma_prun_compat r lk apply f1r w1 d1 d2;
              eliminate exists (w2: pworld).
                  (pwf_world w2 /\ pwext w2 w1 /\
                   pcfrel r w2 (fst (prun lk apply f1r d1))
                               (fst (prun lk apply f1r d2)))
              with (lemma_pwext_trans w2 w1 w;
                    introduce exists (w': pworld).
                        (pwf_world w' /\ pwext w' w /\
                         pcfrel r w' (fst (prun lk apply fuel cf1))
                                     (fst (prun lk apply fuel cf2)))
                    with w2 and ()))
      | _, _ ->
        introduce exists (w': pworld).
            (pwf_world w' /\ pwext w' w /\
             pcfrel r w' (fst (prun lk apply fuel cf1)) (fst (prun lk apply fuel cf2)))
        with w and ()
    end

(* ================================================================== *)
(*  THE NOMINAL OBSERVATION, DERIVED                                   *)
(* ================================================================== *)

let pequivariant_k_at_unfold (#v #cl: Type) (r: pcl_rel_t cl) (w0: pworld)
                             (k: pstack v cl)
                             (h: squash (pequivariant_k_at r w0 k))
  : squash (forall (w: pworld). pwf_world w /\ pwext w w0 ==> pkrel r w k k)
  = h

let pnconverges_unfold (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                       (cf: pconf v cl) (tr: list string) (x: pval v)
                       (sto': pstore v cl)
                       (h: squash (pnconverges lk apply cf tr x sto'))
  : squash (exists (n: nat).
              (fst (prun lk apply n cf)).st == PDone x /\
              snd (prun lk apply n cf) == tr /\
              (fst (prun lk apply n cf)).store == sto')
  = h

let lemma_pstrel_done_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
                          (x1: pval v) (st2: pstate v cl)
  : Lemma (requires pstrel r w (PDone x1) st2)
          (ensures PDone? st2 /\ pval_rel w x1 (PDone?.value st2))
  = pstrel_unfold r w (PDone x1) st2 ()

(**
 * **CONDITION 2, DELIVERED: `pnobs_tr_le` IS DERIVABLE.** PROVED.
 *
 * Two computations related at every well-formed world are in the nominal
 * observation relation -- at EVERY equivariant ambient stack, EVERY equivariant
 * initial store and every counter fresh for it, which is the universal
 * quantification B2b.1 could not reach.
 *
 * The proof is the fundamental theorem and nothing else: run both sides at the
 * fuel the left run's convergence supplies, read the trace equality off, and
 * read the value and store correspondence off the world the theorem hands back.
 * That world is the witness the consequent's existential wants, and it was never
 * written down by hand.
 *)
let lemma_pnobs_tr_le_of_crel (#v #cl: Type) (b: pboundary v cl) (c1 c2: pcomp v cl)
  : Lemma (requires forall (w: pworld). pwf_world w ==> pcrel b.b_rel w c1 c2)
          (ensures pnobs_tr_le b c1 c2)
  = let _ : squash (pcl_mono b.b_rel) = b.b_mono in
    let _ : squash (pcl_down b.b_rel) = b.b_down in
    let _ : squash (plookup_equivariant b.b_rel b.b_lk) = b.b_lookup in
    let _ : squash (papply_equivariant b.b_rel b.b_apply) = b.b_apply_eq in
    introduce forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
                     (tr: list string) (x1: pval v) (s1': pstore v cl).
        ((pequivariant_k_at b.b_rel (panchor sto) k /\
          pstore_equivariant_at b.b_rel sto /\
          psfresh sto n0 /\
          pnconverges b.b_lk b.b_apply
                      ({ st = PStep c1 k; store = sto; next = n0 }) tr x1 s1') ==>
         (exists (x2: pval v) (s2': pstore v cl) (w: pworld).
            pnconverges b.b_lk b.b_apply
                        ({ st = PStep c2 k; store = sto; next = n0 }) tr x2 s2' /\
            pwf_world w /\ pwext w (panchor sto) /\
            pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
    with
      (introduce _ ==> _
       with begin
         let w0 = panchor sto in
         let cf1 : pconf v cl = { st = PStep c1 k; store = sto; next = n0 } in
         let cf2 : pconf v cl = { st = PStep c2 k; store = sto; next = n0 } in
         lemma_panchor_wf sto;
         lemma_panchor_bound sto n0;
         lemma_psrel_anchor_at b.b_rel sto;
         lemma_pwext_refl w0;
         pequivariant_k_at_unfold b.b_rel w0 k ();
         assert (pkrel b.b_rel w0 k k);
         assert (pcrel b.b_rel w0 c1 c2);
         assert (pcfrel b.b_rel w0 cf1 cf2);
         pnconverges_unfold b.b_lk b.b_apply cf1 tr x1 s1' ();
         eliminate exists (n: nat).
             ((fst (prun b.b_lk b.b_apply n cf1)).st == PDone x1 /\
              snd (prun b.b_lk b.b_apply n cf1) == tr /\
              (fst (prun b.b_lk b.b_apply n cf1)).store == s1')
         with
           (lemma_prun_compat b.b_rel b.b_lk b.b_apply n w0 cf1 cf2;
            eliminate exists (w': pworld).
                (pwf_world w' /\ pwext w' w0 /\
                 pcfrel b.b_rel w' (fst (prun b.b_lk b.b_apply n cf1))
                                   (fst (prun b.b_lk b.b_apply n cf2)))
            with begin
              let e1 = fst (prun b.b_lk b.b_apply n cf1) in
              let e2 = fst (prun b.b_lk b.b_apply n cf2) in
              pcfrel_unfold b.b_rel w' e1 e2 ();
              lemma_pstrel_done_inv b.b_rel w' x1 e2.st;
              let x2 = PDone?.value e2.st in
              lemma_pnconverges_at b.b_lk b.b_apply cf2 n tr x2 e2.store;
              introduce exists (y2: pval v) (t2: pstore v cl) (ww: pworld).
                  (pnconverges b.b_lk b.b_apply cf2 tr y2 t2 /\
                   pwf_world ww /\ pwext ww (panchor sto) /\
                   pval_rel ww x1 y2 /\ psrel b.b_rel ww s1' t2)
              with x2 e2.store w' and ()
            end)
       end)

(* ================================================================== *)
(*  RUNS COMPOSE                                                       *)
(* ================================================================== *)

(** **A run of `a + b` transitions is a run of `a` followed by a run of `b`, and
    its trace is the concatenation.** PROVED, by induction on the first count.
    This is what lets a result about a COMMON SUFFIX of two runs be composed with
    a prefix each side takes on its own -- which is how the counterexample pairs
    are handled below, since their two sides reach the common configuration in
    DIFFERENT numbers of steps. *)
let rec lemma_prun_split (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                         (a b: nat) (cf: pconf v cl)
  : Lemma (ensures (let (cfa, ta) = prun lk apply a cf in
                    let (cfb, tb) = prun lk apply b cfa in
                    prun lk apply (a + b) cf == (cfb, ta @ tb)))
          (decreases a)
  = if a = 0 then ()
    else
      match cf.st with
      | PDone _ -> ()
      | PPaused _ _ -> ()
      | PStuck _ _ -> ()
      | PRejected _ -> ()
      | PStep _ _ ->
        let (cf', ev) = pstep_tr lk apply cf in
        lemma_prun_split lk apply (a - 1) b cf';
        let (cfa, ta) = prun lk apply (a - 1) cf' in
        let (cfb, tb) = prun lk apply b cfa in
        append_assoc ev ta tb


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
(*  THE FIRST LINE OF THAT TABLE IS FALSE, AND B2b PROVES THAT IT IS.   *)
(*                                                                     *)
(*  It is left standing above because it is what the laws were WRITTEN  *)
(*  to say, and striking it out would hide the shape of the intention.  *)
(*  But the reading it records does not hold: `ref_ops` REFUSES all     *)
(*  five, and the refusals are checked --                               *)
(*  `guard_ref_ops_refutes_left_identity` and the five guards beside    *)
(*  it, each a proof of a NEGATION and not a proof left undone.         *)
(*                                                                     *)
(*  The reason is not in the operations. `pobs_tr_le` fixes the store   *)
(*  and the counter at the start and compares `pval v` at the end, and  *)
(*  `pval v` contains `PCtxKey`, so the NAME of a freshly allocated     *)
(*  handle is observable. Every law's left-hand side allocates at least *)
(*  one context and its right-hand side allocates none, so a            *)
(*  continuation that produces a context afterwards reports a different *)
(*  key on the two sides. That is the whole of the counterexample, and  *)
(*  it works at the empty store, at counter zero, one transition from   *)
(*  `pload` of a closed program -- so it is not the gate's flagged case *)
(*  of a law failing only at configurations the machine cannot reach.   *)
(*  `guard_ce_conf_one_step_from_pload` and `guard_ce_conf_ok` are      *)
(*  what say so, and they say it by proof rather than by inspection.    *)
(*                                                                     *)
(*  AND THE OTHER TWO LINES OF THE TABLE NO LONGER SAY WHAT THEY       *)
(*  MEANT. The same counterexample refuses `pointwise_ops` and          *)
(*  `flat_ops` -- `guard_pointwise_ops_refutes_left_identity` and       *)
(*  `guard_flat_ops_refutes_left_identity`, both checked -- so          *)
(*  `law_left_identity` is false of EVERY implementation this file      *)
(*  defines, and a proposition false of every candidate separates none  *)
(*  of them. The laws as stated therefore discriminate nothing. Note    *)
(*  particularly that a PURELY ALGEBRAIC law refuses `flat_ops`, which  *)
(*  the note on `flat_ops` argues cannot happen: that argument is not   *)
(*  contradicted, because the refusal is not about the algebra. The     *)
(*  block comment before those two guards says exactly how little they  *)
(*  establish.                                                          *)
(*                                                                     *)
(*  NO STATEMENT BELOW IS AMENDED IN RESPONSE. Two amendments are       *)
(*  available -- restrict the observation to answers in the image of    *)
(*  `PV`, or quotient it by a store isomorphism -- and each changes     *)
(*  what the five laws CLAIM, which makes choosing between them a       *)
(*  design decision about the relation rather than a step in a proof.   *)
(*  The decision is not taken here.                                     *)
(*                                                                     *)
(*  WHAT IS NOT SETTLED, AND IT IS THE INTERESTING PART. Whether the    *)
(*  five would hold under an amended relation is NOT established        *)
(*  either way. The counterexample decides them as stated and says      *)
(*  nothing about what remains: `law_right_identity`'s two sides also   *)
(*  run the inner computation under DIFFERENT frame lists --            *)
(*  `plan_protocol_frames pl` beneath a `PModeF MExtend` on the left    *)
(*  against `plan_enter_frames pl` on the right -- and that they agree  *)
(*  is a bisimulation nothing in this file attempts. The refutations    *)
(*  below therefore CLOSE the question as posed and REOPEN it one line  *)
(*  further down.                                                       *)
(*                                                                     *)
(*  WHAT B1.8 CHANGED, AND IT IS ONE WORD IN EACH OF THE FIVE.          *)
(*                                                                     *)
(*  Every law below is stated over `pobs_tr_eq` and not over `pobs_eq`. *)
(*  The reason is recorded at `prun` and at the observation section: a  *)
(*  value-only relation is satisfied by an implementation that replays  *)
(*  the protected prefix, so under `pobs_eq` these five propositions    *)
(*  did not constrain the one thing the residual representation exists  *)
(*  to buy. They now do -- an implementation that emits an event twice  *)
(*  where the reference emits it once falsifies them, and               *)
(*  `guard_trace_separates_residual_from_suspension` is the instance of *)
(*  exactly that separation, checked.                                   *)
(*                                                                     *)
(*  NOTHING IS GIVEN UP BY THE RETARGET. `lemma_pobs_tr_eq_forget`      *)
(*  proves `pobs_tr_eq ==> pobs_eq`, so each law over the trace-aware   *)
(*  relation IMPLIES the same law over the value-only one, and every    *)
(*  obligation B1.5 and B1.6 wrote down is still an obligation here.    *)
(*  The five are now HARDER to prove than they were, which is the       *)
(*  point and is B2b's problem: this gate's business is that they are   *)
(*  still WELL TYPED, and it does not claim they hold. What is checked  *)
(*  below is that each definition type-checks at `prop` against the new *)
(*  relation, and nothing beyond that.                                  *)
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
(*  stuck while the other proceeds. The statements therefore COVER the  *)
(*  ambient-handler cases B1.5's `settles` premise excluded: those      *)
(*  configurations are now inside the obligation rather than outside    *)
(*  it. That is a claim about the domain the laws speak of, not a claim *)
(*  that they are logically stronger -- no pair is exhibited that the   *)
(*  earlier statements joined and these do not. Whether they HOLD there *)
(*  is B2b's, and this file does not claim it.                         *)
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
 *
 * **B2b: THIS IS FALSE OF `ref_ops`, and the negation is PROVED** --
 * `guard_ref_ops_refutes_left_identity`, at `plan_A`, `fone` and `PVar`. The
 * left-hand side produces a context and the right-hand side does not, so the two
 * runs leave the counter one apart, and `pobs_tr_eq` observes the handle the next
 * production is handed. The statement above is NOT amended; the block comment
 * before the laws says why, and says what the two available amendments would
 * change about what this law claims.
 *)
let law_left_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (g: pval v -> pcomp v cl)
  : GTot prop
  = pobs_tr_eq lk apply
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
 *
 * **B2b: THIS IS FALSE OF `ref_ops`, and the negation is PROVED** --
 * `guard_ref_ops_refutes_right_identity`, at `plan_A` and `c = PVar fone`. The
 * bridging fact this law was to have established -- that `MExtend` makes a
 * `PSiteF` nothing, so `plan_protocol_frames` agrees with `plan_enter_frames` --
 * IS NOT DECIDED by the refutation, in either direction: the counterexample
 * separates the two sides on the allocation counter, at a plan with no `PIBind`
 * and therefore no `PSiteF` at all. The bridging fact remains open and is
 * neither claimed nor refuted here.
 *)
let law_right_identity
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pobs_tr_eq lk apply
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
 *
 * **B2b: BOTH CONJUNCTS ARE FALSE OF `ref_ops`, and both negations are PROVED**
 * -- `guard_ref_ops_refutes_assoc_algebraic` and
 * `guard_ref_ops_refutes_assoc_anchored`, with
 * `guard_ref_ops_refutes_assoc` refuting the conjunction they make up. They fail
 * at two DIFFERENT configurations and for the same reason: `o_extend_ctx`
 * ALLOCATES -- which is condition 8 working as designed -- and the composite
 * extension on the other side does not. The anchored half's two sides are two
 * allocations apart rather than one.
 *
 * The algebraic half is the only statement among the six that names a context it
 * did not itself produce, so its refutation had to be careful about which store
 * it stood at. It stands at the store an actual production left behind
 * (`ce_prod`), at the handle that production returned, and
 * `guard_ce_aa_reachable` proves the whole configuration -- store, counter and
 * stack together -- is what five transitions of a closed program reach.
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
    pobs_tr_eq lk apply
      (pbind (ops.o_extend_ctx pl cx g) (fun cy -> ops.o_extend pl cy h))
      (ops.o_extend pl cx (fun x -> pbind (g x) h))
    /\ // the anchored half -- one crossing of THIS plan, and no other
    pobs_tr_eq lk apply
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
 *
 * **B2b: THIS IS FALSE OF `ref_ops`, and the negation is PROVED** --
 * `guard_ref_ops_refutes_resume`. It is worth saying which part does NOT break:
 * this is one of the two ANCHORED laws, written against `plan_resume_frames`
 * rather than against the operations, and the anchoring is not what fails. The
 * counter separates the two sides before the resumption's own behaviour is
 * reached, at a plan whose resume projection and enter projection are the same
 * one-frame list. What resumption MEANS is untouched by the refutation.
 *)
let law_resume_matches_continuation
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (k: pval v -> pcomp v cl)
  : GTot prop
  = pobs_tr_eq lk apply
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
 *
 * **B2b: THIS IS FALSE OF `ref_ops`, and the negation is PROVED** --
 * `guard_ref_ops_refutes_transparent_agrees`, AT A PLAN WITH NO LAYERS. A plan
 * with no layers is one all of whose layers are transparent, for want of any, so
 * the hypothesis this law is stated under is satisfied in the strongest way it
 * can be -- and the law still fails. What that shows is that the gap is not
 * about transparency: it is the same allocation the other four trip over.
 * `fixture_6_transparent` is unaffected and still checks what it checked, which
 * is an equality of two RUNS and not an instance of this proposition.
 *)
let law_transparent_agrees
    (#v #cl: Type)
    (lk: plookup_t cl) (apply: papply_t v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pobs_tr_eq lk apply
      (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
      (PSplice (plan_enter_frames pl) c)

(* ================================================================== *)
(*  B2b.1: THE FIVE LAWS, RETARGETED AT THE NOMINAL OBSERVATION        *)
(*                                                                     *)
(*  The five above are FALSE of `ref_ops` -- proved, six times, in the  *)
(*  B2b section -- and the cause is `pobs_tr_eq`'s comparison of a      *)
(*  `pval v` by equality when `pval v` contains `PCtxKey`.  This block  *)
(*  states the same five over `pnobs_tr_eq`, which compares the values  *)
(*  under a WORLD and the stores on that world's domain, and leaves the *)
(*  trace comparison exactly as it was.                                 *)
(*                                                                     *)
(*  BOTH FORMS ARE KEPT, and deliberately.  The `pobs_tr_eq` form is    *)
(*  what the six refutations refute; deleting it would delete the       *)
(*  record of the finding, and the guards that establish it would have  *)
(*  nothing to be about.  The `pnobs_tr_eq` form is the obligation      *)
(*  B2b.2 inherits.                                                     *)
(*                                                                     *)
(*  NOTHING BELOW IS PROVED, AND NO RELATION BETWEEN THE TWO FORMS IS   *)
(*  CLAIMED.  In particular it is NOT claimed that the nominal form is  *)
(*  weaker, stronger, or implied by the other: neither implication is   *)
(*  established here and neither is obvious.  `pobs_tr_eq` demands the  *)
(*  final values be EQUAL, which the nominal form does not; the nominal *)
(*  form demands a store correspondence, which `pobs_tr_eq` does not;   *)
(*  and the two quantify over different sets of ambient stacks, since   *)
(*  the nominal form admits only equivariant ones.  What IS checked is  *)
(*  narrower and is in the B2b.1 section below: at the very             *)
(*  configuration where the six refutations bite, the nominal           *)
(*  observation's CONSEQUENT holds, with the world exhibited -- and     *)
(*  that configuration satisfies the nominal observation's hypotheses,  *)
(*  so the difference is not obtained by excluding it.                  *)
(*                                                                     *)
(*  B2b.3 UPDATE: THE NOMINAL FORM IS FALSE OF `ref_ops` TOO, AND THE   *)
(*  SIX NEGATIONS ARE PROVED (`guard_nom_b2b3_verdict`).  The repair    *)
(*  did what it was made to do -- the counter, the number of contexts   *)
(*  allocated and the NAMES of the handles are all beyond the reach of  *)
(*  the new counterexamples, and one of the six does not mention a      *)
(*  world at all -- and the laws fail for a different reason, which is  *)
(*  recorded at the B2b.3 section.  Still no relation is claimed        *)
(*  between the two forms in either direction.                          *)
(*                                                                     *)
(*  `ops` still appears, unchanged: a law is still a proposition ABOUT  *)
(*  AN IMPLEMENTATION.  What has moved is `lk` and `apply`, which are   *)
(*  now fields of the boundary record, because the observation needs    *)
(*  them together with the clause relation they must respect.           *)
(* ================================================================== *)

let law_left_identity_nom
    (#v #cl: Type)
    (b: pboundary v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (g: pval v -> pcomp v cl)
  : GTot prop
  = pnobs_tr_eq b
      (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_extend pl cx g))
      (ops.o_enter pl (g x))

let law_right_identity_nom
    (#v #cl: Type)
    (b: pboundary v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pnobs_tr_eq b
      (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
      (ops.o_enter pl c)

let law_assoc_nom
    (#v #cl: Type)
    (b: pboundary v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
    (cx: pval v)
    (g h: pval v -> pcomp v cl)
  : GTot prop
  = pnobs_tr_eq b
      (pbind (ops.o_extend_ctx pl cx g) (fun cy -> ops.o_extend pl cy h))
      (ops.o_extend pl cx (fun x -> pbind (g x) h))
    /\
    pnobs_tr_eq b
      (pbind (ops.o_enter_ctx pl c)
             (fun c0 -> pbind (ops.o_extend_ctx pl c0 g)
                              (fun cy -> ops.o_extend pl cy h)))
      (PSplice (plan_enter_frames pl) (pbind (pbind c g) h))

let law_resume_matches_continuation_nom
    (#v #cl: Type)
    (b: pboundary v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (x: pval v)
    (k: pval v -> pcomp v cl)
  : GTot prop
  = pnobs_tr_eq b
      (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_resume pl cx k))
      (PSplice (plan_resume_frames pl) (k x))

let law_transparent_agrees_nom
    (#v #cl: Type)
    (b: pboundary v cl)
    (ops: ctx_ops v cl)
    (pl: plan v cl)
    (c: pcomp v cl)
  : GTot prop
  = pnobs_tr_eq b
      (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
      (PSplice (plan_enter_frames pl) c)

(** **The five retargeted statements are WELL TYPED at `prop`, and that is the
    ONLY thing this states.** They are not proved, not partially proved, and no
    fixture, transition or other definition in this file depends on any of them
    holding -- exactly as with the five they are retargeted from.

    **B2b.3 DECIDES THEM, AND THE ANSWER IS NO.** All six propositions the five
    make up are FALSE of `ref_ops` under the repaired observation, and every
    negation is PROVED -- `guard_nom_b2b3_verdict`. This comment is left standing
    because what it says is still true of THIS gate: nothing here proves them,
    and nothing here depends on them. See the B2b.3 section at the end of the
    file for the counterexamples and for what they localise. *)
let guard_nom_laws_are_statable
    (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl) (pl: plan v cl)
    (c: pcomp v cl) (x: pval v) (cxv: pval v) (g h k: pval v -> pcomp v cl)
  : Lemma (law_left_identity_nom b ops pl x g == law_left_identity_nom b ops pl x g /\
           law_right_identity_nom b ops pl c == law_right_identity_nom b ops pl c /\
           law_assoc_nom b ops pl c cxv g h == law_assoc_nom b ops pl c cxv g h /\
           law_resume_matches_continuation_nom b ops pl x k
             == law_resume_matches_continuation_nom b ops pl x k /\
           law_transparent_agrees_nom b ops pl c
             == law_transparent_agrees_nom b ops pl c)
  = ()

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
  | FEmits                       (* resume twice, EMITTING around each -- B1.8  *)

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

(** The two inner layers of B1.8's emitting clause, NAMED. They are top-level so
    that `lemma_femits_wb` can peel the well-scopedness judgement one node at a
    time; written inline, the nesting is five index decrements deep and the
    judgement would need enough fuel to unfold all five at once. *)
let femits_out (r1: pval fv) (r2: pval fv) : pcomp fv fcl
  = PEmit "cl-out" (fret (FL [fseen r1; fseen r2]))

let femits_mid (kf: pval fv -> pcomp fv fcl) (r1: pval fv) : pcomp fv fcl
  = PEmit "cl-mid" (POp (kf (fpv (FS "e2"))) (femits_out r1))

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
  // **B1.8, for gate condition 6.** The only clause here whose body contains a
  // `PEmit`. Three events of the CLAUSE INTERPRETER's own, in order, with a
  // resumption between each pair -- so a fixture over it reads both the order of
  // the interpreter's emissions and the multiplicity of everything the
  // resumptions re-run. Without it, "an emission raised by `apply` is recorded"
  // would rest on reading `pstep_tr` rather than on running anything.
  | FEmits -> PEmit "cl-in" (POp (k (fpv (FS "e1"))) (femits_mid k))

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
      | "Ev" -> Some (fclause FEmits)
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

(** The table B1.8's condition-6 fixtures hang on an AMBIENT prompt: `"Ev"` and
    nothing else, so the emitting clause is reached by an operation no plan
    prompt and no owner will take. It is a separate table rather than an entry
    added to `ftbl`, so that not one existing fixture's run changes. *)
let ftbl_ev : ptable fcl = { hs = fhs; binds = ["Ev"] }

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

(** **How often an event occurs in a trace.** Multiplicity is half of gate
    condition 6. A list equation fixes order and multiplicity together, which is
    the stronger statement and the one the fixtures below make; this exists so
    that "exactly once" can also be said on its own, of a trace whose full shape
    is not the point. *)
let rec fcount (ev: string) (tr: list string) : Tot nat (decreases tr)
  = match tr with
    | [] -> 0
    | e :: rest -> (if e = ev then 1 else 0) + fcount ev rest

(* ---- B1.8: reading a run as a trace-aware CONVERGENCE ------------- *)

(** The configuration a traced run ends in. It is `frun` -- PROVED, by trace
    erasure, so the fixtures that read `frun` and the ones that read `ftrace` are
    reading the same run and not two runs that happen to agree. *)
let fend (fuel: nat) (c: pcomp fv fcl) : pconf fv fcl
  = fst (prun flook fapply fuel (pload c))

let lemma_fend_is_frun (fuel: nat) (c: pcomp fv fcl)
  : Lemma (ensures fend fuel c == frun fuel c)
  = lemma_prun_erase flook fapply fuel (pload c)

(** The answer as a `pval fv`, total, so that a witness for `pconverges_tr` can be
    WRITTEN DOWN without the fixture having to spell the value out. `fresult`
    renders through `fseen` and is for reading; this is for quantifying. *)
let fdone (cf: pconf fv fcl) : pval fv
  = match cf.st with | PDone y -> y | _ -> PV FU

let lemma_fdone (cf: pconf fv fcl)
  : Lemma (requires PDone? cf.st) (ensures cf.st == PDone (fdone cf))
  = ()

(** **A concrete run, read as a trace-aware convergence.** PROVED. `fuel` occurs
    in the HYPOTHESIS -- it is how the witness is found -- and not in the
    conclusion, which is `pconverges_tr` and quantifies the step count away. That
    is the shape gate condition 3 asks for: a guard may name a fuel to exhibit a
    witness, the RELATION may not name one at all. *)
let lemma_fconverges_tr (c: pcomp fv fcl) (fuel: nat) (tr: list string)
  : Lemma (requires PDone? (fend fuel c).st /\ ftrace fuel c == tr)
          (ensures pconverges_tr flook fapply (pload c) tr (fdone (fend fuel c)))
  = lemma_fdone (fend fuel c);
    introduce exists (n: nat).
        (fst (prun flook fapply n (pload c))).st == PDone (fdone (fend fuel c))
        /\ snd (prun flook fapply n (pload c)) == tr
    with fuel and ()

(** The same run read as a VALUE-only convergence, which is what makes "their
    values agree" a checked statement rather than an aside. PROVED. *)
let lemma_fconverges (c: pcomp fv fcl) (fuel: nat) (x: pval fv)
  : Lemma (requires (fend fuel c).st == PDone x)
          (ensures pconverges flook fapply (pload c) x)
  = lemma_prun_erase flook fapply fuel (pload c);
    introduce exists (n: nat). (psteps flook fapply n (pload c)).st == PDone x
    with fuel and ()

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

(* ---- 12b. THE SAME TWO PROGRAMS, AS A STATEMENT ABOUT THE RELATION.
   GATE CONDITION 5. -------------------------------------------------

   `fixture_11` and `fixture_12` are two RUNS at one fixed fuel. That was B1.6's
   whole answer, and by itself it constrains nothing: a relation is what the laws
   are stated over, and neither fixture is a fact about any relation. What
   follows is.

   The values agree -- checked, below, and it is the reason this could not have
   been done under `pobs_eq`. The traces do not, and `pconverges_tr` converges to
   at most one trace, so the residual program is not below the suspension one and
   the suspension one is not below the residual one. Neither ordering holds, so
   the equivalence does not either, at ANY fuel: the fuel 400 appears only in
   finding the witnesses.

   What this does NOT say, and the distinction matters: it does not say
   `pobs_eq flook fapply prog_traced prog_susp` HOLDS. That is a statement about
   every stack, every store and every counter, and this file does not prove it.
   What is checked is the weaker and sufficient thing -- that at the
   configuration where the traces separate them, the VALUES do not, so the
   separation is not one the value-only relation could have made here. ---- *)

let guard_susp_agrees_on_value () : Lemma
  (ensures pconverges flook fapply (pload prog_traced) (fdone (fend 400 prog_traced))
        /\ pconverges flook fapply (pload prog_susp) (fdone (fend 400 prog_traced)))
  = assert_norm (PDone? (fend 400 prog_traced).st);
    assert_norm (PDone? (fend 400 prog_susp).st);
    assert_norm (fdone (fend 400 prog_traced) == fdone (fend 400 prog_susp));
    lemma_fdone (fend 400 prog_traced);
    lemma_fdone (fend 400 prog_susp);
    lemma_fconverges prog_traced 400 (fdone (fend 400 prog_traced));
    lemma_fconverges prog_susp 400 (fdone (fend 400 prog_traced))

(** The two trace-aware convergences the separation is read off. PROVED. *)
let guard_traced_converges_tr () : Lemma
  (ensures pconverges_tr flook fapply (pload prog_traced)
             ["prefix"; "c1"; "c2"] (fdone (fend 400 prog_traced)))
  = assert_norm (PDone? (fend 400 prog_traced).st);
    assert_norm (ftrace 400 prog_traced == ["prefix"; "c1"; "c2"]);
    lemma_fconverges_tr prog_traced 400 ["prefix"; "c1"; "c2"]

let guard_susp_converges_tr () : Lemma
  (ensures pconverges_tr flook fapply (pload prog_susp)
             ["prefix"; "c1"; "prefix"; "c2"] (fdone (fend 400 prog_susp)))
  = assert_norm (PDone? (fend 400 prog_susp).st);
    assert_norm (ftrace 400 prog_susp == ["prefix"; "c1"; "prefix"; "c2"]);
    lemma_fconverges_tr prog_susp 400 ["prefix"; "c1"; "prefix"; "c2"]

(** **The residual program is NOT below the suspension one.** PROVED. Assume it
    is; the residual's convergence at the trace `["prefix"; "c1"; "c2"]` is then
    also the suspension's, and the suspension already converges at
    `["prefix"; "c1"; "prefix"; "c2"]` -- two traces for one configuration, which
    `lemma_pconverges_tr_unique` forbids. *)
let guard_traced_not_below_susp () : Lemma
  (ensures ~(pobs_tr_le flook fapply prog_traced prog_susp))
  = guard_traced_converges_tr ();
    guard_susp_converges_tr ();
    introduce pobs_tr_le flook fapply prog_traced prog_susp ==> False
    with
      lemma_pconverges_tr_unique flook fapply (pload prog_susp)
        ["prefix"; "c1"; "c2"] ["prefix"; "c1"; "prefix"; "c2"]
        (fdone (fend 400 prog_traced)) (fdone (fend 400 prog_susp))

(** And not above it either. PROVED, by the same argument in the other
    direction. *)
let guard_susp_not_below_traced () : Lemma
  (ensures ~(pobs_tr_le flook fapply prog_susp prog_traced))
  = guard_traced_converges_tr ();
    guard_susp_converges_tr ();
    introduce pobs_tr_le flook fapply prog_susp prog_traced ==> False
    with
      lemma_pconverges_tr_unique flook fapply (pload prog_traced)
        ["prefix"; "c1"; "prefix"; "c2"] ["prefix"; "c1"; "c2"]
        (fdone (fend 400 prog_susp)) (fdone (fend 400 prog_traced))

(**
 * **GATE CONDITION 5, AS A THEOREM ABOUT THE RELATION.** PROVED.
 *
 * The residual representation and the withdrawn suspension representation are
 * NOT equivalent under the trace-aware relation, in either direction, while
 * `guard_susp_agrees_on_value` checks that they converge to the SAME VALUE. So
 * the separation is genuinely the trace's doing: it is the observable the
 * value-only relation does not have, and it is why retargeting the laws is a
 * strengthening with content rather than a change of notation.
 *)
let guard_trace_separates_residual_from_suspension () : Lemma
  (ensures ~(pobs_tr_eq flook fapply prog_traced prog_susp)
        /\ ~(pobs_tr_eq flook fapply prog_susp prog_traced))
  = guard_traced_not_below_susp ();
    guard_susp_not_below_traced ()

(* ---- 12c. EMISSIONS RAISED BY THE AMBIENT STACK AND BY THE CLAUSE
   INTERPRETER, WITH ORDER AND MULTIPLICITY. GATE CONDITION 6. --------

   `pstep_tr` intercepts the `PEmit` NODE and does not ask where the node came
   from, so it is tempting to call this condition true by construction. It is
   not enough: "by construction" is a reading of a definition, and what is asked
   for is ORDER and MULTIPLICITY, which no reading of `pstep_tr` supplies. Both
   are properties of the list `prun` builds with `@`, and the only way to have
   them is to run something.

   Neither emission below is reachable from the term the program wrote. One is
   produced by `apply` -- the `FEmits` clause, whose body emits `"cl-in"`,
   `"cl-mid"` and `"cl-out"` in that order around two resumptions. The other is
   produced by the value rule at a prompt frame, from an AMBIENT prompt's return
   clause. A program that named either directly would be testing nothing.

     - `prog_clause_emits` has no return clause, so its trace is the
       interpreter's three events with the resumed body's `"leaf"` between them.
       The interpreter's order and the resumption's multiplicity, separately
       legible.
     - `prog_ambient_emits` adds the emitting return clause, and `"amb-ret"`
       appears TWICE -- once per resumption, because `pfind_prompt` captures the
       prompt along with the segment and a resumption re-installs it. The
       multiplicity of an ambient emission is the multiplicity of the resumption
       that caused it, and the trace says so.
     - `prog_amb_scope` puts a whole scope between the operation and the ambient
       handler. The scope's consumer emits `"c2"` and it appears twice, for the
       same reason and one level out: the captured segment contains the scope
       floor, so resuming re-installs the entire scope above the ambient
       handler's pending frames. That is B1.6's requirement 6 read on the trace
       instead of on the answer -- and note that this is a prefix that runs
       twice WITHOUT any residual being consumed twice. It is the ambient
       handler that asked for it, so it is not the defect `fixture_11` is about;
       `guard_amb_scope_prefix_once` records the difference. ---- *)

let body_amb : pcomp fv fcl =
  POp (PPerform "Ev" "e" [fpv (FS "v")])
      (fun x -> PEmit "leaf" (fret (FL [FS "leaf"; fseen x])))

(** An AMBIENT prompt's return clause that emits. It is the only `pret` in this
    file with a `PEmit` in it, and it is what makes "the stack raised it" a case
    distinct from "the program did". *)
let famb_ret : option (pval fv -> pcomp fv fcl) =
  Some (fun x -> PEmit "amb-ret" (fret (FL [FS "amb-ret"; fseen x])))

let prog_clause_emits : pcomp fv fcl = PHandle ftbl_ev None PMono body_amb
let prog_ambient_emits : pcomp fv fcl = PHandle ftbl_ev famb_ret PMono body_amb
let prog_amb_scope : pcomp fv fcl =
  PHandle ftbl_ev famb_ret PMono
    (fscope plan_L body_amb (fun cx -> resume_at_C plan_L cx fc2))

let fixture_23_ambient_and_clause_emissions () : Lemma
  (ensures ftrace 200 prog_clause_emits
             == ["cl-in"; "leaf"; "cl-mid"; "leaf"; "cl-out"]
        /\ ftrace 200 prog_ambient_emits
             == ["cl-in"; "leaf"; "amb-ret"; "cl-mid"; "leaf"; "amb-ret"; "cl-out"]
        /\ ftrace 800 prog_amb_scope
             == ["cl-in"; "leaf"; "c2"; "amb-ret";
                 "cl-mid"; "leaf"; "c2"; "amb-ret"; "cl-out"])
  = assert_norm (ftrace 200 prog_clause_emits
                 == ["cl-in"; "leaf"; "cl-mid"; "leaf"; "cl-out"]);
    assert_norm (ftrace 200 prog_ambient_emits
                 == ["cl-in"; "leaf"; "amb-ret"; "cl-mid"; "leaf"; "amb-ret"; "cl-out"]);
    assert_norm (ftrace 800 prog_amb_scope
                 == ["cl-in"; "leaf"; "c2"; "amb-ret";
                     "cl-mid"; "leaf"; "c2"; "amb-ret"; "cl-out"])

(** **The multiplicities, independently.** PROVED, as counts on the trace:
    `"leaf"` -- the last thing the protected prefix does before the token is
    produced -- appears exactly as often as the ambient handler resumed, and
    each of the clause's own events appears the number of times it should.
    Counts are checked here rather than asserted in prose.

    **What a count cannot show, and where that comes from instead.** These
    equations say how many of each event the whole run emitted. They do not say
    WHERE the events fell, so they do not on their own establish that no single
    production contains two `"leaf"`s. That is an ordering fact and it comes
    from `fixture_23`'s exact trace, which pins the whole sequence; this guard
    fixes the multiplicities beside it. The two together are what say "once per
    production" -- neither says it alone. *)
let guard_amb_scope_prefix_once () : Lemma
  (ensures fcount "leaf" (ftrace 800 prog_amb_scope) == 2
        /\ fcount "c2" (ftrace 800 prog_amb_scope) == 2
        /\ fcount "cl-in" (ftrace 800 prog_amb_scope) == 1
        /\ fcount "cl-mid" (ftrace 800 prog_amb_scope) == 1
        /\ fcount "cl-out" (ftrace 800 prog_amb_scope) == 1
        /\ fcount "amb-ret" (ftrace 800 prog_amb_scope) == 2)
  = assert_norm (fcount "leaf" (ftrace 800 prog_amb_scope) == 2);
    assert_norm (fcount "c2" (ftrace 800 prog_amb_scope) == 2);
    assert_norm (fcount "cl-in" (ftrace 800 prog_amb_scope) == 1);
    assert_norm (fcount "cl-mid" (ftrace 800 prog_amb_scope) == 1);
    assert_norm (fcount "cl-out" (ftrace 800 prog_amb_scope) == 1);
    assert_norm (fcount "amb-ret" (ftrace 800 prog_amb_scope) == 2)

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


(* ================================================================== *)
(*  B2a, strand 2: NON-VACUITY                                         *)
(*                                                                     *)
(*  An invariant that excluded the programs this machine is meant to    *)
(*  run would prove nothing about it, and the initial-term condition    *)
(*  `pterm_wb` and the interpreter condition `papply_wb` are the two    *)
(*  places that could go wrong that way. Both are CHECKED here rather   *)
(*  than asserted in prose: `papply_wb` for the fixtures' own clause    *)
(*  interpreter, and `pterm_wb` for each fixture program the ledger at  *)
(*  the end of this section names -- one lemma each. That ledger is    *)
(*  maintained by hand and nothing checks it is complete; see its own   *)
(*  doc comment.                                                        *)
(*                                                                     *)
(*  WHAT THE CHECK FOUND, and it is a result rather than a formality:   *)
(*  every LEDGERED program satisfies the condition, and most satisfy    *)
(*  it TRIVIALLY. `pterm_wb` looks at a `PEnterCtx` and at the three    *)
(*  consuming nodes and asks nothing at all, so a program built out of  *)
(*  scopes and binds discharges by `()`. The only programs with an      *)
(*  obligation are the three built on a raw `PSplice` -- `prog6_enter`, *)
(*  `prog1old` and `prog_susp` -- which is the judgement's own doc       *)
(*  comment seen from the other side.                                   *)
(*                                                                     *)
(*  `PWeave` IS MEASURED AT THE JUDGEMENT, NOT AT AN EXECUTION. No      *)
(*  fixture builds a `PWeave`, because this prototype has no dispatch   *)
(*  that produces one (see the module header), so there is no RUN to    *)
(*  measure `pints_wb` against and there will not be one before B3.     *)
(*  What there is instead is a pair of type-level guards --             *)
(*  `guard_wb_weave_accepts` and `guard_wb_weave_rejects` -- which      *)
(*  differ in the return clause alone and pin that the condition admits *)
(*  a Family prompt carrying a real return clause and refuses a         *)
(*  malformed one. That makes `pints_wb` a condition about this machine *)
(*  rather than a hypothesis the preservation proof carries along, and  *)
(*  it is as far as a judgement can be measured without a program.      *)
(* ================================================================== *)

(* ---- The equations, as rewrite rules, AT THE FIXTURES' TYPES ------ *)
(*                                                                     *)
(*  Checking three dozen concrete programs by hand would be three       *)
(*  dozen chains of the equations above, and the chains would be the    *)
(*  only thing a reader could not check by reading. These give Z3 the   *)
(*  equations as rewrites instead, so each program's check is `()`.     *)
(*                                                                     *)
(*  They are declared HERE, at the very end of the file and only at     *)
(*  `fv`/`fcl`, so that no proof above this line is affected by them:   *)
(*  an SMT pattern is global from its declaration onwards, and every    *)
(*  theorem of the development is already checked by the time these     *)
(*  appear. Each is PROVED, by the corresponding equation.              *)

let pat_wb_var (x: pval fv)
  : Lemma (pterm_wb (PVar x <: pcomp fv fcl))
          [SMTPat (pterm_wb (PVar x <: pcomp fv fcl))]
  = lemma_wb_trivial (PVar x <: pcomp fv fcl)

let pat_wb_perform (eff op: string) (payload: list (pval fv))
  : Lemma (pterm_wb (PPerform eff op payload <: pcomp fv fcl))
          [SMTPat (pterm_wb (PPerform eff op payload <: pcomp fv fcl))]
  = lemma_wb_trivial (PPerform eff op payload <: pcomp fv fcl)

let pat_wb_readp (l: string)
  : Lemma (pterm_wb (PReadP l <: pcomp fv fcl))
          [SMTPat (pterm_wb (PReadP l <: pcomp fv fcl))]
  = lemma_wb_trivial (PReadP l <: pcomp fv fcl)

let pat_wb_enterctx (pl: plan fv fcl) (body: pcomp fv fcl)
  : Lemma (pterm_wb (PEnterCtx pl body))
          [SMTPat (pterm_wb (PEnterCtx pl body))]
  = lemma_wb_trivial (PEnterCtx pl body <: pcomp fv fcl)

let pat_wb_extend (pl: plan fv fcl) (h: pval fv) (g: pval fv -> pcomp fv fcl)
  : Lemma (pterm_wb (PExtendC pl h g))
          [SMTPat (pterm_wb (PExtendC pl h g))]
  = lemma_wb_trivial (PExtendC pl h g <: pcomp fv fcl)

let pat_wb_extend_ctx (pl: plan fv fcl) (h: pval fv) (g: pval fv -> pcomp fv fcl)
  : Lemma (pterm_wb (PExtendCtxC pl h g))
          [SMTPat (pterm_wb (PExtendCtxC pl h g))]
  = lemma_wb_trivial (PExtendCtxC pl h g <: pcomp fv fcl)

let pat_wb_resume (pl: plan fv fcl) (h: pval fv) (kk: pval fv -> pcomp fv fcl)
  : Lemma (pterm_wb (PResumeC pl h kk))
          [SMTPat (pterm_wb (PResumeC pl h kk))]
  = lemma_wb_trivial (PResumeC pl h kk <: pcomp fv fcl)

let pat_wb_op (inner: pcomp fv fcl) (fn: pval fv -> pcomp fv fcl)
  : Lemma (pterm_wb (POp inner fn)
           <==> (pterm_wb inner /\ (forall (x: pval fv). pterm_wb (fn x))))
          [SMTPat (pterm_wb (POp inner fn))]
  = lemma_wb_op inner fn

let pat_wb_emit (ev: string) (body: pcomp fv fcl)
  : Lemma (pterm_wb (PEmit ev body) <==> pterm_wb body)
          [SMTPat (pterm_wb (PEmit ev body))]
  = introduce pterm_wb (PEmit ev body) ==> pterm_wb body
    with lemma_wb_emit_fwd ev body;
    introduce pterm_wb body ==> pterm_wb (PEmit ev body)
    with lemma_wb_emit_bwd ev body

let pat_wb_handle
    (tbl: ptable fcl) (ret: option (pval fv -> pcomp fv fcl))
    (prov: prompt_provenance) (body: pcomp fv fcl)
  : Lemma (pterm_wb (PHandle tbl ret prov body) <==> (pret_wb ret /\ pterm_wb body))
          [SMTPat (pterm_wb (PHandle tbl ret prov body))]
  = introduce pterm_wb (PHandle tbl ret prov body) ==> (pret_wb ret /\ pterm_wb body)
    with lemma_wb_handle_fwd tbl ret prov body;
    introduce (pret_wb ret /\ pterm_wb body) ==> pterm_wb (PHandle tbl ret prov body)
    with lemma_wb_handle_bwd tbl ret prov body

(* `pret_wb None` needs no rule: it unfolds to `True` in one step. *)

let pat_wb_ret_some (r: pval fv -> pcomp fv fcl)
  : Lemma (pret_wb (Some r) <==> (forall (x: pval fv). pterm_wb (r x)))
          [SMTPat (pret_wb (Some r))]
  = introduce pret_wb (Some r) ==> (forall (x: pval fv). pterm_wb (r x))
    with lemma_wb_ret_some_fwd r;
    introduce (forall (x: pval fv). pterm_wb (r x)) ==> pret_wb (Some r)
    with lemma_wb_ret_some_bwd r

(* ---- The two return clauses the fixtures install ----------------- *)

let guard_fown_ret_wb () : Lemma (pret_wb fown_ret) = ()
let guard_fouter_ret_wb () : Lemma (pret_wb fouter_ret) = ()

(* ---- The condition on the clause interpreter, DISCHARGED ---------- *)

(**
 * **`papply_wb fapply`.** PROVED, and it is the check that the condition imposed
 * on the FFI parameter is one a real interpreter meets.
 *
 * Every clause of `fapply` builds its result out of `POp`, the continuation it
 * was handed, a `PPerform` and values, and none of those constrains anything. A
 * clause that returned a raw `PSplice` of a frame list of its own would be the
 * interesting case, and it is exactly the case the condition exists to exclude;
 * no real clause has one, because a clause has no frames to splice that the
 * machine did not hand it as `kf`.
 *)
(** **The emitting clause satisfies the condition too.** PROVED, by peeling the
    judgement one node at a time with the defining equations rather than by
    asking for enough fuel to unfold five of them at once. `PEmit` is a
    node like any other here: it constrains nothing and passes the judgement
    straight through to its body, which is why an emitting interpreter is not a
    special case of anything. *)
let lemma_femits_wb (kf: pval fv -> pcomp fv fcl)
  : Lemma (requires forall (x: pval fv). pterm_wb (kf x))
          (ensures pterm_wb (PEmit "cl-in" (POp (kf (fpv (FS "e1"))) (femits_mid kf))))
  = introduce forall (r1: pval fv). pterm_wb (femits_mid kf r1)
    with
      (introduce forall (r2: pval fv). pterm_wb (femits_out r1 r2)
       with lemma_wb_emit_bwd #fv #fcl "cl-out" (fret (FL [fseen r1; fseen r2]));
       lemma_wb_op_bwd (kf (fpv (FS "e2"))) (femits_out r1);
       lemma_wb_emit_bwd #fv #fcl "cl-mid"
         (POp (kf (fpv (FS "e2"))) (femits_out r1)));
    lemma_wb_op_bwd (kf (fpv (FS "e1"))) (femits_mid kf);
    lemma_wb_emit_bwd #fv #fcl "cl-in" (POp (kf (fpv (FS "e1"))) (femits_mid kf))

let lemma_fapply_wb_at (c: fcl) (payload: list (pval fv)) (kf: pval fv -> pcomp fv fcl)
  : Lemma (requires forall (x: pval fv). pterm_wb (kf x))
          (ensures pterm_wb (fapply c payload kf))
  = match c with
    | FEcho -> (match payload with | x :: _ -> () | [] -> ())
    | FAbort _ -> ()
    | FTwice _ _ -> ()
    | FRetry -> ()
    | FBetween -> ()
    | FWrap -> ()
    | FEmits -> lemma_femits_wb kf

let guard_fapply_wb () : Lemma (papply_wb fapply)
  = introduce forall (c: fcl) (payload: list (pval fv)) (kf: (pval fv -> pcomp fv fcl)).
      (forall (x: pval fv). pterm_wb (kf x)) ==> pterm_wb (fapply c payload kf)
    with (introduce (forall (x: pval fv). pterm_wb (kf x))
                    ==> pterm_wb (fapply c payload kf)
          with lemma_fapply_wb_at c payload kf)

(* ---- The three programs built on a raw `PSplice` ------------------ *)

(** The shape every `plan_enter_frames` in this file has: two prompts and nothing
    else. PROVED. *)
let lemma_wb_frames_two_prompts
    (t1: ptable fcl) (r1: option (pval fv -> pcomp fv fcl)) (p1: prompt_provenance)
    (t2: ptable fcl) (r2: option (pval fv -> pcomp fv fcl)) (p2: prompt_provenance)
  : Lemma (requires pret_wb r1 /\ pret_wb r2)
          (ensures pframes_wb [PPromptF t1 r1 p1; PPromptF t2 r2 p2])
  = lemma_wb_frames_nil #fv #fcl ();
    lemma_wb_frame_prompt_bwd t2 r2 p2;
    lemma_wb_frames_cons_bwd (PPromptF t2 r2 p2) ([] <: pstack fv fcl);
    lemma_wb_frame_prompt_bwd t1 r1 p1;
    lemma_wb_frames_cons_bwd (PPromptF t1 r1 p1) [PPromptF t2 r2 p2]

(** The prefix `fixture_1` lengthens is judged at every length. PROVED, by
    induction on the length. *)
let rec lemma_pchain_wb (n: nat) (c: pcomp fv fcl)
  : Lemma (requires pterm_wb c) (ensures pterm_wb (pchain n c)) (decreases n)
  = if n = 0 then () else lemma_pchain_wb (n - 1) c

let lemma_body1_wb (n: nat) : Lemma (ensures pterm_wb (body1 n))
  = lemma_pchain_wb
      n (POp (PPerform "Two" "flip" [])
             (fun (x: pval fv) -> fret (FL [FS "leaf"; fseen x])))

let guard_wb_prog6_enter () : Lemma (pterm_wb prog6_enter)
  = lemma_wb_ret_none #fv #fcl ();
    lemma_wb_frames_two_prompts ftbl None PMono ftbl None PFamily;
    assert_norm (plan_enter_frames plan_T
                 == [PPromptF ftbl None PMono; PPromptF ftbl None PFamily]);
    assert_norm (pwb (plan_enter_frames plan_T));
    assert_norm (panswered (plan_enter_frames plan_T) == false);
    lemma_wb_splice_bwd (plan_enter_frames plan_T) body6

let lemma_plan_L_enter_frames_wb () : Lemma (pframes_wb (plan_enter_frames plan_L))
  = lemma_wb_ret_none #fv #fcl ();
    guard_fown_ret_wb ();
    lemma_wb_frames_two_prompts ftbl None PFamily ftbl fown_ret PFamily;
    assert_norm (plan_enter_frames plan_L
                 == [PPromptF ftbl None PFamily; PPromptF ftbl fown_ret PFamily])

let lemma_plan_L_resume_frames_wb () : Lemma (pframes_wb (plan_resume_frames plan_L))
  = lemma_wb_ret_none #fv #fcl ();
    guard_fown_ret_wb ();
    lemma_wb_frames_two_prompts ftbl None PFamily ftbl fown_ret PFamily;
    assert_norm (plan_resume_frames plan_L
                 == [PPromptF ftbl None PFamily; PPromptF ftbl fown_ret PFamily])

let guard_wb_prog1old (n: nat) : Lemma (pterm_wb (prog1old n))
  = lemma_body1_wb n;
    lemma_plan_L_enter_frames_wb ();
    lemma_plan_L_resume_frames_wb ();
    assert_norm (pwb (plan_enter_frames plan_L));
    assert_norm (panswered (plan_enter_frames plan_L) == false);
    assert_norm (pwb (plan_resume_frames plan_L));
    assert_norm (panswered (plan_resume_frames plan_L) == false);
    lemma_wb_splice_bwd (plan_enter_frames plan_L) (pbind (body1 n) (PVar #fv #fcl));
    lemma_wb_splice_bwd (plan_resume_frames plan_L) (pbind (body1 n) fk)

let guard_wb_prog_susp () : Lemma (pterm_wb prog_susp)
  = lemma_plan_L_enter_frames_wb ();
    lemma_plan_L_resume_frames_wb ();
    assert_norm (pwb (plan_enter_frames plan_L));
    assert_norm (panswered (plan_enter_frames plan_L) == false);
    assert_norm (pwb (plan_resume_frames plan_L));
    assert_norm (panswered (plan_resume_frames plan_L) == false);
    lemma_wb_splice_bwd (plan_enter_frames plan_L) (pbind body_e fc1);
    lemma_wb_splice_bwd (plan_resume_frames plan_L) (pbind body_e fc2)

(* ---- Every other fixture program, one lemma each ------------------ *)

let guard_wb_prog1new (n: nat) : Lemma (pterm_wb (prog1new n)) = ()
let guard_wb_prog2 () : Lemma (pterm_wb prog2) = ()
let guard_wb_prog2_probe () : Lemma (pterm_wb prog2_probe) = ()
let guard_wb_prog3a () : Lemma (pterm_wb prog3a) = ()
let guard_wb_prog3b () : Lemma (pterm_wb prog3b) = ()
let guard_wb_prog4 () : Lemma (pterm_wb prog4) = ()
let guard_wb_prog5 () : Lemma (pterm_wb prog5) = ()
let guard_wb_prog5_probe () : Lemma (pterm_wb prog5_probe) = ()
let guard_wb_prog5b () : Lemma (pterm_wb prog5b) = ()
let guard_wb_prog6_residual () : Lemma (pterm_wb prog6_residual) = ()
let guard_wb_prog7 () : Lemma (pterm_wb prog7) = ()
let guard_wb_prog8 () : Lemma (pterm_wb prog8) = ()
let guard_wb_prog8b () : Lemma (pterm_wb prog8b) = ()
let guard_wb_prog_out () : Lemma (pterm_wb prog_out) = ()
let guard_wb_prog_silent () : Lemma (pterm_wb prog_silent) = ()
let guard_wb_prog_traced () : Lemma (pterm_wb prog_traced) = ()
let guard_wb_prog_traced2 () : Lemma (pterm_wb prog_traced2) = ()
let guard_wb_prog_nested () : Lemma (pterm_wb prog_nested) = ()
let guard_wb_prog_two_floors () : Lemma (pterm_wb prog_two_floors) = ()
let guard_wb_prog16 () : Lemma (pterm_wb prog16) = ()
let guard_wb_prog17 () : Lemma (pterm_wb prog17) = ()
let guard_wb_prog18_outer () : Lemma (pterm_wb prog18_outer) = ()
let guard_wb_prog18_inner () : Lemma (pterm_wb prog18_inner) = ()
let guard_wb_prog19_good () : Lemma (pterm_wb prog19_good) = ()
let guard_wb_prog19_forged () : Lemma (pterm_wb prog19_forged) = ()
let guard_wb_prog19_notahandle () : Lemma (pterm_wb prog19_notahandle) = ()
(* Six binds deep under three nested handle binders. This is the one place where
   the rewrite rules do not close on their own -- not for want of fuel, but
   because Z3 will not push the instantiation under three quantified handles at
   once. The inner three binds are proved once, over arbitrary handles, and the
   outer three then close. *)
let lemma_prog20_inner_wb (cx cy1 cy2: pval fv)
  : Lemma (pterm_wb (POp (resume_at_C plan_L0 cy1 fk)
                         (fun (a: pval fv) ->
                            POp (resume_at_C plan_L0 cy2 fk)
                                (fun (b: pval fv) ->
                                   POp (resume_at_C plan_L0 cx fk)
                                       (fun (c: pval fv) ->
                                          fret (FL [fseen a; fseen b; fseen c]))))))
  = ()

let lemma_prog20_rev_inner_wb (cx cy1 cy2: pval fv)
  : Lemma (pterm_wb (POp (resume_at_C plan_L0 cy2 fk)
                         (fun (b: pval fv) ->
                            POp (resume_at_C plan_L0 cy1 fk)
                                (fun (a: pval fv) ->
                                   POp (resume_at_C plan_L0 cx fk)
                                       (fun (c: pval fv) ->
                                          fret (FL [fseen a; fseen b; fseen c]))))))
  = ()

let guard_wb_prog20 () : Lemma (pterm_wb prog20)
  = introduce forall (cx: pval fv) (cy1: pval fv) (cy2: pval fv).
      pterm_wb (POp (resume_at_C plan_L0 cy1 fk)
                    (fun (a: pval fv) ->
                       POp (resume_at_C plan_L0 cy2 fk)
                           (fun (b: pval fv) ->
                              POp (resume_at_C plan_L0 cx fk)
                                  (fun (c: pval fv) ->
                                     fret (FL [fseen a; fseen b; fseen c])))))
    with lemma_prog20_inner_wb cx cy1 cy2

let guard_wb_prog20_rev () : Lemma (pterm_wb prog20_rev)
  = introduce forall (cx: pval fv) (cy1: pval fv) (cy2: pval fv).
      pterm_wb (POp (resume_at_C plan_L0 cy2 fk)
                    (fun (b: pval fv) ->
                       POp (resume_at_C plan_L0 cy1 fk)
                           (fun (a: pval fv) ->
                              POp (resume_at_C plan_L0 cx fk)
                                  (fun (c: pval fv) ->
                                     fret (FL [fseen a; fseen b; fseen c])))))
    with lemma_prog20_rev_inner_wb cx cy1 cy2
let guard_wb_prog20_handles () : Lemma (pterm_wb prog20_handles) = ()
let guard_wb_prog21_handles () : Lemma (pterm_wb prog21_handles) = ()
let guard_wb_prog21_consume () : Lemma (pterm_wb prog21_consume) = ()
let guard_wb_prog_sep () : Lemma (pterm_wb prog_sep) = ()
let guard_wb_prog9_resume () : Lemma (pterm_wb (resume_at_C plan_L (PCtxKey 0) fk)) = ()
let guard_wb_prog9_extend () : Lemma (pterm_wb (extend_at_C plan_L (PCtxKey 0) fk)) = ()
let guard_wb_prog9_extend_ctx ()
  : Lemma (pterm_wb (extend_ctx_at_C plan_L (PCtxKey 0) fk)) = ()

(* ---- B1.8's three condition-6 programs, and the emitting return
   clause they hang on. The `PEmit` inside `famb_ret` is why these get
   the defining equations by hand rather than a bare `()`: the
   judgement has to be peeled through the emission node, and the
   default fuel unfolds two levels, not three. ---------------------- *)

let guard_famb_ret_wb () : Lemma (pret_wb famb_ret)
  = introduce forall (x: pval fv). pterm_wb (PEmit "amb-ret" (fret (FL [FS "amb-ret"; fseen x])))
    with lemma_wb_emit_bwd #fv #fcl "amb-ret" (fret (FL [FS "amb-ret"; fseen x]));
    lemma_wb_ret_some_bwd (fun (x: pval fv) ->
      PEmit "amb-ret" (fret (FL [FS "amb-ret"; fseen x])))

let guard_wb_body_amb () : Lemma (pterm_wb body_amb)
  = introduce forall (x: pval fv). pterm_wb (PEmit "leaf" (fret (FL [FS "leaf"; fseen x])))
    with lemma_wb_emit_bwd #fv #fcl "leaf" (fret (FL [FS "leaf"; fseen x]));
    lemma_wb_op_bwd (PPerform "Ev" "e" [fpv (FS "v")])
                    (fun (x: pval fv) -> PEmit "leaf" (fret (FL [FS "leaf"; fseen x])))

let guard_wb_prog_clause_emits () : Lemma (pterm_wb prog_clause_emits)
  = guard_wb_body_amb ();
    lemma_wb_ret_none #fv #fcl ();
    lemma_wb_handle_bwd ftbl_ev None PMono body_amb

let guard_wb_prog_ambient_emits () : Lemma (pterm_wb prog_ambient_emits)
  = guard_wb_body_amb ();
    guard_famb_ret_wb ();
    lemma_wb_handle_bwd ftbl_ev famb_ret PMono body_amb

let guard_wb_prog_amb_scope () : Lemma (pterm_wb prog_amb_scope)
  = guard_famb_ret_wb ();
    lemma_wb_handle_bwd ftbl_ev famb_ret PMono
      (fscope plan_L body_amb (fun cx -> resume_at_C plan_L cx fc2))

(* ---- The list, so that the claim is one statement ---------------- *)

let rec pterm_wb_all (#v #cl: Type) (l: list (pcomp v cl)) : Tot prop (decreases l)
  = match l with
    | [] -> True
    | c :: rest -> pterm_wb c /\ pterm_wb_all rest

(** The check composes over `@`. PROVED, and it is what lets the list below be
    checked in blocks: forty programs in one query is forty rewrites of the
    judgement inside one term, which Z3 does not finish. *)
let rec lemma_pterm_wb_all_append (#v #cl: Type) (l1 l2: list (pcomp v cl))
  : Lemma (requires pterm_wb_all l1 /\ pterm_wb_all l2)
          (ensures pterm_wb_all (l1 @ l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: rest -> lemma_pterm_wb_all_append rest l2

(* ================================================================== *)
(*  B2b: THE FIVE LAWS ARE FALSE OF `ref_ops`, AND THE REASON IS THE   *)
(*  OBSERVATION RELATION RATHER THAN THE ALGEBRA                       *)
(*                                                                     *)
(*  This section is a FINDING and not a repair. Not one law's statement *)
(*  is amended, not one is weakened by a hypothesis, and not one is     *)
(*  restated over a different relation. What is added is the           *)
(*  counterexample, CHECKED, together with the evidence that the        *)
(*  configuration it lives at is one the machine can actually be in --  *)
(*  because that is the one thing that would have made the failure an   *)
(*  artefact rather than a result.                                      *)
(*                                                                     *)
(*  THE ARGUMENT, IN THREE SENTENCES.                                   *)
(*                                                                     *)
(*  `pobs_tr_le` fixes the store and the counter at the START of both   *)
(*  runs and compares the `pval v` at the END. `pval v` contains        *)
(*  `PCtxKey i`, and `palloc` hands out `cf.next` and increments -- so  *)
(*  a program that produces a context and returns its handle observes   *)
(*  EXACTLY HOW MANY CONTEXTS WERE ALLOCATED BEFORE IT RAN. Every one   *)
(*  of the five laws has a left-hand side that produces or extends a    *)
(*  context and a right-hand side that does not, so the two sides       *)
(*  differ by at least one allocation, and any continuation that        *)
(*  afterwards produces a context of its own reports the difference as  *)
(*  its answer.                                                         *)
(*                                                                     *)
(*  NOTHING ABOUT THIS IS A DEFECT OF THE OPERATIONS. `ref_ops` does    *)
(*  what the design says it should: production allocates, and it must,  *)
(*  because a handle has to name something in the store. The           *)
(*  discrepancy is that `pobs_tr_eq` treats the NAME as observable. Two *)
(*  runs that agree on everything a program could compute from its      *)
(*  answers, and differ only in which natural number a handle carries,  *)
(*  are counted as different observations.                              *)
(*                                                                     *)
(*  WHAT IS *NOT* CLAIMED HERE, AND IT IS THE STRONGER STATEMENT.       *)
(*  This section does NOT establish that allocation counting is the     *)
(*  ONLY reason the laws fail. The two sides of `law_right_identity`    *)
(*  also run the inner computation under DIFFERENT frame lists --       *)
(*  `plan_protocol_frames pl` beneath a `PModeF MExtend` on the left,   *)
(*  `plan_enter_frames pl` on the right -- and whether those agree is a *)
(*  bisimulation this file does not attempt and does not settle. The    *)
(*  counterexample below decides the laws as stated; it does not decide *)
(*  what would remain if the observation were made insensitive to       *)
(*  handle names. That is stated, not proved, and it is the open        *)
(*  question this finding hands on.                                    *)
(*                                                                     *)
(*  THE AMENDMENT IS NOT MADE. Two are available -- observe only        *)
(*  answers in the image of `PV`, or quotient the observation by a      *)
(*  store isomorphism -- and each changes what the five laws CLAIM.     *)
(*  Choosing between them is a design decision about the relation and   *)
(*  is deliberately left open here; see the header's list of what this  *)
(*  file states rather than proves.                                     *)
(* ================================================================== *)

(** **The smallest plan there is**: no layers, and an owner with no return
    clause. It is used because the counterexample has nothing to do with layers
    -- the smaller the plan, the more clearly the failure is about allocation and
    not about a projection -- and because at it `plan_enter_frames`,
    `plan_resume_frames` and `plan_protocol_frames` are the SAME one-frame list,
    so the two sides of every law below differ in nothing except which
    transitions they take. *)
let plan_A : plan fv fcl = Plan [] fowner_plain

let guard_plan_A_projections_agree ()
  : Lemma (plan_enter_frames plan_A == plan_resume_frames plan_A /\
           plan_protocol_frames plan_A == plan_enter_frames plan_A /\
           plan_enter_frames plan_A == [PPromptF ftbl None PFamily])
  = assert_norm (plan_enter_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (plan_resume_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (plan_protocol_frames plan_A == [PPromptF ftbl None PFamily])

let fone : pval fv = fpv (FI 1)

(** **The ambient continuation that reads the counter, and the ONLY thing in the
    counterexample that is not forced.** It produces a context of its own and
    returns the handle -- an entirely ordinary program, with nothing forged and
    nothing smuggled: the handle it returns is one the run allocated.

    It is a NAMED top-level function rather than a lambda so that the frame
    `PBindF fnew_ctx` is one SMT symbol wherever it appears. *)
let fnew_ctx (_: pval fv) : pcomp fv fcl = PEnterCtx plan_A (PVar (fpv (FI 2)))

let fk_new : pstack fv fcl = [PBindF fnew_ctx]

(**
 * **The two sides, and they serve THREE of the five laws at once.**
 *
 * At `pl = plan_A`, `x = fone` and `g = PVar`, `law_left_identity`'s two sides
 * are literally `law_right_identity`'s at `c = PVar fone`, and literally
 * `law_transparent_agrees`'s at the same `c` -- because `ops.o_enter pl c` IS
 * `PSplice (plan_enter_frames pl) c` for `ref_ops`, and because the left-hand
 * side of the second and the fifth is the same term. That coincidence is not
 * arranged: it is what it means for the three laws to be about one identity read
 * three ways, and it means one pair of programs refutes three propositions.
 *)
let ce_l : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx plan_A (PVar fone))
        (fun cx -> ref_ops.o_extend plan_A cx (PVar #fv #fcl))

let ce_r : pcomp fv fcl = ref_ops.o_enter plan_A (PVar fone)

(** The configuration each side is compared at: the ambient stack above, the
    EMPTY store, and the counter at ZERO -- which is to say `pload`'s own store
    and counter. Nothing here is a store the machine could not have; it is the
    store the machine STARTS with. *)
let ce_cf_l : pconf fv fcl = { st = PStep ce_l fk_new; store = []; next = 0 }
let ce_cf_r : pconf fv fcl = { st = PStep ce_r fk_new; store = []; next = 0 }

(**
 * **THE CONFIGURATION IS ONE STEP FROM A LOADED PROGRAM.** PROVED, by
 * unfolding, and it is the guard that decides the question the gate flags.
 *
 * `pobs_tr_le` quantifies over an arbitrary stack, store and counter and does
 * NOT require `pconf_wf`, so a law could in principle fail only at
 * configurations the machine can never be in -- and a failure of that kind would
 * say something about the relation's domain rather than about the operations. It
 * is not that kind here: `ce_prog_l` and `ce_prog_r` are closed programs, and
 * ONE transition from `pload` of each is exactly the configuration the
 * refutations below use.
 *)
let ce_prog_l : pcomp fv fcl = pbind ce_l fnew_ctx
let ce_prog_r : pcomp fv fcl = pbind ce_r fnew_ctx

let guard_ce_conf_one_step_from_pload ()
  : Lemma (pstep flook fapply (pload ce_prog_l) == ce_cf_l /\
           pstep flook fapply (pload ce_prog_r) == ce_cf_r)
  = ()

(**
 * **AND IT IS WELL FORMED, IN EVERY SENSE B2a GAVE THE WORD.** PROVED, through
 * `lemma_pload_ok` and one transition of the preservation theorem -- so the
 * conclusion is not an assertion about these two configurations but an instance
 * of the invariant the machine maintains.
 *
 * `pconf_ok` is freshness, the store-residual invariant and the stack condition
 * together, so this closes off the second reading of the gate's stop condition as
 * well: the counterexample is not standing on a residual no production could
 * have built, because its store is empty.
 *)
let guard_ce_conf_ok ()
  : Lemma (pconf_ok ce_cf_l /\ pconf_ok ce_cf_r)
  = guard_fapply_wb ();
    lemma_wb_ret_none #fv #fcl ();
    lemma_wb_frames_nil #fv #fcl ();
    lemma_wb_trivial (PVar fone <: pcomp fv fcl);
    lemma_wb_frame_prompt_bwd #fv #fcl ftbl None PFamily;
    lemma_wb_frames_cons_bwd #fv #fcl (PPromptF ftbl None PFamily) [];
    assert_norm (plan_enter_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (pwb (plan_enter_frames plan_A));
    assert_norm (panswered (plan_enter_frames plan_A) == false);
    lemma_wb_splice_bwd (plan_enter_frames plan_A) (PVar fone);
    lemma_pload_ok ce_prog_l;
    lemma_pload_ok ce_prog_r;
    lemma_pstep_conf_ok flook fapply (pload ce_prog_l);
    lemma_pstep_conf_ok flook fapply (pload ce_prog_r);
    guard_ce_conf_one_step_from_pload ()

(**
 * **THE RUNS, side by side.** PROVED by `assert_norm`, which is to say by
 * running the machine.
 *
 * Both settle, both settle silently -- the trace is empty on both sides, so the
 * separation is NOT the trace-aware half of the relation doing the work -- and
 * they settle on two different handles. The left-hand side produced a context, so
 * the ambient continuation's own production got key `1`; the right-hand side
 * produced none, so it got key `0`.
 *)
let guard_ce_runs_differ ()
  : Lemma ((fst (prun flook fapply 200 ce_cf_l)).st == PDone (PCtxKey 1) /\
           snd (prun flook fapply 200 ce_cf_l) == [] /\
           (fst (prun flook fapply 200 ce_cf_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook fapply 200 ce_cf_r) == [])
  = assert_norm ((fst (prun flook fapply 200 ce_cf_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_r) == [])

(** **The ordering fails, left to right.** PROVED, from the two runs and
    uniqueness of the observation. This is the single fact all three refutations
    below rest on; each of them adds only the identification of its law's two
    sides with `ce_l` and `ce_r`. *)
let guard_ce_not_below ()
  : Lemma (~(pobs_tr_eq flook fapply ce_l ce_r))
  = guard_ce_runs_differ ();
    lemma_pconverges_tr_at flook fapply ce_cf_l 200 [] (PCtxKey 1);
    lemma_pconverges_tr_refuse flook fapply ce_cf_r 200 (PCtxKey 0) [] (PCtxKey 1);
    lemma_not_pobs_tr_le flook fapply ce_l ce_r fk_new [] 0 [] (PCtxKey 1);
    lemma_not_pobs_tr_eq flook fapply ce_l ce_r

(* ---- The identifications, and why they need a tactic ------------- *)
(*                                                                     *)
(*  Each law BUILDS a lambda inside its own definition -- the          *)
(*  `fun cx -> ops.o_extend pl cx g` that receives the handle -- and    *)
(*  F* gives a lambda occurring in a definition an SMT encoding of its  *)
(*  own, so Z3 cannot see that it is the same function as the one       *)
(*  written here. It is the trap `lemma_ctx_drive_answers_head`         *)
(*  documents, met a second time, and the answer is the same: normalise *)
(*  until the two terms are IDENTICAL and close by reflexivity, with no *)
(*  SMT query.                                                         *)
(*                                                                     *)
(*  `delta_only` and not full normalisation. Unfolding `pobs_tr_eq`     *)
(*  would drag `pconverges_tr` and `prun` under two quantifiers, and    *)
(*  the resulting term is large enough that the equality fails -- it    *)
(*  was tried. Naming exactly the symbols that stand between a law and  *)
(*  its two programs leaves the relation untouched on both sides, and   *)
(*  the goal closes on a term a reader can hold in their head.          *)
(* ------------------------------------------------------------------ *)

(** **`law_left_identity` IS FALSE OF `ref_ops`.** PROVED -- the negation is
    proved, not the law left unproved. *)
let guard_ref_ops_refutes_left_identity ()
  : Lemma (~(law_left_identity flook fapply ref_ops plan_A fone (PVar #fv #fcl)))
  = guard_ce_not_below ();
    assert (law_left_identity flook fapply ref_ops plan_A fone (PVar #fv #fcl)
            == pobs_tr_eq flook fapply ce_l ce_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_left_identity; `%ce_l; `%ce_r; `%ref_ops;
                       `%enter_ctx_C; `%extend_at_C; `%enter_C; `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(** **`law_right_identity` IS FALSE OF `ref_ops`.** PROVED, at the same pair:
    `PVar` is the inner monad's `pure`, and extending by it is what the left-hand
    side does either way. *)
let guard_ref_ops_refutes_right_identity ()
  : Lemma (~(law_right_identity flook fapply ref_ops plan_A (PVar fone)))
  = guard_ce_not_below ();
    assert (law_right_identity flook fapply ref_ops plan_A (PVar fone)
            == pobs_tr_eq flook fapply ce_l ce_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_right_identity; `%ce_l; `%ce_r; `%ref_ops;
                       `%enter_ctx_C; `%extend_at_C; `%enter_C; `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(** **`law_transparent_agrees` IS FALSE OF `ref_ops`** -- and note that it is
    refuted AT A PLAN WITH NO LAYERS, so at a plan every one of whose layers is
    transparent for want of any layer at all. PROVED. The gap it exhibits is
    therefore not about transparency: it is the same allocation the other two
    laws trip over. *)
let guard_ref_ops_refutes_transparent_agrees ()
  : Lemma (~(law_transparent_agrees flook fapply ref_ops plan_A (PVar fone)))
  = guard_ce_not_below ();
    assert (law_transparent_agrees flook fapply ref_ops plan_A (PVar fone)
            == pobs_tr_eq flook fapply ce_l ce_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_transparent_agrees; `%ce_l; `%ce_r; `%ref_ops;
                       `%enter_ctx_C; `%extend_at_C; `%enter_C; `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(* ---- The fourth law, whose right-hand side is ANCHORED ----------- *)
(*                                                                     *)
(*  `law_resume_matches_continuation` is one of the two laws written    *)
(*  against an INDEPENDENT description of what it is a law of -- the    *)
(*  plan's resume projection, not the operations -- so it is the law    *)
(*  the design leans on hardest. It fails for the same reason as the    *)
(*  purely algebraic three, and that is the point worth recording: the  *)
(*  anchoring is not what breaks. A left-hand side that produces a      *)
(*  context is compared with a right-hand side that does not, so the    *)
(*  counter separates them before the resumption's own behaviour is     *)
(*  reached at all.                                                     *)
(* ------------------------------------------------------------------ *)

let ce_rm_l : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx plan_A (PVar fone))
        (fun cx -> ref_ops.o_resume plan_A cx (PVar #fv #fcl))

let ce_rm_r : pcomp fv fcl = PSplice (plan_resume_frames plan_A) (PVar fone)

let ce_cf_rm_l : pconf fv fcl = { st = PStep ce_rm_l fk_new; store = []; next = 0 }
let ce_cf_rm_r : pconf fv fcl = { st = PStep ce_rm_r fk_new; store = []; next = 0 }

let ce_prog_rm_l : pcomp fv fcl = pbind ce_rm_l fnew_ctx
let ce_prog_rm_r : pcomp fv fcl = pbind ce_rm_r fnew_ctx

(** One step from a loaded program, exactly as before. PROVED. *)
let guard_ce_rm_one_step_from_pload ()
  : Lemma (pstep flook fapply (pload ce_prog_rm_l) == ce_cf_rm_l /\
           pstep flook fapply (pload ce_prog_rm_r) == ce_cf_rm_r)
  = ()

(** And well formed. PROVED, by the same route. *)
let guard_ce_rm_conf_ok ()
  : Lemma (pconf_ok ce_cf_rm_l /\ pconf_ok ce_cf_rm_r)
  = guard_fapply_wb ();
    lemma_wb_ret_none #fv #fcl ();
    lemma_wb_frames_nil #fv #fcl ();
    lemma_wb_trivial (PVar fone <: pcomp fv fcl);
    lemma_wb_frame_prompt_bwd #fv #fcl ftbl None PFamily;
    lemma_wb_frames_cons_bwd #fv #fcl (PPromptF ftbl None PFamily) [];
    assert_norm (plan_resume_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (pwb (plan_resume_frames plan_A));
    assert_norm (panswered (plan_resume_frames plan_A) == false);
    lemma_wb_splice_bwd (plan_resume_frames plan_A) (PVar fone);
    lemma_pload_ok ce_prog_rm_l;
    lemma_pload_ok ce_prog_rm_r;
    lemma_pstep_conf_ok flook fapply (pload ce_prog_rm_l);
    lemma_pstep_conf_ok flook fapply (pload ce_prog_rm_r);
    guard_ce_rm_one_step_from_pload ()

let guard_ce_rm_runs_differ ()
  : Lemma ((fst (prun flook fapply 200 ce_cf_rm_l)).st == PDone (PCtxKey 1) /\
           snd (prun flook fapply 200 ce_cf_rm_l) == [] /\
           (fst (prun flook fapply 200 ce_cf_rm_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook fapply 200 ce_cf_rm_r) == [])
  = assert_norm ((fst (prun flook fapply 200 ce_cf_rm_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_rm_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_rm_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_rm_r) == [])

(** **`law_resume_matches_continuation` IS FALSE OF `ref_ops`.** PROVED. *)
let guard_ref_ops_refutes_resume ()
  : Lemma (~(law_resume_matches_continuation flook fapply ref_ops plan_A fone
                                             (PVar #fv #fcl)))
  = guard_ce_rm_runs_differ ();
    lemma_pconverges_tr_at flook fapply ce_cf_rm_l 200 [] (PCtxKey 1);
    lemma_pconverges_tr_refuse flook fapply ce_cf_rm_r 200 (PCtxKey 0) [] (PCtxKey 1);
    lemma_not_pobs_tr_le flook fapply ce_rm_l ce_rm_r fk_new [] 0 [] (PCtxKey 1);
    lemma_not_pobs_tr_eq flook fapply ce_rm_l ce_rm_r;
    assert (law_resume_matches_continuation flook fapply ref_ops plan_A fone
                                            (PVar #fv #fcl)
            == pobs_tr_eq flook fapply ce_rm_l ce_rm_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_resume_matches_continuation; `%ce_rm_l; `%ce_rm_r;
                       `%ref_ops; `%enter_ctx_C; `%resume_at_C; `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(* ---- `law_assoc`, BOTH CONJUNCTS, separately -------------------- *)
(*                                                                     *)
(*  The two halves fail at two DIFFERENT configurations and it is       *)
(*  worth keeping them apart, because the algebraic half is the only    *)
(*  statement among the six that names a context it did not itself      *)
(*  produce. Its `cx` is quantified, so `pobs_tr_le`'s quantification    *)
(*  over the STORE is what ranges over what `cx` resolves to -- and a   *)
(*  refutation there has to be careful that the store it picks is one   *)
(*  the machine could have. It is: the store below is LITERALLY the     *)
(*  store a run left behind, and `ce_cx` is LITERALLY the handle that   *)
(*  run returned.                                                       *)
(* ------------------------------------------------------------------ *)

(** The production whose store the algebraic half is refuted at. Nothing is
    written by hand: `ce_sto` and `ce_nxt` are projections of an actual run. *)
let ce_prod : pconf fv fcl = frun 30 (PEnterCtx plan_A (PVar fone))
let ce_sto : pstore fv fcl = ce_prod.store
let ce_nxt : nat = ce_prod.next
let ce_cx : pval fv = PCtxKey 0

(** **The run really did return `ce_cx` and really did leave the counter at one.**
    PROVED by running it. *)
let guard_ce_prod ()
  : Lemma (ce_prod.st == PDone ce_cx /\ ce_nxt == 1)
  = assert_norm (ce_prod.st == PDone (PCtxKey 0));
    assert_norm (ce_nxt == 1)

let ce_aa_l : pcomp fv fcl =
  pbind (ref_ops.o_extend_ctx plan_A ce_cx (PVar #fv #fcl))
        (fun cy -> ref_ops.o_extend plan_A cy (PVar #fv #fcl))

let ce_aa_r : pcomp fv fcl =
  ref_ops.o_extend plan_A ce_cx (fun x -> pbind (PVar x) (PVar #fv #fcl))

let ce_cf_aa_l : pconf fv fcl =
  { st = PStep ce_aa_l fk_new; store = ce_sto; next = ce_nxt }
let ce_cf_aa_r : pconf fv fcl =
  { st = PStep ce_aa_r fk_new; store = ce_sto; next = ce_nxt }

(**
 * **THE ALGEBRAIC HALF'S CONFIGURATION IS REACHED BY A CLOSED PROGRAM.** PROVED,
 * by running five transitions of one.
 *
 * This is the strongest form of the reachability answer and it is available here
 * because the store the half needs is the store a production leaves: the program
 * produces a context, binds its handle, and goes on with the law's left-hand side
 * at that handle. The configuration the refutation names is what the fifth
 * transition reaches -- store, counter and stack together, not merely each of
 * them separately.
 *)
let ce_prog_aa_l : pcomp fv fcl =
  pbind (PEnterCtx plan_A (PVar fone)) (fun _ -> pbind ce_aa_l fnew_ctx)
let ce_prog_aa_r : pcomp fv fcl =
  pbind (PEnterCtx plan_A (PVar fone)) (fun _ -> pbind ce_aa_r fnew_ctx)

let guard_ce_aa_reachable ()
  : Lemma (psteps flook fapply 5 (pload ce_prog_aa_l) == ce_cf_aa_l /\
           psteps flook fapply 5 (pload ce_prog_aa_r) == ce_cf_aa_r)
  = assert_norm (psteps flook fapply 5 (pload ce_prog_aa_l) == ce_cf_aa_l);
    assert_norm (psteps flook fapply 5 (pload ce_prog_aa_r) == ce_cf_aa_r)

let guard_ce_aa_runs_differ ()
  : Lemma ((fst (prun flook fapply 200 ce_cf_aa_l)).st == PDone (PCtxKey 2) /\
           snd (prun flook fapply 200 ce_cf_aa_l) == [] /\
           (fst (prun flook fapply 200 ce_cf_aa_r)).st == PDone (PCtxKey 1) /\
           snd (prun flook fapply 200 ce_cf_aa_r) == [])
  = assert_norm ((fst (prun flook fapply 200 ce_cf_aa_l)).st == PDone (PCtxKey 2));
    assert_norm (snd (prun flook fapply 200 ce_cf_aa_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_aa_r)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_aa_r) == [])

(** **THE ALGEBRAIC HALF OF `law_assoc` IS FALSE OF `ref_ops`.** PROVED, at the
    two programs the half compares -- `o_extend_ctx` ALLOCATES, which is condition
    8 working exactly as designed, and the composite extension does not. *)
let guard_ref_ops_refutes_assoc_algebraic ()
  : Lemma (~(pobs_tr_eq flook fapply ce_aa_l ce_aa_r))
  = guard_ce_aa_runs_differ ();
    lemma_pconverges_tr_at flook fapply ce_cf_aa_l 200 [] (PCtxKey 2);
    lemma_pconverges_tr_refuse flook fapply ce_cf_aa_r 200 (PCtxKey 1) [] (PCtxKey 2);
    lemma_not_pobs_tr_le flook fapply ce_aa_l ce_aa_r fk_new ce_sto ce_nxt []
                         (PCtxKey 2);
    lemma_not_pobs_tr_eq flook fapply ce_aa_l ce_aa_r

let ce_ac_l : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx plan_A (PVar fone))
        (fun c0 -> pbind (ref_ops.o_extend_ctx plan_A c0 (PVar #fv #fcl))
                         (fun cy -> ref_ops.o_extend plan_A cy (PVar #fv #fcl)))

let ce_ac_r : pcomp fv fcl =
  PSplice (plan_enter_frames plan_A)
          (pbind (pbind (PVar fone) (PVar #fv #fcl)) (PVar #fv #fcl))

let ce_cf_ac_l : pconf fv fcl = { st = PStep ce_ac_l fk_new; store = []; next = 0 }
let ce_cf_ac_r : pconf fv fcl = { st = PStep ce_ac_r fk_new; store = []; next = 0 }

let ce_prog_ac_l : pcomp fv fcl = pbind ce_ac_l fnew_ctx
let ce_prog_ac_r : pcomp fv fcl = pbind ce_ac_r fnew_ctx

let guard_ce_ac_one_step_from_pload ()
  : Lemma (pstep flook fapply (pload ce_prog_ac_l) == ce_cf_ac_l /\
           pstep flook fapply (pload ce_prog_ac_r) == ce_cf_ac_r)
  = ()

let guard_ce_ac_runs_differ ()
  : Lemma ((fst (prun flook fapply 200 ce_cf_ac_l)).st == PDone (PCtxKey 2) /\
           snd (prun flook fapply 200 ce_cf_ac_l) == [] /\
           (fst (prun flook fapply 200 ce_cf_ac_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook fapply 200 ce_cf_ac_r) == [])
  = assert_norm ((fst (prun flook fapply 200 ce_cf_ac_l)).st == PDone (PCtxKey 2));
    assert_norm (snd (prun flook fapply 200 ce_cf_ac_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_ac_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_ac_r) == [])

(** **THE ANCHORED HALF OF `law_assoc` IS FALSE OF `ref_ops`.** PROVED, and its
    left-hand side allocates TWICE -- once producing and once extending -- against
    a right-hand side that allocates not at all, so the two are two apart rather
    than one. *)
let guard_ref_ops_refutes_assoc_anchored ()
  : Lemma (~(pobs_tr_eq flook fapply ce_ac_l ce_ac_r))
  = guard_ce_ac_runs_differ ();
    lemma_pconverges_tr_at flook fapply ce_cf_ac_l 200 [] (PCtxKey 2);
    lemma_pconverges_tr_refuse flook fapply ce_cf_ac_r 200 (PCtxKey 0) [] (PCtxKey 2);
    lemma_not_pobs_tr_le flook fapply ce_ac_l ce_ac_r fk_new [] 0 [] (PCtxKey 2);
    lemma_not_pobs_tr_eq flook fapply ce_ac_l ce_ac_r

(** **`law_assoc` IS FALSE OF `ref_ops`, AND BOTH ITS CONJUNCTS ARE.** PROVED.
    The law is a conjunction, so either half would do; both are refuted above and
    the identification below names both, so nothing is being carried by one half
    that the other could not have carried. *)
let guard_ref_ops_refutes_assoc ()
  : Lemma (~(law_assoc flook fapply ref_ops plan_A (PVar fone) ce_cx
                       (PVar #fv #fcl) (PVar #fv #fcl)))
  = guard_ref_ops_refutes_assoc_algebraic ();
    guard_ref_ops_refutes_assoc_anchored ();
    assert (law_assoc flook fapply ref_ops plan_A (PVar fone) ce_cx
                      (PVar #fv #fcl) (PVar #fv #fcl)
            == (pobs_tr_eq flook fapply ce_aa_l ce_aa_r /\
                pobs_tr_eq flook fapply ce_ac_l ce_ac_r))
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_assoc; `%ce_aa_l; `%ce_aa_r; `%ce_ac_l; `%ce_ac_r;
                       `%ref_ops; `%enter_ctx_C; `%extend_at_C; `%extend_ctx_at_C;
                       `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(* ================================================================== *)
(*  THE CONSEQUENCE THAT MATTERS MOST: THE LAWS AS STATED DISCRIMINATE *)
(*  NOTHING                                                            *)
(*                                                                     *)
(*  The five laws exist to SEPARATE implementations. The block comment  *)
(*  before them records the intended separation -- `pointwise_ops`      *)
(*  refused by all four, `flat_ops` refused by the two anchored ones -- *)
(*  and the note on `flat_ops` argues at length why not every law may   *)
(*  be anchored, on pain of collapsing "these are the laws" into        *)
(*  "`ops == ref_ops`".                                                 *)
(*                                                                     *)
(*  THAT ARGUMENT IS NOW MOOT, AND THE TWO GUARDS BELOW ARE WHY. The    *)
(*  same counterexample refuses `pointwise_ops` and `flat_ops` as well  *)
(*  as `ref_ops`, so `law_left_identity` is false of ALL THREE          *)
(*  implementations the file defines. A proposition false of every      *)
(*  candidate distinguishes none of them, whatever it was written to    *)
(*  say -- so the refutations below are NOT the refutations the design  *)
(*  wanted, and it would be a serious misreading to record them as      *)
(*  such. They hold for a reason that has nothing to do with plans:     *)
(*  each of the three allocates on the left and does not on the right.  *)
(*                                                                     *)
(*  Two further honesty notes, both of which cut against reading the    *)
(*  guards as evidence about the algebras.                              *)
(*                                                                     *)
(*  AT `plan_A`, `flat_ops` AND `ref_ops` ARE THE SAME FUNCTIONS on the *)
(*  two sides this law compares. `plan_A` has no layers, so             *)
(*  `flat_ops`'s `owner_only` is the identity on it and its `o_enter`   *)
(*  splices the owner frame `plan_enter_frames` would have produced --   *)
(*  the identification below is `trefl`, not a proof about behaviour.    *)
(*  `flat_ops` is wrong about PLANS WITH LAYERS and this says nothing   *)
(*  whatever about that.                                                *)
(*                                                                     *)
(*  `pointwise_ops` DOES differ here -- its extension splices           *)
(*  `plan_enter_frames` around each leaf -- and it is still refused for *)
(*  the allocation reason and not for that one: its run below reaches   *)
(*  the SAME handle `ref_ops` reaches, `PCtxKey 1`, so the extra        *)
(*  crossing of the layers is invisible at this plan and contributes    *)
(*  nothing to the refusal.                                             *)
(*                                                                     *)
(*  WHETHER ANY LAW WOULD STILL SEPARATE THE THREE UNDER AN AMENDED     *)
(*  RELATION IS NOT ESTABLISHED HERE, in either direction.              *)
(* ================================================================== *)

let ce_pw_l : pcomp fv fcl =
  pbind (pointwise_ops.o_enter_ctx plan_A (PVar fone))
        (fun cx -> pointwise_ops.o_extend plan_A cx (PVar #fv #fcl))

let ce_cf_pw_l : pconf fv fcl = { st = PStep ce_pw_l fk_new; store = []; next = 0 }
let ce_prog_pw_l : pcomp fv fcl = pbind ce_pw_l fnew_ctx

let guard_ce_pw_one_step_from_pload ()
  : Lemma (pstep flook fapply (pload ce_prog_pw_l) == ce_cf_pw_l)
  = ()

(** **`pointwise_ops` reaches the SAME handle `ref_ops` does.** PROVED by
    running it, and it is the fact that makes the refusal below uninformative
    about the algebra: the two implementations are separated from the right-hand
    side by the same one allocation, and not from each other at all. *)
let guard_ce_pw_run ()
  : Lemma ((fst (prun flook fapply 200 ce_cf_pw_l)).st == PDone (PCtxKey 1) /\
           snd (prun flook fapply 200 ce_cf_pw_l) == [])
  = assert_norm ((fst (prun flook fapply 200 ce_cf_pw_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_pw_l) == [])

(** **`law_left_identity` IS FALSE OF `pointwise_ops` TOO.** PROVED. Read the
    block comment above before reading this as a separation. *)
let guard_pointwise_ops_refutes_left_identity ()
  : Lemma (~(law_left_identity flook fapply pointwise_ops plan_A fone
                               (PVar #fv #fcl)))
  = guard_ce_pw_run ();
    guard_ce_runs_differ ();
    lemma_pconverges_tr_at flook fapply ce_cf_pw_l 200 [] (PCtxKey 1);
    lemma_pconverges_tr_refuse flook fapply ce_cf_r 200 (PCtxKey 0) [] (PCtxKey 1);
    lemma_not_pobs_tr_le flook fapply ce_pw_l ce_r fk_new [] 0 [] (PCtxKey 1);
    lemma_not_pobs_tr_eq flook fapply ce_pw_l ce_r;
    assert (law_left_identity flook fapply pointwise_ops plan_A fone (PVar #fv #fcl)
            == pobs_tr_eq flook fapply ce_pw_l ce_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_left_identity; `%ce_pw_l; `%ce_r; `%pointwise_ops;
                       `%ref_ops; `%enter_ctx_C; `%enter_C; `%pbind];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(** **`law_left_identity` IS FALSE OF `flat_ops` TOO** -- a law the design did
    NOT expect to refuse it, being purely algebraic. PROVED, and the proof is the
    identification alone: at `plan_A` the two sides ARE `ce_l` and `ce_r`, so
    there is no second run to do. That the identification goes through by
    reflexivity is exactly the warning in the block comment above. *)
let guard_flat_ops_refutes_left_identity ()
  : Lemma (~(law_left_identity flook fapply flat_ops plan_A fone (PVar #fv #fcl)))
  = guard_ce_not_below ();
    assert (law_left_identity flook fapply flat_ops plan_A fone (PVar #fv #fcl)
            == pobs_tr_eq flook fapply ce_l ce_r)
    by (FStar.Tactics.V2.norm
          [delta_only [`%law_left_identity; `%ce_l; `%ce_r; `%flat_ops; `%ref_ops;
                       `%enter_ctx_C; `%extend_at_C; `%enter_C; `%pbind;
                       `%plan_A; `%plan_enter_frames; `%enter_layer_frames;
                       `%owner_frame];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(* ---- The counterexample programs meet the initial-term condition -- *)
(*                                                                     *)
(*  They are loaded programs, so they belong in the ledger below, and   *)
(*  the ledger is why this block is here rather than at the end of the  *)
(*  file. Only the two SPLICING sides need anything said about them:    *)
(*  `PSplice` is the one node the judgement constrains, and the frames  *)
(*  it constrains are `plan_A`'s single prompt.                          *)
(* ------------------------------------------------------------------ *)

(** The one prompt `plan_A` projects to, judged once for all three
    projections -- which are the same list, by
    `guard_plan_A_projections_agree`. PROVED. *)
let lemma_ce_frames_wb ()
  : Lemma (pwb (plan_enter_frames plan_A) /\
           pframes_wb (plan_enter_frames plan_A) /\
           panswered (plan_enter_frames plan_A) == false /\
           pwb (plan_resume_frames plan_A) /\
           pframes_wb (plan_resume_frames plan_A) /\
           panswered (plan_resume_frames plan_A) == false)
  = lemma_wb_ret_none #fv #fcl ();
    lemma_wb_frames_nil #fv #fcl ();
    lemma_wb_frame_prompt_bwd #fv #fcl ftbl None PFamily;
    lemma_wb_frames_cons_bwd #fv #fcl (PPromptF ftbl None PFamily) [];
    assert_norm (plan_enter_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (plan_resume_frames plan_A == [PPromptF ftbl None PFamily]);
    assert_norm (pwb (plan_enter_frames plan_A));
    assert_norm (pwb (plan_resume_frames plan_A));
    assert_norm (panswered (plan_enter_frames plan_A) == false);
    assert_norm (panswered (plan_resume_frames plan_A) == false)

let lemma_ce_r_wb () : Lemma (pterm_wb ce_r)
  = lemma_ce_frames_wb ();
    lemma_wb_trivial (PVar fone <: pcomp fv fcl);
    lemma_wb_splice_bwd (plan_enter_frames plan_A) (PVar fone)

let lemma_ce_rm_r_wb () : Lemma (pterm_wb ce_rm_r)
  = lemma_ce_frames_wb ();
    lemma_wb_trivial (PVar fone <: pcomp fv fcl);
    lemma_wb_splice_bwd (plan_resume_frames plan_A) (PVar fone)

let lemma_ce_ac_r_wb () : Lemma (pterm_wb ce_ac_r)
  = lemma_ce_frames_wb ();
    introduce forall (x: pval fv). pterm_wb (PVar x <: pcomp fv fcl)
    with lemma_wb_trivial (PVar x <: pcomp fv fcl);
    lemma_wb_op_bwd (PVar fone <: pcomp fv fcl) (PVar #fv #fcl);
    lemma_wb_op_bwd (pbind (PVar fone) (PVar #fv #fcl)) (PVar #fv #fcl);
    lemma_wb_splice_bwd (plan_enter_frames plan_A)
                        (pbind (pbind (PVar fone) (PVar #fv #fcl)) (PVar #fv #fcl))

let guard_wb_ce_prog_l () : Lemma (pterm_wb ce_prog_l) = ()
let guard_wb_ce_prog_pw_l () : Lemma (pterm_wb ce_prog_pw_l) = ()
let guard_wb_ce_prog_rm_l () : Lemma (pterm_wb ce_prog_rm_l) = ()
let guard_wb_ce_prog_ac_l () : Lemma (pterm_wb ce_prog_ac_l) = ()
let guard_wb_ce_prog_aa_l () : Lemma (pterm_wb ce_prog_aa_l) = ()
let guard_wb_ce_prog_aa_r () : Lemma (pterm_wb ce_prog_aa_r) = ()
let guard_wb_ce_prod () : Lemma (pterm_wb (PEnterCtx plan_A (PVar fone))) = ()

let guard_wb_ce_prog_r () : Lemma (pterm_wb ce_prog_r)
  = lemma_ce_r_wb (); lemma_wb_op_bwd ce_r fnew_ctx

let guard_wb_ce_prog_rm_r () : Lemma (pterm_wb ce_prog_rm_r)
  = lemma_ce_rm_r_wb (); lemma_wb_op_bwd ce_rm_r fnew_ctx

let guard_wb_ce_prog_ac_r () : Lemma (pterm_wb ce_prog_ac_r)
  = lemma_ce_ac_r_wb (); lemma_wb_op_bwd ce_ac_r fnew_ctx

let fprogs_1 : list (pcomp fv fcl) =
  [ prog1new 1; prog1new 5; prog1old 1; prog1old 5;
    prog2; prog2_probe; prog3a; prog3b; prog4 ]

let fprogs_2 : list (pcomp fv fcl) =
  [ prog5; prog5_probe; prog5b;
    prog6_enter; prog6_residual; prog7; prog8; prog8b ]

let fprogs_3 : list (pcomp fv fcl) =
  [ prog_out; prog_silent; prog_traced; prog_susp; prog_traced2;
    prog_nested; prog_two_floors; prog16; prog17 ]

let fprogs_4 : list (pcomp fv fcl) =
  [ prog18_outer; prog18_inner;
    prog19_good; prog19_forged; prog19_notahandle;
    prog20; prog20_rev; prog20_handles ]

let fprogs_5 : list (pcomp fv fcl) =
  [ prog21_handles; prog21_consume; prog_sep;
    resume_at_C plan_L (PCtxKey 0) fk;
    extend_at_C plan_L (PCtxKey 0) fk;
    extend_ctx_at_C plan_L (PCtxKey 0) fk ]

(** B1.8's three, added to the ledger BECAUSE THEY BELONG IN IT: each is a closed
    program that `ftrace` runs, which is the ledger's admission criterion. The
    only fixture terms B1.8 adds that are NOT here are `femits_out` and
    `femits_mid`, and they are deliberately absent -- they are fragments of a
    CLAUSE BODY, produced by `apply` and never loaded by `pload`, so the
    initial-term condition is not the condition that applies to them.
    `guard_fapply_wb` is, and `lemma_femits_wb` discharges it. *)
let fprogs_6 : list (pcomp fv fcl) =
  [ prog_clause_emits; prog_ambient_emits; prog_amb_scope ]

(** **The fixture programs, named in one place -- a MANUALLY MAINTAINED
    LEDGER.**

    Nothing checks that this list is complete. A new fixture program that is
    never added here is simply never checked against `pterm_wb`, and the file
    still verifies: there is no naming convention the build enforces and no
    reflection over the module's declarations. So "every fixture program
    satisfies the initial-term condition" is a claim about the programs IN THIS
    LIST, audited by hand, and it stays that way until a build-side name check
    exists to make omission detectable. Keeping the ledger honest is a
    reviewer's job, not the type checker's. *)
(** B2b's nine, added for the same reason B1.8's three were: each is a closed
    program this file LOADS -- `guard_ce_conf_one_step_from_pload`,
    `guard_ce_rm_one_step_from_pload`, `guard_ce_ac_one_step_from_pload` and
    `guard_ce_aa_reachable` all start from `pload` of one, and `ce_prod` runs the
    ninth to completion. The counterexample configurations themselves are NOT
    programs and are not here; what makes them well formed is `guard_ce_conf_ok`
    and `guard_ce_rm_conf_ok`, which are a different statement about a different
    object. *)
let fprogs_7 : list (pcomp fv fcl) =
  [ ce_prog_l; ce_prog_r; ce_prog_rm_l; ce_prog_rm_r;
    ce_prog_aa_l; ce_prog_aa_r; ce_prog_ac_l; ce_prog_ac_r;
    ce_prog_pw_l; PEnterCtx plan_A (PVar fone) ]

(** **B2b.1 ADDS NOTHING TO THIS LEDGER, and the audit is recorded rather than
    left implicit.** The nominal layer introduces no closed program that `pload`
    is applied to: `fk_const`, `fk_const_n` and `fwrap_body` are a CONTINUATION
    and a CLAUSE-BODY fragment -- deliberately absent for the same reason
    `femits_out` and `femits_mid` are -- and `ncl` / `napply` are a clause
    language and its interpreter, which the initial-term condition is not about.
    The four counterexample pairs' programs were already admitted, as
    `fprogs_7`. *)
let fixture_programs : list (pcomp fv fcl) =
  fprogs_1 @ fprogs_2 @ fprogs_3 @ fprogs_4 @ fprogs_5 @ fprogs_6 @ fprogs_7

(* The fuel is for `pterm_wb_all` and for nothing else: a nine-element block
   needs nine unfoldings of a list recursion, and the default is two. Every
   program's own check is at the default fuel, above. *)
#push-options "--fuel 12"
let guard_fprogs_1_wb () : Lemma (pterm_wb_all fprogs_1)
  = guard_wb_prog1new 1; guard_wb_prog1new 5;
    guard_wb_prog1old 1; guard_wb_prog1old 5;
    guard_wb_prog2 (); guard_wb_prog2_probe ();
    guard_wb_prog3a (); guard_wb_prog3b (); guard_wb_prog4 ()

let guard_fprogs_2_wb () : Lemma (pterm_wb_all fprogs_2)
  = guard_wb_prog5 (); guard_wb_prog5_probe (); guard_wb_prog5b ();
    guard_wb_prog6_enter (); guard_wb_prog6_residual ();
    guard_wb_prog7 (); guard_wb_prog8 (); guard_wb_prog8b ()

let guard_fprogs_3_wb () : Lemma (pterm_wb_all fprogs_3)
  = guard_wb_prog_out ();
    guard_wb_prog_silent (); guard_wb_prog_traced ();
    guard_wb_prog_susp (); guard_wb_prog_traced2 ();
    guard_wb_prog_nested (); guard_wb_prog_two_floors ();
    guard_wb_prog16 (); guard_wb_prog17 ()

let guard_fprogs_4_wb () : Lemma (pterm_wb_all fprogs_4)
  = guard_wb_prog18_outer (); guard_wb_prog18_inner ();
    guard_wb_prog19_good (); guard_wb_prog19_forged (); guard_wb_prog19_notahandle ();
    guard_wb_prog20 (); guard_wb_prog20_rev (); guard_wb_prog20_handles ()

let guard_fprogs_5_wb () : Lemma (pterm_wb_all fprogs_5)
  = guard_wb_prog21_handles (); guard_wb_prog21_consume (); guard_wb_prog_sep ();
    guard_wb_prog9_resume (); guard_wb_prog9_extend (); guard_wb_prog9_extend_ctx ()

let guard_fprogs_6_wb () : Lemma (pterm_wb_all fprogs_6)
  = guard_wb_prog_clause_emits (); guard_wb_prog_ambient_emits ();
    guard_wb_prog_amb_scope ()

let guard_fprogs_7_wb () : Lemma (pterm_wb_all fprogs_7)
  = guard_wb_ce_prog_l (); guard_wb_ce_prog_r ();
    guard_wb_ce_prog_rm_l (); guard_wb_ce_prog_rm_r ();
    guard_wb_ce_prog_aa_l (); guard_wb_ce_prog_aa_r ();
    guard_wb_ce_prog_ac_l (); guard_wb_ce_prog_ac_r ();
    guard_wb_ce_prog_pw_l (); guard_wb_ce_prod ()
#pop-options

(** **EVERY FIXTURE PROGRAM SATISFIES THE INITIAL-TERM CONDITION.** PROVED, from
    the lemmas above and nothing else. The two `n`-indexed families are listed at
    the two lengths `fixture_1` actually runs, and `guard_wb_prog1new` and
    `guard_wb_prog1old` are each proved for EVERY `n`. *)
let guard_fixture_programs_wb () : Lemma (pterm_wb_all fixture_programs)
  = guard_fprogs_1_wb (); guard_fprogs_2_wb (); guard_fprogs_3_wb ();
    guard_fprogs_4_wb (); guard_fprogs_5_wb (); guard_fprogs_6_wb ();
    guard_fprogs_7_wb ();
    lemma_pterm_wb_all_append fprogs_6 fprogs_7;
    lemma_pterm_wb_all_append fprogs_5 (fprogs_6 @ fprogs_7);
    lemma_pterm_wb_all_append fprogs_4 (fprogs_5 @ (fprogs_6 @ fprogs_7));
    lemma_pterm_wb_all_append fprogs_3
      (fprogs_4 @ (fprogs_5 @ (fprogs_6 @ fprogs_7)));
    lemma_pterm_wb_all_append fprogs_2
      (fprogs_3 @ (fprogs_4 @ (fprogs_5 @ (fprogs_6 @ fprogs_7))));
    lemma_pterm_wb_all_append fprogs_1
      (fprogs_2 @ (fprogs_3 @ (fprogs_4 @ (fprogs_5 @ (fprogs_6 @ fprogs_7)))))

(* ---- The `PWeave` clause, which no program here reaches ---------- *)

(**
 * **These two guards are about the JUDGEMENT, not about an execution.**
 * `PWeave` remains the one node no fixture program builds -- this prototype
 * has no dispatch that produces one, as the section header above says -- so
 * nothing in the ledger touches `pints_wb`, the condition `pterm_wb` puts on a
 * weave's intervening segment. That is precisely what makes it worth checking
 * separately. A condition nothing exercises is a condition nobody has
 * measured: were `pints_wb` to accept every segment whatsoever, the
 * preservation proof would still go through, having been handed its hypothesis
 * for free, and the ledger above would not notice.
 *
 * `pterm_wb` is a type-level predicate, so it can be measured without a
 * program that runs. These guards measure it at `fv`/`fcl`, on the tables,
 * plans and owner the fixtures already use, in the only two directions that
 * say anything: one weave the condition must ACCEPT and one it must REFUSE.
 * What they would catch is a `pints_wb` that had drifted to `True` -- guard 1
 * would still pass, guard 2 would fail -- or one that had been tightened into
 * something no legitimate segment meets, which guard 1 would catch.
 *)

(**
 * **The intervening segment a legitimate weave carries.** A recorded bind
 * frame, a Family prompt and a transparent one: the shape `plan_layers`
 * classifies and `enter_layer_frames` rebuilds, with the bind frame in front so
 * that the clause `pints_wb` deliberately SKIPS is on the path too.
 *
 * The Family prompt's return clause is `fown_ret`, and that is the point of
 * guard 1 rather than a detail of it. `pints_wb` constrains prompt return
 * clauses and nothing else, and its `None` case is `True` in one step -- so a
 * segment of `None`-returning prompts satisfies the condition without the
 * condition ever looking at a computation, and a guard built that way would
 * pass against `pints_wb = True` just as happily. `fown_ret` is a clause that
 * is actually there, the fixtures' own answer former, and judging it forces the
 * descent into `pterm_wb` on its body that the guard exists to witness.
 *)
let fweave_ints : pstack fv fcl =
  [ PBindF fk; PPromptF ftbl fown_ret PFamily; PPromptF ftbl None PMono ]

let fweave_good : pcomp fv fcl = PWeave "Two" "flip" fweave_ints fowner body6

(** The segment is judged. PROVED, from the `pints_wb` equations and nothing
    else. *)
let guard_wb_weave_ints () : Lemma (pints_wb fweave_ints)
  = lemma_wb_ints_nil #fv #fcl ();
    lemma_wb_ret_none #fv #fcl ();
    lemma_wb_ints_prompt_bwd #fv #fcl ftbl None PMono [];
    guard_fown_ret_wb ();
    lemma_wb_ints_prompt_bwd #fv #fcl ftbl fown_ret PFamily
      [PPromptF ftbl None PMono];
    lemma_wb_ints_other_bwd #fv #fcl (PBindF fk)
      [PPromptF ftbl fown_ret PFamily; PPromptF ftbl None PMono]

let guard_wb_weave_body () : Lemma (pterm_wb body6) = ()

(** **GUARD 1: the condition ACCEPTS the general path.** PROVED. A `PWeave`
    whose intervening segment carries a Family prompt with a return clause that
    is really there satisfies `pterm_wb`. *)
let guard_wb_weave_accepts () : Lemma (pterm_wb fweave_good)
  = guard_wb_weave_ints ();
    guard_fown_ret_wb ();
    guard_wb_weave_body ();
    introduce forall (n: nat). pterm_wb_n n fweave_good
    with (if n = 0 then ()
          else (assert (pints_wb_n n fweave_ints);
                assert (pret_wb_n n fown_ret);
                assert (pterm_wb_n (n - 1) body6)))

(**
 * **The same weave with the return clause broken.** `PSplice [PBoundaryF]` is
 * the shape used elsewhere in this file for exactly this job: a boundary with
 * nothing beneath it that could answer, which is the one thing `pwb` refuses.
 * Everything else about the weave -- the bind frame, the transparent prompt,
 * the owner, the body -- is unchanged from `fweave_good`, so what guard 2
 * separates from guard 1 is the return clause and only the return clause.
 *)
let fweave_bad_clause (x: pval fv) : pcomp fv fcl =
  PSplice [PBoundaryF] (fret (FL [FS "own"; fseen x]))

let fweave_bad_ints : pstack fv fcl =
  [ PBindF fk;
    PPromptF ftbl (Some fweave_bad_clause) PFamily;
    PPromptF ftbl None PMono ]

let fweave_bad : pcomp fv fcl = PWeave "Two" "flip" fweave_bad_ints fowner body6

(** **GUARD 2: the condition REFUSES the broken one.** PROVED, and stated as
    the negation itself rather than as a mutation that is then reverted: from
    `pterm_wb fweave_bad` the forward equations walk down to `pwb [PBoundaryF]`,
    which `assert_norm` computes to `false`. *)
let guard_wb_weave_rejects () : Lemma (~(pterm_wb fweave_bad))
  = assert_norm (pwb ([PBoundaryF] <: pstack fv fcl) == false);
    introduce pterm_wb fweave_bad ==> False
    with
      (lemma_wb_weave_fwd "Two" "flip" fweave_bad_ints fowner body6;
       lemma_wb_ints_other_fwd #fv #fcl (PBindF fk)
         [PPromptF ftbl (Some fweave_bad_clause) PFamily;
          PPromptF ftbl None PMono];
       lemma_wb_ints_prompt_fwd #fv #fcl ftbl (Some fweave_bad_clause) PFamily
         [PPromptF ftbl None PMono];
       lemma_wb_ret_some_fwd fweave_bad_clause;
       assert (pterm_wb (fweave_bad_clause (fpv (FS "x"))));
       lemma_wb_splice_fwd ([PBoundaryF] <: pstack fv fcl)
         (fret (FL [FS "own"; fseen (fpv (FS "x"))])))

(* ---- What the conditions then buy, at the fixtures' types -------- *)

(** **The payoff, applied to the fixtures.** `fixture_9_paused_is_unreachable`
    checks by execution that thirteen named programs settle at one fixed fuel;
    this says that ANY program satisfying the condition -- which, by the list
    above, is every fixture program the ledger names -- never reaches `PPaused`,
    at any fuel whatever. PROVED, by instantiating `lemma_reachable_not_paused` at
    the fixtures' own lookup and interpreter. *)
let guard_fixture_never_paused (fuel: nat) (c: pcomp fv fcl)
  : Lemma (requires pterm_wb c) (ensures ~(PPaused? (frun fuel c).st))
  = guard_fapply_wb ();
    lemma_reachable_not_paused flook fapply fuel c

(** And the store consequence, at the fixtures' types and with NO hypothesis at
    all -- not even `pterm_wb`, and not `papply_wb` either -- because the store
    layer needs none. PROVED. *)
let guard_fixture_residuals_wf (fuel: nat) (c: pcomp fv fcl) (i: nat)
  : Lemma (ensures (match pstore_lookup i (frun fuel c).store with
                    | Some (PCtxRequests _ r _) -> presid_wf r
                    | _ -> True))
  = lemma_reachable_residual_wf flook fapply fuel c i

(* ================================================================== *)
(*  B2b.1: THE SIX COUNTEREXAMPLES, UNDER THE NOMINAL OBSERVATION      *)
(*                                                                     *)
(*  The section above proves the five laws FALSE of `ref_ops` under     *)
(*  `pobs_tr_eq`, at six statements and four pairs of programs, and     *)
(*  identifies the cause as the observation rather than the algebra.    *)
(*  This section carries those same four pairs over to the nominal      *)
(*  observation and exhibits, FOR EACH, the world under which the two   *)
(*  runs' answers correspond.                                          *)
(*                                                                     *)
(*  WHAT IS ESTABLISHED HERE AND WHAT IS NOT.  For each pair this       *)
(*  section proves the body of `pnobs_tr_le` AT THE CONFIGURATION THAT  *)
(*  REFUTES `pobs_tr_le` -- the ambient stack `fk_new`, the store and   *)
(*  counter the refutation used -- with all three existential           *)
(*  witnesses supplied explicitly: the right-hand run, the world, and   *)
(*  the final store.  It ALSO proves that this configuration is inside  *)
(*  the nominal observation's quantifier: `fk_new` is equivariant and   *)
(*  the starting store is, so the repair does not work by EXCLUDING     *)
(*  the continuation that defeated the old relation.                    *)
(*                                                                     *)
(*  It does NOT prove `pnobs_tr_eq` itself for any pair.  That is the   *)
(*  universally quantified statement over EVERY equivariant stack and   *)
(*  store, and it needs a fundamental theorem for this machine -- a     *)
(*  simulation over `pstep` relating two configurations related by a    *)
(*  world.  That theorem is not attempted here and nothing below        *)
(*  claims it.                                                          *)
(* ================================================================== *)

(**
 * **The clause relation the fixtures run under.**
 *
 * Equality -- and the reason it is legitimate HERE is a fact about the type
 * `fcl` and not a convenience: every field of every `fcl` constructor is an
 * `fv`, and `fv` has no handle constructor, so no fixture clause can capture a
 * `pval`. `fcl_rel` is therefore not the refuted same-clause condition; it is
 * that condition's one sound instance, at a clause language in which capture is
 * not expressible. The general case -- a clause that really does capture a live
 * handle -- is `ncl` below, whose relation is NOT equality and could not be.
 *
 * (That `fv` contains no `pval` is read off the type declaration; it is not a
 * proposition this module proves.)
 *)
let fcl_rel : pcl_rel_t fcl = fun _ _ c1 c2 -> c1 == c2

let lemma_fcl_rel_mono () : Lemma (pcl_mono fcl_rel) = ()

(** Any table is related to itself under an equality clause relation, whatever
    the abstract `handlers` value inside it turns out to answer. PROVED without
    knowing anything about `mk_handlers`. *)
let lemma_ptable_selfrel (n: nat) (w: pworld) (t: ptable fcl)
  : Lemma (ptable_rel fcl_rel n w t t)
  = introduce forall (eff op: string).
      (match lookup_handler t.hs eff op, lookup_handler t.hs eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ fcl_rel n w f1.body f2.body
       | _, _ -> False)
    with (match lookup_handler t.hs eff op with | None -> () | Some _ -> ())

(**
 * **THE FIXTURES' LOOKUP IS EQUIVARIANT.** PROVED. `flook` reads only `binds`
 * and the effect label, and `ptable_rel` already forces `binds` to agree, so
 * two related tables answer identically -- which is more than the boundary
 * condition asks for, and implies it.
 *)
let lemma_flook_equivariant () : Lemma (plookup_equivariant fcl_rel flook)
  = introduce forall (n: nat) (w: pworld) (t1 t2: ptable fcl) (eff op: string).
      (ptable_rel fcl_rel n w t1 t2 ==>
       (match flook t1 eff op, flook t2 eff op with
        | None, None -> True
        | Some f1, Some f2 -> f1.kind == f2.kind /\ fcl_rel n w f1.body f2.body
        | _, _ -> False))
    with (introduce _ ==> _
          with (assert (t1.binds == t2.binds);
                assert (flook t1 eff op == flook t2 eff op);
                match flook t1 eff op with | None -> () | Some _ -> ()))

(* ---- The plan and the ambient stack the counterexample uses -------- *)

#push-options "--fuel 4 --ifuel 2"

let lemma_plan_A_selfrel (n: nat) (w: pworld)
  : Lemma (pplan_rel fcl_rel n w plan_A plan_A)
  = if n = 0 then () else lemma_ptable_selfrel n w ftbl

(**
 * **THE AMBIENT CONTINUATION THAT DEFEATS THE OLD RELATION IS EQUIVARIANT.**
 * PROVED, and GLOBALLY -- at every well-formed world, hence at every anchor.
 *
 * `fk_new` is the stack `[PBindF fnew_ctx]`, and `fnew_ctx` produces a context
 * of its own and returns its handle. It is the whole of the counterexample that
 * was not forced, and it is an entirely ordinary program: nothing forged,
 * nothing smuggled, and the handle it returns is one the run allocated. It
 * satisfies the nominal observation's hypothesis on the ambient stack, so the
 * repair below does not work by throwing it out.
 *)
let guard_nom_fk_new_equivariant ()
  : Lemma (pequivariant_k fcl_rel fk_new /\
           (forall (w0: pworld). pequivariant_k_at fcl_rel w0 fk_new))
  = introduce forall (w: pworld). (pwf_world w ==> pkrel fcl_rel w fk_new fk_new)
    with (introduce _ ==> _
          with (introduce forall (n: nat). pframes_rel fcl_rel n w fk_new fk_new
                with (if n = 0 then ()
                      else
                        introduce forall (w': pworld) (y1 y2: pval fv).
                            (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                             pcomp_rel fcl_rel n w' (fnew_ctx y1) (fnew_ctx y2))
                        with (introduce _ ==> _
                              with lemma_plan_A_selfrel (n - 1) w'))));
    introduce forall (w0: pworld). pequivariant_k_at fcl_rel w0 fk_new
    with (introduce forall (w: pworld).
              (pwf_world w /\ pwext w w0 ==> pkrel fcl_rel w fk_new fk_new)
          with (introduce _ ==> _ with ()))

(* ---- The store entries the two runs leave behind ------------------- *)

(** The frame list every context these runs build carries: the scope boundary
    and the plan's single prompt. Named so that the relation proof has one
    symbol to unfold rather than a literal to match. *)
let fce_frames : list (pframe fv fcl) = [PBoundaryF; PPromptF ftbl None PFamily]

(** The shape of every entry either run allocates: a request carrying a payload,
    that frame list, and the identity as its `post`. *)
let fce_cx (a: fv) : pctx fv fcl
  = PCtxRequests (PV a) fce_frames (PVar #fv #fcl)

let lemma_fce_frames_selfrel (n: nat) (w: pworld)
  : Lemma (pframes_rel fcl_rel n w fce_frames fce_frames)
  = if n = 0 then () else lemma_ptable_selfrel n w ftbl

(** **Every entry these runs leave is self-related, at EVERY world.** PROVED.
    It holds no handle -- its payload is an `FI` and its `post` is the identity
    -- so no world can separate it from itself. This is what condition 6 needs
    on the entries the world's domain DOES name. *)
let lemma_fce_cx_selfrel (w: pworld) (a: fv)
  : Lemma (pxrel fcl_rel w (fce_cx a) (fce_cx a))
  = introduce forall (n: nat). pctx_rel fcl_rel n w (fce_cx a) (fce_cx a)
    with (if n = 0 then ()
          else begin
            lemma_fce_frames_selfrel n w;
            introduce forall (w': pworld) (y1 y2: pval fv).
                (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                 pcomp_rel fcl_rel n w' (PVar y1) (PVar y2))
            with (introduce _ ==> _ with ())
          end)

#pop-options

(** The starting store of the algebraic half is a store the machine left behind,
    and it holds exactly one entry, of that same shape. PROVED by running. *)
let guard_nom_ce_sto ()
  : Lemma (ce_sto == [(0, fce_cx (FI 1))] /\ ce_nxt == 1)
  = assert_norm (ce_sto == [(0, fce_cx (FI 1))]);
    assert_norm (ce_nxt == 1)

(** The initial stores of all four pairs are equivariant, and fresh for their
    counters. PROVED. The empty store trivially; `ce_sto` because its one entry
    is self-related at every world. *)
let guard_nom_initial_stores_ok ()
  : Lemma (pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
           psfresh ([] <: pstore fv fcl) 0 /\
           pstore_equivariant_at fcl_rel ce_sto /\
           psfresh ce_sto 1)
  = guard_nom_ce_sto ();
    introduce forall (i: nat) (cx: pctx fv fcl).
        (pstore_lookup i ce_sto == Some cx ==>
         pequivariant_ctx_at fcl_rel (panchor ce_sto) cx)
    with (introduce _ ==> _
          with (assert (i == 0 /\ cx == fce_cx (FI 1));
                introduce forall (w: pworld).
                    (pwf_world w /\ pwext w (panchor ce_sto) ==>
                     pxrel fcl_rel w cx cx)
                with (introduce _ ==> _ with lemma_fce_cx_selfrel w (FI 1))))

(* ================================================================== *)
(*  PAIR 1 -- `ce_l` / `ce_r`, WHICH SERVES THREE OF THE SIX           *)
(*  (`law_left_identity`, `law_right_identity`,                        *)
(*   `law_transparent_agrees`)                                         *)
(* ================================================================== *)

let fce_sl : pstore fv fcl = [(1, fce_cx (FI 2)); (0, fce_cx (FI 1))]
let fce_sr : pstore fv fcl = [(0, fce_cx (FI 2))]

(** The world the two runs' answers correspond under: the left's key 1 to the
    right's key 0, and NOTHING ELSE. The left's own key 0 -- the context it
    allocated and discarded -- is not in the world at all. *)
let fce_w : pworld = [(1, 0)]

let guard_nom_ce_runs ()
  : Lemma (pnconverges flook fapply ce_cf_l [] (PCtxKey 1) fce_sl /\
           pnconverges flook fapply ce_cf_r [] (PCtxKey 0) fce_sr)
  = assert_norm ((fst (prun flook fapply 200 ce_cf_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_l)).store == fce_sl);
    assert_norm ((fst (prun flook fapply 200 ce_cf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_r) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_r)).store == fce_sr);
    lemma_pnconverges_at flook fapply ce_cf_l 200 [] (PCtxKey 1) fce_sl;
    lemma_pnconverges_at flook fapply ce_cf_r 200 [] (PCtxKey 0) fce_sr

#push-options "--fuel 4 --ifuel 2"
let guard_nom_ce_world ()
  : Lemma (pwf_world fce_w /\ pwext fce_w (panchor ([] <: pstore fv fcl)) /\
           pval_rel #fv fce_w (PCtxKey 1) (PCtxKey 0) /\
           pwlookup_l 0 fce_w == None /\
           psrel fcl_rel fce_w fce_sl fce_sr)
  = assert_norm (pwlookup_l 1 fce_w == Some 0);
    assert_norm (pwlookup_l 0 fce_w == None);
    assert_norm (panchor ([] <: pstore fv fcl) == ([] <: pworld));
    introduce forall (i j: nat).
        (pwlookup_l i fce_w == Some j ==>
         (Some? (pstore_lookup i fce_sl) /\ Some? (pstore_lookup j fce_sr) /\
          pxrel fcl_rel fce_w (psget i fce_sl) (psget j fce_sr)))
    with (introduce _ ==> _
          with (assert (i == 1 /\ j == 0);
                assert_norm (psget 1 fce_sl == fce_cx (FI 2));
                assert_norm (psget 0 fce_sr == fce_cx (FI 2));
                lemma_fce_cx_selfrel fce_w (FI 2)))
#pop-options

(**
 * **PAIR 1, RELATED.** PROVED, and this conjunction IS the body of
 * `pnobs_tr_le ce_l ce_r` at `k := fk_new`, `sto := []`, `n0 := 0`, with every
 * existential witness written down.
 *
 * The trace is `[]` on both sides and is compared by EQUALITY -- the separation
 * the old relation made was never the trace's doing and the repair does not
 * touch it. The counter is not mentioned. The left run ends holding one context
 * more than the right; that context is named by no key the world speaks for, so
 * `psrel` never looks at it.
 *)
let guard_nom_ce_related ()
  : Lemma (
      // the hypotheses the nominal observation imposes, at this configuration
      pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl)) fk_new /\
      pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
      psfresh ([] <: pstore fv fcl) 0 /\
      // the left run -- the antecedent
      pnconverges flook fapply ce_cf_l [] (PCtxKey 1) fce_sl /\
      // the witnesses the consequent demands
      pnconverges flook fapply ce_cf_r [] (PCtxKey 0) fce_sr /\
      pwf_world fce_w /\ pwext fce_w (panchor ([] <: pstore fv fcl)) /\
      pval_rel #fv fce_w (PCtxKey 1) (PCtxKey 0) /\
      psrel fcl_rel fce_w fce_sl fce_sr)
  = guard_nom_fk_new_equivariant ();
    guard_nom_initial_stores_ok ();
    guard_nom_ce_runs ();
    guard_nom_ce_world ()

(**
 * **AND THE WORLD IS NOT A RE-ANCHORING.** PROVED, at the store the left run
 * actually ends with. `panchor fce_sl` pins the left's garbage key 0 to itself;
 * `fce_w` is silent about it; and no world under which the two answers
 * correspond can extend `panchor fce_sl`, because that anchor pins key 1 to
 * itself while the answers force it to 0.
 *)
let guard_nom_ce_not_a_reanchoring ()
  : Lemma (pwlookup_l 0 (panchor fce_sl) == Some 0 /\
           pwlookup_l 0 fce_w == None /\
           pwlookup_l 1 (panchor fce_sl) == Some 1 /\
           pwlookup_l 1 fce_w == Some 0 /\
           ~(pwext fce_w (panchor fce_sl)) /\
           (forall (w: pworld). pval_rel #fv w (PCtxKey 1) (PCtxKey 0) ==>
                                ~(pwext w (panchor fce_sl))))
  = assert_norm (Some? (pstore_lookup 0 fce_sl));
    assert_norm (Some? (pstore_lookup 1 fce_sl));
    lemma_panchor_pins 0 fce_sl;
    lemma_panchor_pins 1 fce_sl;
    assert_norm (pwlookup_l 0 fce_w == None);
    assert_norm (pwlookup_l 1 fce_w == Some 0);
    introduce forall (w: pworld).
        (pval_rel #fv w (PCtxKey 1) (PCtxKey 0) ==> ~(pwext w (panchor fce_sl)))
    with (introduce _ ==> _ with guard_nom_no_reanchoring 1 0 fce_sl w)

(* ================================================================== *)
(*  PAIR 2 -- `ce_rm_l` / `ce_rm_r` (`law_resume_matches_continuation`) *)
(* ================================================================== *)

let guard_nom_ce_rm_related ()
  : Lemma (
      pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl)) fk_new /\
      pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
      psfresh ([] <: pstore fv fcl) 0 /\
      pnconverges flook fapply ce_cf_rm_l [] (PCtxKey 1) fce_sl /\
      pnconverges flook fapply ce_cf_rm_r [] (PCtxKey 0) fce_sr /\
      pwf_world fce_w /\ pwext fce_w (panchor ([] <: pstore fv fcl)) /\
      pval_rel #fv fce_w (PCtxKey 1) (PCtxKey 0) /\
      psrel fcl_rel fce_w fce_sl fce_sr)
  = guard_nom_fk_new_equivariant ();
    guard_nom_initial_stores_ok ();
    guard_nom_ce_world ();
    assert_norm ((fst (prun flook fapply 200 ce_cf_rm_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_rm_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_rm_l)).store == fce_sl);
    assert_norm ((fst (prun flook fapply 200 ce_cf_rm_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_rm_r) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_rm_r)).store == fce_sr);
    lemma_pnconverges_at flook fapply ce_cf_rm_l 200 [] (PCtxKey 1) fce_sl;
    lemma_pnconverges_at flook fapply ce_cf_rm_r 200 [] (PCtxKey 0) fce_sr

(* ================================================================== *)
(*  PAIR 3 -- `ce_aa_l` / `ce_aa_r` (`law_assoc`, ALGEBRAIC HALF)      *)
(*                                                                     *)
(*  The one pair whose starting store is NOT empty: it is the store a   *)
(*  real production left behind, so the anchor is not empty either and  *)
(*  the world must EXTEND it.  That is condition 2 doing its work in    *)
(*  the middle of a positive result rather than beside one: the         *)
(*  already-public key 0 keeps its own name, and only the two freshly   *)
(*  allocated handles are put in correspondence.                        *)
(* ================================================================== *)

let fce_aa_sl : pstore fv fcl =
  [(2, fce_cx (FI 2));
   (1, PCtxRequests (PV (FI 1)) fce_frames (fun z -> POp (PVar z) (PVar #fv #fcl)));
   (0, fce_cx (FI 1))]
let fce_aa_sr : pstore fv fcl = [(1, fce_cx (FI 2)); (0, fce_cx (FI 1))]

(** The starting anchor pins the public key 0; the run adds ONE pair, for the
    handle each side allocated last. The left's key 1 -- the context
    `o_extend_ctx` allocated and the right side never built -- is garbage and
    stays unspoken for. *)
let fce_aa_w : pworld = [(2, 1); (0, 0)]

#push-options "--fuel 6 --ifuel 2"
let guard_nom_ce_aa_world ()
  : Lemma (pwf_world fce_aa_w /\ pwext fce_aa_w (panchor ce_sto) /\
           pval_rel #fv fce_aa_w (PCtxKey 2) (PCtxKey 1) /\
           pwlookup_l 1 fce_aa_w == None /\
           psrel fcl_rel fce_aa_w fce_aa_sl fce_aa_sr)
  = guard_nom_ce_sto ();
    assert_norm (panchor ([(0, fce_cx (FI 1))] <: pstore fv fcl) == [(0, 0)]);
    assert_norm (pwlookup_l 2 fce_aa_w == Some 1);
    assert_norm (pwlookup_l 1 fce_aa_w == None);
    assert_norm (pwlookup_l 0 fce_aa_w == Some 0);
    introduce forall (i j: nat).
        (pwlookup_l i fce_aa_w == Some j ==>
         (Some? (pstore_lookup i fce_aa_sl) /\ Some? (pstore_lookup j fce_aa_sr) /\
          pxrel fcl_rel fce_aa_w (psget i fce_aa_sl) (psget j fce_aa_sr)))
    with (introduce _ ==> _
          with (assert ((i == 2 /\ j == 1) \/ (i == 0 /\ j == 0));
                assert_norm (psget 2 fce_aa_sl == fce_cx (FI 2));
                assert_norm (psget 1 fce_aa_sr == fce_cx (FI 2));
                assert_norm (psget 0 fce_aa_sl == fce_cx (FI 1));
                assert_norm (psget 0 fce_aa_sr == fce_cx (FI 1));
                lemma_fce_cx_selfrel fce_aa_w (FI 2);
                lemma_fce_cx_selfrel fce_aa_w (FI 1)))
#pop-options

let guard_nom_ce_aa_related ()
  : Lemma (
      pequivariant_k_at fcl_rel (panchor ce_sto) fk_new /\
      pstore_equivariant_at fcl_rel ce_sto /\ psfresh ce_sto ce_nxt /\
      pnconverges flook fapply ce_cf_aa_l [] (PCtxKey 2) fce_aa_sl /\
      pnconverges flook fapply ce_cf_aa_r [] (PCtxKey 1) fce_aa_sr /\
      pwf_world fce_aa_w /\ pwext fce_aa_w (panchor ce_sto) /\
      pval_rel #fv fce_aa_w (PCtxKey 2) (PCtxKey 1) /\
      psrel fcl_rel fce_aa_w fce_aa_sl fce_aa_sr)
  = guard_nom_fk_new_equivariant ();
    guard_nom_initial_stores_ok ();
    guard_nom_ce_sto ();
    guard_nom_ce_aa_world ();
    assert_norm ((fst (prun flook fapply 200 ce_cf_aa_l)).st == PDone (PCtxKey 2));
    assert_norm (snd (prun flook fapply 200 ce_cf_aa_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_aa_l)).store == fce_aa_sl);
    assert_norm ((fst (prun flook fapply 200 ce_cf_aa_r)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook fapply 200 ce_cf_aa_r) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_aa_r)).store == fce_aa_sr);
    lemma_pnconverges_at flook fapply ce_cf_aa_l 200 [] (PCtxKey 2) fce_aa_sl;
    lemma_pnconverges_at flook fapply ce_cf_aa_r 200 [] (PCtxKey 1) fce_aa_sr

(* ================================================================== *)
(*  PAIR 4 -- `ce_ac_l` / `ce_ac_r` (`law_assoc`, ANCHORED HALF)       *)
(*                                                                     *)
(*  The left allocates TWICE and the right not at all, so the two       *)
(*  answers are TWO apart rather than one.  The world still adds        *)
(*  exactly one pair -- one per handle that surfaced ON BOTH SIDES --   *)
(*  and both of the left's other entries are garbage.                   *)
(* ================================================================== *)

let fce_ac_w : pworld = [(2, 0)]

#push-options "--fuel 4 --ifuel 2"
let guard_nom_ce_ac_world ()
  : Lemma (pwf_world fce_ac_w /\ pwext fce_ac_w (panchor ([] <: pstore fv fcl)) /\
           pval_rel #fv fce_ac_w (PCtxKey 2) (PCtxKey 0) /\
           pwlookup_l 1 fce_ac_w == None /\ pwlookup_l 0 fce_ac_w == None /\
           psrel fcl_rel fce_ac_w fce_aa_sl fce_sr)
  = assert_norm (pwlookup_l 2 fce_ac_w == Some 0);
    assert_norm (pwlookup_l 1 fce_ac_w == None);
    assert_norm (pwlookup_l 0 fce_ac_w == None);
    assert_norm (panchor ([] <: pstore fv fcl) == ([] <: pworld));
    introduce forall (i j: nat).
        (pwlookup_l i fce_ac_w == Some j ==>
         (Some? (pstore_lookup i fce_aa_sl) /\ Some? (pstore_lookup j fce_sr) /\
          pxrel fcl_rel fce_ac_w (psget i fce_aa_sl) (psget j fce_sr)))
    with (introduce _ ==> _
          with (assert (i == 2 /\ j == 0);
                assert_norm (psget 2 fce_aa_sl == fce_cx (FI 2));
                assert_norm (psget 0 fce_sr == fce_cx (FI 2));
                lemma_fce_cx_selfrel fce_ac_w (FI 2)))
#pop-options

let guard_nom_ce_ac_related ()
  : Lemma (
      pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl)) fk_new /\
      pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
      psfresh ([] <: pstore fv fcl) 0 /\
      pnconverges flook fapply ce_cf_ac_l [] (PCtxKey 2) fce_aa_sl /\
      pnconverges flook fapply ce_cf_ac_r [] (PCtxKey 0) fce_sr /\
      pwf_world fce_ac_w /\ pwext fce_ac_w (panchor ([] <: pstore fv fcl)) /\
      pval_rel #fv fce_ac_w (PCtxKey 2) (PCtxKey 0) /\
      psrel fcl_rel fce_ac_w fce_aa_sl fce_sr)
  = guard_nom_fk_new_equivariant ();
    guard_nom_initial_stores_ok ();
    guard_nom_ce_ac_world ();
    assert_norm ((fst (prun flook fapply 200 ce_cf_ac_l)).st == PDone (PCtxKey 2));
    assert_norm (snd (prun flook fapply 200 ce_cf_ac_l) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_ac_l)).store == fce_aa_sl);
    assert_norm ((fst (prun flook fapply 200 ce_cf_ac_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook fapply 200 ce_cf_ac_r) == []);
    assert_norm ((fst (prun flook fapply 200 ce_cf_ac_r)).store == fce_sr);
    lemma_pnconverges_at flook fapply ce_cf_ac_l 200 [] (PCtxKey 2) fce_aa_sl;
    lemma_pnconverges_at flook fapply ce_cf_ac_r 200 [] (PCtxKey 0) fce_sr

(**
 * **THE SIX, IN ONE STATEMENT.** PROVED. Four pairs of programs, six
 * propositions -- `law_left_identity`, `law_right_identity`,
 * `law_transparent_agrees` at pair 1, `law_resume_matches_continuation` at pair
 * 2, and `law_assoc`'s two conjuncts at pairs 3 and 4 -- every one of which is
 * FALSE under `pobs_tr_eq` (the guards above) and every one of whose two sides
 * corresponds under a world here.
 *
 * In each case the world adds ONE pair per handle that surfaced on both sides,
 * extends the starting anchor, and is silent about every context only one side
 * built.
 *)
let guard_nom_the_six ()
  : Lemma (
      // the three that share pair 1
      pval_rel #fv fce_w (PCtxKey 1) (PCtxKey 0) /\
      psrel fcl_rel fce_w fce_sl fce_sr /\
      pwext fce_w (panchor ([] <: pstore fv fcl)) /\
      // the fourth
      pnconverges flook fapply ce_cf_rm_l [] (PCtxKey 1) fce_sl /\
      pnconverges flook fapply ce_cf_rm_r [] (PCtxKey 0) fce_sr /\
      // `law_assoc`, algebraic half -- at a NON-EMPTY anchor
      pval_rel #fv fce_aa_w (PCtxKey 2) (PCtxKey 1) /\
      psrel fcl_rel fce_aa_w fce_aa_sl fce_aa_sr /\
      pwext fce_aa_w (panchor ce_sto) /\
      pwlookup_l 0 fce_aa_w == Some 0 /\
      // `law_assoc`, anchored half -- two allocations against none
      pval_rel #fv fce_ac_w (PCtxKey 2) (PCtxKey 0) /\
      psrel fcl_rel fce_ac_w fce_aa_sl fce_sr /\
      // and every world above is well formed, hence a bijection
      pwf_world fce_w /\ pwf_world fce_aa_w /\ pwf_world fce_ac_w)
  = guard_nom_ce_related ();
    guard_nom_ce_rm_related ();
    guard_nom_ce_aa_related ();
    guard_nom_ce_ac_related ();
    assert_norm (pwlookup_l 0 fce_aa_w == Some 0)

(* ================================================================== *)
(*  B2b.1: THE NEGATIVES -- WHAT THE REPAIR MUST NOT RELATE            *)
(*                                                                     *)
(*  A repair that related everything would be worthless.  Five things   *)
(*  must stay separated, and each is checked below rather than argued:  *)
(*  two genuinely distinct LIVE handles; two entries whose contexts     *)
(*  BEHAVE differently; a FORGED or STALE handle; a name the run has    *)
(*  not created; and two programs whose TRACES differ.                  *)
(* ================================================================== *)

(* ---- CONDITION 2: B1.7's two live handles are not collapsed -------- *)

(**
 * **THE TWO DISTINCT LIVE HANDLES OF `fixture_17` STAY DISTINCT.** PROVED, at
 * the store that fixture's own run leaves behind.
 *
 * `prog17` produces two scopes and holds both handles at once; the store ends
 * with two entries, keys 0 and 1. The anchor pins each to ITSELF, and a world
 * is a partial FUNCTION, so no world extending the anchor can send key 0 to key
 * 1. Condition 2 is therefore not a property of how the repair happens to be
 * used: it is unavailable to it.
 *)
let fs17 : pstore fv fcl = (frun 800 prog17).store

let guard_nom_fixture_17_handles_live ()
  : Lemma (Some? (pstore_lookup 0 fs17) /\ Some? (pstore_lookup 1 fs17) /\
           pwlookup_l 0 (panchor fs17) == Some 0 /\
           pwlookup_l 1 (panchor fs17) == Some 1)
  = assert_norm (Some? (pstore_lookup 0 fs17));
    assert_norm (Some? (pstore_lookup 1 fs17));
    lemma_panchor_pins 0 fs17;
    lemma_panchor_pins 1 fs17

let guard_nom_fixture_17_not_collapsed (w: pworld)
  : Lemma (requires pwext w (panchor fs17))
          (ensures ~(pval_rel #fv w (PCtxKey 0) (PCtxKey 1)) /\
                   ~(pval_rel #fv w (PCtxKey 1) (PCtxKey 0)))
  = guard_nom_fixture_17_handles_live ();
    guard_nom_distinct_live_handles 0 1 fs17 w;
    guard_nom_distinct_live_handles 1 0 fs17 w

(* ---- CONDITION 3: aliasing, and the ORDER handles are selected in --- *)

(**
 * **A WORLD EXTENDING THE ANCHOR IS THE IDENTITY ON EVERY ALREADY-PUBLIC
 * HANDLE.** PROVED. So a program that selects the FIRST of two handles it was
 * given is matched by one that selects the first, and not the second: the order
 * in which handles are selected is preserved because the public ones are not
 * renamed at all, and the ones created during the run are put in correspondence
 * one pair at a time, in the order they surfaced.
 *)
let guard_nom_selection_order_preserved (#v #cl: Type)
      (sto: pstore v cl) (w: pworld) (i j: nat)
  : Lemma (requires pwext w (panchor sto) /\
                    Some? (pstore_lookup i sto) /\ Some? (pstore_lookup j sto))
          (ensures pval_rel #v w (PCtxKey i) (PCtxKey i) /\
                   pval_rel #v w (PCtxKey j) (PCtxKey j) /\
                   ((i == j) <==> (pwlookup_l i w == pwlookup_l j w)))
  = lemma_panchor_pins i sto;
    lemma_panchor_pins j sto

(** And aliasing, at the two handles of `fixture_17`: they are different on the
    left exactly when their partners are different on the right. PROVED, from
    `pwf_world`'s biconditional and nothing else. *)
let guard_nom_fixture_17_aliasing (w: pworld) (a b: pval fv)
  : Lemma (requires pwf_world w /\ pval_rel #fv w (PCtxKey 0) a /\
                    pval_rel #fv w (PCtxKey 1) b)
          (ensures (PCtxKey #fv 0 == PCtxKey #fv 1) <==> (a == b))
  = guard_nom_eq_preserves_aliasing w (PCtxKey 0) a (PCtxKey 1) b

(* ---- CONDITION 4: contexts that behave differently ----------------- *)

(** A second context shape, identical to `fce_cx` except in what it DOES when
    consumed: its `post` performs an operation before returning rather than
    returning at once. *)
let fce_cx_b (a: fv) : pctx fv fcl
  = PCtxRequests (PV a) fce_frames (fun z -> POp (PVar z) (PVar #fv #fcl))

(**
 * **TWO ENTRIES WHOSE CONTEXTS BEHAVE DIFFERENTLY ARE NOT RELATED, AT ANY
 * WORLD.** PROVED. The `post` components must send related arguments to related
 * computations, and `PVar y` is not related to `POp (PVar y) PVar` -- different
 * constructors at the head, and the relation has no clause joining them.
 *)
let guard_nom_different_contexts_unrelated (w: pworld) (a: fv)
  : Lemma (requires pwf_world w)
          (ensures ~(pxrel fcl_rel w (fce_cx a) (fce_cx_b a)) /\
                   ~(pxrel fcl_rel w (fce_cx_b a) (fce_cx a)))
  = introduce pxrel fcl_rel w (fce_cx a) (fce_cx_b a) ==> False
    with begin
      assert (pval_rel #fv w (fpv FU) (fpv FU));
      assert (pctx_rel fcl_rel 1 w (fce_cx a) (fce_cx_b a));
      assert (pcomp_rel fcl_rel 1 w (PVar (fpv FU))
                                    (POp (PVar (fpv FU)) (PVar #fv #fcl)))
    end;
    introduce pxrel fcl_rel w (fce_cx_b a) (fce_cx a) ==> False
    with begin
      assert (pval_rel #fv w (fpv FU) (fpv FU));
      assert (pctx_rel fcl_rel 1 w (fce_cx_b a) (fce_cx a));
      assert (pcomp_rel fcl_rel 1 w (POp (PVar (fpv FU)) (PVar #fv #fcl))
                                    (PVar (fpv FU)))
    end

(** Nor two entries that merely carry different payloads. PROVED. *)
let guard_nom_different_payloads_unrelated (w: pworld)
  : Lemma (~(pxrel fcl_rel w (fce_cx (FI 1)) (fce_cx (FI 2))))
  = introduce pxrel fcl_rel w (fce_cx (FI 1)) (fce_cx (FI 2)) ==> False
    with assert (pctx_rel fcl_rel 1 w (fce_cx (FI 1)) (fce_cx (FI 2)))

(**
 * **AND THE STORE RELATION REFUSES THE PAIR.** PROVED. A world that sent a key
 * holding one context to a key holding the other would not relate the two
 * stores -- so the repair cannot buy agreement by mapping a handle onto a
 * differently behaving one.
 *)
let guard_nom_psrel_refuses_different_contexts
      (w: pworld) (s1 s2: pstore fv fcl) (i j: nat) (a: fv)
  : Lemma (requires pwf_world w /\ pwlookup_l i w == Some j /\
                    pstore_lookup i s1 == Some (fce_cx a) /\
                    pstore_lookup j s2 == Some (fce_cx_b a))
          (ensures ~(psrel fcl_rel w s1 s2))
  = guard_nom_different_contexts_unrelated w a;
    introduce psrel fcl_rel w s1 s2 ==> False
    with begin
      assert (Some? (pstore_lookup i s1) /\ Some? (pstore_lookup j s2));
      assert (psget i s1 == fce_cx a);
      assert (psget j s2 == fce_cx_b a)
    end

(* ---- CONDITION 5: forged and stale handles, and future names ------- *)

(**
 * **A FORGED OR STALE HANDLE IS RELATED TO NOTHING, AND THERE IS NO FALLBACK
 * TO NEARNESS.** PROVED. `pval_rel` has exactly one clause for handles and it
 * asks the world; a key the world does not speak for has no partner, and no
 * clause relates it to a nearby key, to a payload, or to anything else.
 *
 * `fixture_19` already shows a forged handle FAILING in the machine --
 * `presolve` refuses it and the run gets stuck, so it never reaches a value to
 * be compared. This is the relational half of the same statement.
 *)
let guard_nom_forged_stays_forged (w: pworld) (n1 n2 i: nat) (x2: pval fv)
  : Lemma (requires pwbound w n1 n2 /\ i >= n1)
          (ensures ~(pval_rel #fv w (PCtxKey i) x2))
  = guard_nom_forged_handle_unrelated w i x2

(**
 * **AN ANCHOR NEVER PINS A NAME THE RUN HAS NOT CREATED.** PROVED, and it is
 * what closes the hole the relativisation could have opened.
 *
 * Anchor-relative equivariance is WEAKER than the global notion, so the obvious
 * worry is that a dishonest closure could pre-own a name. It cannot: an anchor
 * pins exactly the keys the store ALREADY HOLDS, and the store holds nothing at
 * or above the counter. Every name the run has not yet created is therefore
 * still an unowned future name, and a closure that returns one is refused -- at
 * EVERY anchor whatsoever.
 *)
let guard_nom_anchor_never_pins_a_future_name
      (#v #cl: Type) (r: pcl_rel_t cl) (sto: pstore v cl) (n0: nat) (i: nat)
  : Lemma (requires psfresh sto n0 /\ i >= n0)
          (ensures pwlookup_l i (panchor sto) == None /\
                   pwlookup_r (i + 1) (panchor sto) == None /\
                   ~(pfn_rel_at r (panchor sto) (pkcap #v #cl i) (pkcap #v #cl i)))
  = lemma_panchor_l i sto;
    lemma_panchor_r (i + 1) sto;
    lemma_panchor_wf sto;
    lemma_pwextend_wf i (i + 1) (panchor sto);
    let w = pwextend i (i + 1) (panchor sto) in
    assert (pwf_world w /\ pwext w (panchor sto) /\ pwlookup_l i w == Some (i + 1));
    assert (pval_rel #v w (PCtxKey i) (PCtxKey (i + 1)));
    introduce pfn_rel_at r (panchor sto) (pkcap #v #cl i) (pkcap #v #cl i) ==> False
    with begin
      assert (pcrel r w (pkcap #v #cl i (PCtxKey i)) (pkcap #v #cl i (PCtxKey (i + 1))));
      assert (pcomp_rel r 1 w (PVar (PCtxKey #v i)) (PVar (PCtxKey #v i)))
    end

(**
 * **THE SAME TERM, TWO ANCHORS, OPPOSITE VERDICTS.** PROVED, and this is what
 * makes the relativisation carry its weight rather than rename the problem.
 *
 * `pkcap i` returns the handle `PCtxKey i`. At an anchor that does not own `i`
 * -- the empty one, and every anchor of a store not holding `i` -- it is
 * REFUSED: `i` is an unowned future name and a world is free to rename it. At
 * an anchor that DOES own `i` it is ADMITTED, because the term is then a
 * legitimate CAPTURE of a handle the store already holds. The discrimination is
 * not syntactic; it comes from the provenance the starting world carries.
 *)
let guard_nom_capture_vs_guess (#v #cl: Type) (r: pcl_rel_t cl) (i: nat) (w0: pworld)
  : Lemma (requires pwlookup_l i w0 == Some i)
          (ensures pfn_rel_at r w0 (pkcap #v #cl i) (pkcap #v #cl i) /\
                   ~(pfn_rel_at r ([] <: pworld) (pkcap #v #cl i) (pkcap #v #cl i)))
  = guard_nom_capture_not_single_sided #v #cl r i;
    introduce forall (w: pworld) (y1 y2: pval v).
        (pwf_world w /\ pwext w w0 /\ pval_rel w y1 y2 ==>
         pcrel r w (pkcap #v #cl i y1) (pkcap #v #cl i y2))
    with (introduce _ ==> _
          with (assert (pwlookup_l i w == Some i);
                assert (pval_rel #v w (PCtxKey i) (PCtxKey i));
                introduce forall (n: nat).
                    pcomp_rel r n w (PVar (PCtxKey #v i)) (PVar (PCtxKey #v i))
                with ()))

(**
 * **AND THE TWO-SIDED FORM, WHICH IS THE WHOLE REASON THE RELATION IS
 * TWO-SIDED.** PROVED. Two closures capturing the two CORRESPONDING raw keys --
 * different terms, holding different numbers -- are related at a world that
 * says the two keys correspond. No single-sided condition can state this, and
 * (`guard_nom_capture_not_single_sided`) none holds of either closure alone.
 *)
let guard_nom_two_captures_related (#v #cl: Type) (r: pcl_rel_t cl)
      (i j: nat) (w0: pworld)
  : Lemma (requires pwlookup_l i w0 == Some j)
          (ensures pfn_rel_at r w0 (pkcap #v #cl i) (pkcap #v #cl j))
  = introduce forall (w: pworld) (y1 y2: pval v).
        (pwf_world w /\ pwext w w0 /\ pval_rel w y1 y2 ==>
         pcrel r w (pkcap #v #cl i y1) (pkcap #v #cl j y2))
    with (introduce _ ==> _
          with (assert (pwlookup_l i w == Some j);
                assert (pval_rel #v w (PCtxKey i) (PCtxKey j));
                introduce forall (n: nat).
                    pcomp_rel r n w (PVar (PCtxKey #v i)) (PVar (PCtxKey #v j))
                with ()))

(* ---- CONDITION 6: only unreachable entries are ignored ------------- *)

(**
 * **WHAT IS IGNORED, AND WHAT IS NOT.** `psrel` quantifies over the WORLD'S
 * DOMAIN, so an entry is ignored exactly when no key the world speaks for names
 * it. Two facts bound that, and both are checked:
 *
 *   - `lemma_psrel_garbage` (above): an entry added at the fresh counter, which
 *     is what an allocation only one side performed leaves, is outside the
 *     anchor's domain -- and the two stores are then related in BOTH
 *     directions, which is what makes the ignoring symmetric rather than a
 *     licence for the left side to hide things;
 *   - and here, concretely: the entry the world's domain DOES name at the
 *     counterexample carries no handle at all -- its payload is an ordinary
 *     value, its residual frames are a boundary and a prompt, and its `post` is
 *     the identity -- so nothing reachable from the answer names the ignored
 *     key.
 *
 * **What is NOT claimed.** "Reachable" is not a computable predicate here: a
 * `PCtxRequests` carries a `post` whose returned keys cannot be enumerated,
 * which is the reason this relation is defined by what the two sides PRODUCE in
 * the first place. So the general statement "exactly the unreachable entries
 * are ignored" is not proved; what is proved is the domain restriction and this
 * instance of it.
 *)
let guard_nom_only_garbage_ignored ()
  : Lemma (PCtxRequests?.value (fce_cx (FI 2)) == PV (FI 2) /\
           PCtxRequests?.residual (fce_cx (FI 2)) == fce_frames /\
           PCtxRequests?.post (fce_cx (FI 2)) == (PVar #fv #fcl) /\
           fce_frames == [PBoundaryF; PPromptF ftbl None PFamily] /\
           pwlookup_l 0 fce_w == None /\
           Some? (pstore_lookup 0 fce_sl) /\
           psrel fcl_rel fce_w fce_sl fce_sr)
  = guard_nom_ce_world ();
    assert_norm (pwlookup_l 0 fce_w == None);
    assert_norm (Some? (pstore_lookup 0 fce_sl))

(* ---- CONDITION 8 / CONDITION 7: the trace, and what survives ------- *)

(**
 * **THE TRACE-BASED SEPARATION OF THE RESIDUAL FROM THE SUSPENSION SURVIVES.**
 * PROVED, and in the strongest form: the suspension program does not converge
 * with the residual program's trace AT ALL, so no choice of world can rescue
 * it. The world enters the nominal observation only at the VALUE and the STORE;
 * the trace is compared by equality before any world is chosen.
 *
 * The configuration is `pload`'s -- empty stack, empty store, counter zero --
 * which satisfies every hypothesis the nominal observation imposes, so this is
 * a separation INSIDE the new relation's quantifier and not outside it.
 *)
let guard_nom_trace_separation_survives ()
  : Lemma ((forall (x2: pval fv) (s2: pstore fv fcl).
              ~(pnconverges flook fapply (pload prog_susp)
                            ["prefix"; "c1"; "c2"] x2 s2)) /\
           (forall (x2: pval fv) (s2: pstore fv fcl).
              ~(pnconverges flook fapply (pload prog_traced)
                            ["prefix"; "c1"; "prefix"; "c2"] x2 s2)) /\
           pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl))
                             ([] <: pstack fv fcl) /\
           pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
           psfresh ([] <: pstore fv fcl) 0)
  = guard_traced_converges_tr ();
    guard_susp_converges_tr ();
    introduce forall (x2: pval fv) (s2: pstore fv fcl).
        ~(pnconverges flook fapply (pload prog_susp) ["prefix"; "c1"; "c2"] x2 s2)
    with (introduce pnconverges flook fapply (pload prog_susp)
                                ["prefix"; "c1"; "c2"] x2 s2 ==> False
          with (lemma_pnconverges_forget flook fapply (pload prog_susp)
                  ["prefix"; "c1"; "c2"] x2 s2;
                lemma_pconverges_tr_unique flook fapply (pload prog_susp)
                  ["prefix"; "c1"; "c2"] ["prefix"; "c1"; "prefix"; "c2"]
                  x2 (fdone (fend 400 prog_susp))));
    introduce forall (x2: pval fv) (s2: pstore fv fcl).
        ~(pnconverges flook fapply (pload prog_traced)
                      ["prefix"; "c1"; "prefix"; "c2"] x2 s2)
    with (introduce pnconverges flook fapply (pload prog_traced)
                                ["prefix"; "c1"; "prefix"; "c2"] x2 s2 ==> False
          with (lemma_pnconverges_forget flook fapply (pload prog_traced)
                  ["prefix"; "c1"; "prefix"; "c2"] x2 s2;
                lemma_pconverges_tr_unique flook fapply (pload prog_traced)
                  ["prefix"; "c1"; "prefix"; "c2"] ["prefix"; "c1"; "c2"]
                  x2 (fdone (fend 400 prog_traced))))

(**
 * **THE NEGATIVES, IN ONE STATEMENT.** PROVED.
 *)
let guard_nom_the_negatives ()
  : Lemma (
      // 2: two distinct LIVE handles, at B1.7's own fixture
      (forall (w: pworld). pwext w (panchor fs17) ==>
         ~(pval_rel #fv w (PCtxKey 0) (PCtxKey 1))) /\
      // 3: aliasing, from the bijection
      (forall (w: pworld) (a1 a2 b1 b2: pval fv).
         pwf_world w /\ pval_rel w a1 a2 /\ pval_rel w b1 b2 ==>
         ((a1 == b1) <==> (a2 == b2))) /\
      // 4: contexts that behave differently
      (forall (w: pworld) (a: fv).
         pwf_world w ==> ~(pxrel fcl_rel w (fce_cx a) (fce_cx_b a))) /\
      // 5: forged and stale handles
      (forall (w: pworld) (n1 n2 i: nat) (x2: pval fv).
         pwbound w n1 n2 /\ i >= n1 ==> ~(pval_rel #fv w (PCtxKey i) x2)) /\
      // 8: the trace
      (forall (x2: pval fv) (s2: pstore fv fcl).
         ~(pnconverges flook fapply (pload prog_susp)
                       ["prefix"; "c1"; "c2"] x2 s2)))
  = introduce forall (w: pworld). (pwext w (panchor fs17) ==>
                                   ~(pval_rel #fv w (PCtxKey 0) (PCtxKey 1)))
    with (introduce _ ==> _ with guard_nom_fixture_17_not_collapsed w);
    introduce forall (w: pworld) (a1 a2 b1 b2: pval fv).
        (pwf_world w /\ pval_rel w a1 a2 /\ pval_rel w b1 b2 ==>
         ((a1 == b1) <==> (a2 == b2)))
    with (introduce _ ==> _ with guard_nom_eq_preserves_aliasing w a1 a2 b1 b2);
    introduce forall (w: pworld) (a: fv).
        (pwf_world w ==> ~(pxrel fcl_rel w (fce_cx a) (fce_cx_b a)))
    with (introduce _ ==> _ with guard_nom_different_contexts_unrelated w a);
    introduce forall (w: pworld) (n1 n2 i: nat) (x2: pval fv).
        (pwbound w n1 n2 /\ i >= n1 ==> ~(pval_rel #fv w (PCtxKey i) x2))
    with (introduce _ ==> _ with guard_nom_forged_stays_forged w n1 n2 i x2);
    guard_nom_trace_separation_survives ()

(* ================================================================== *)
(*  B2b.1: THE BOUNDARY, INHABITED -- AND ONE FINDING                  *)
(* ================================================================== *)

(** A constant continuation, equivariant at every world because it looks at
    nothing. It is the simplest witness the two negatives below need. *)
let fk_const (_: pval fv) : pcomp fv fcl = PVar (fpv FU)

let lemma_fk_const_equivariant (w: pworld)
  : Lemma (pfn_rel_at fcl_rel w fk_const fk_const)
  = introduce forall (w': pworld) (y1 y2: pval fv).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
         pcrel fcl_rel w' (fk_const y1) (fk_const y2))
    with (introduce _ ==> _
          with (introduce forall (n: nat).
                    pcomp_rel fcl_rel n w' (PVar (fpv FU)) (PVar (fpv FU))
                with ()))

(** The body `FWrap` wraps its answer in, at top level so that the relation
    proof has a symbol rather than a lambda inside `fapply` to match. *)
let fwrap_body (r: pval fv) : pcomp fv fcl = fret (FL [FS "wrap"; fseen r])

let lemma_fapply_wrap_shape ()
  : Lemma (fapply FWrap [] fk_const == POp (fk_const (fpv (FS "outer-ans"))) fwrap_body)
  = assert (fapply FWrap [] fk_const
            == POp (fk_const (fpv (FS "outer-ans"))) fwrap_body)
    by (FStar.Tactics.V2.norm
          [delta_only [`%fapply; `%fwrap_body; `%fk_const; `%fret; `%fpv];
           zeta; iota; primops];
        FStar.Tactics.V2.trefl ())

(**
 * **A FINDING: THE FIXTURES' CLAUSE INTERPRETER IS *NOT* EQUIVARIANT, AND THE
 * REASON IS `fseen`.** PROVED -- the negation is proved.
 *
 * `fseen` renders a handle as `FL [FS "ctx"; FI i]`, RAW NAME INCLUDED. That is
 * deliberate and documented: `fseen` is the fixtures' observer, the thing that
 * lets a fixture report WHICH context it was given, and the note on it already
 * says it is not available to the machine. But an interpreter that prints a
 * handle's name is exactly the `Show`-style exposure a nominal observation must
 * refuse, and refusing it is not optional: two related handles carry different
 * numbers, so the rendered answers differ and the two applications are not
 * related.
 *
 * WHAT THIS DOES AND DOES NOT COST. It means no `pboundary fv fcl` can be built
 * with `b_apply = fapply`, so the nominal observation is not available AT THE
 * FIXTURES' OWN CLAUSE LANGUAGE. It costs the results above nothing: the four
 * counterexample pairs perform no operation at all, so `fapply` is never
 * reached on either side of any of them -- which is why those results are
 * stated over `flook` and `fapply` directly rather than through a record.
 *
 * `nboundary` below is the record built instead, over a clause language that
 * does not render handles and DOES capture them.
 *)
(** The world the refutation uses: it renames the key 0 to 1, which is a thing
    a legal world may do to a name no anchor owns. Top level, so that
    `assert_norm` can unfold it. *)
let fw01 : pworld = [(0, 1)]

#push-options "--fuel 4 --ifuel 2"
let guard_nom_fapply_not_equivariant ()
  : Lemma (~(papply_equivariant fcl_rel fapply))
  = lemma_fapply_wrap_shape ();
    lemma_fk_const_equivariant ([] <: pworld);
    assert_norm (pwlookup_l 0 fw01 == Some 1);
    assert_norm (pwlookup_r 1 fw01 == Some 0);
    assert (pwf_world ([] <: pworld));
    assert (pwf_world fw01);
    assert (pwext fw01 ([] <: pworld));
    assert (pval_rel #fv fw01 (PCtxKey 0) (PCtxKey 1));
    assert_norm (fwrap_body (PCtxKey 0)
                 == PVar (PV (FL [FS "wrap"; FL [FS "ctx"; FI 0]])));
    assert_norm (fwrap_body (PCtxKey 1)
                 == PVar (PV (FL [FS "wrap"; FL [FS "ctx"; FI 1]])));
    assert_norm (FL [FS "wrap"; FL [FS "ctx"; FI 0]]
                 =!= FL [FS "wrap"; FL [FS "ctx"; FI 1]]);
    introduce papply_equivariant fcl_rel fapply ==> False
    with begin
      assert (pclrel fcl_rel ([] <: pworld) FWrap FWrap);
      assert (pvals_rel #fv ([] <: pworld) [] []);
      assert (pcrel fcl_rel ([] <: pworld)
                (fapply FWrap [] fk_const) (fapply FWrap [] fk_const));
      assert (pcomp_rel fcl_rel 2 ([] <: pworld)
                (POp (fk_const (fpv (FS "outer-ans"))) fwrap_body)
                (POp (fk_const (fpv (FS "outer-ans"))) fwrap_body));
      assert (pcomp_rel fcl_rel 1 fw01 (fwrap_body (PCtxKey 0)) (fwrap_body (PCtxKey 1)))
    end
#pop-options

(* ------------------------------------------------------------------ *)
(*  A CLAUSE LANGUAGE THAT CAPTURES HANDLES, AND THE RECORD OVER IT    *)
(* ------------------------------------------------------------------ *)

(**
 * **The clause language the boundary record is built at.** Three shapes, chosen
 * so that the two that matter CAPTURE A `pval fv` -- which is to say, may be
 * holding a live handle -- and so that one of them CONSUMES its capture by
 * handing it to the continuation. This is the situation the shipped machine is
 * actually in: `cl` is an opaque PureScript closure and nothing stops it from
 * having closed over a context handle.
 *
 * Nothing here renders a handle. That is the whole difference from `fcl`, and
 * it is why a record can be built here and not there.
 *)
noeq
type ncl =
  | NEcho: ncl                    (* resume with the payload's head           *)
  | NRet: cap:pval fv -> ncl      (* RETURN a captured value -- maybe a handle *)
  | NResume: cap:pval fv -> ncl   (* RESUME with the captured value           *)

(**
 * **The clause relation: TWO-SIDED, and world-indexed.** Two clauses correspond
 * when they are the same shape and their CAPTURES correspond -- which for two
 * handles means the world says so. `NRet (PCtxKey 5)` and `NRet (PCtxKey 6)`
 * are DIFFERENT VALUES and are related at a world sending 5 to 6; that is the
 * whole difficulty, and no relation phrased over one clause value can express
 * it.
 *)
let ncl_rel : pcl_rel_t ncl = fun _ w c1 c2 ->
  match c1, c2 with
  | NEcho, NEcho -> True
  | NRet a, NRet b -> pval_rel w a b
  | NResume a, NResume b -> pval_rel w a b
  | _, _ -> False

let napply : papply_t fv ncl = fun c payload k ->
  match c with
  | NEcho -> (match payload with | x :: _ -> k x | [] -> k (fpv FU))
  | NRet cap -> PVar cap
  | NResume cap -> k cap

(** The same constant continuation at the `ncl` clause language, and its
    equivariance -- generic in the clause relation, so that both the two-sided
    relation and the one-sided one below can use it. *)
let fk_const_n (_: pval fv) : pcomp fv ncl = PVar (fpv FU)

let lemma_fk_const_n_equivariant (r: pcl_rel_t ncl) (w: pworld)
  : Lemma (pfn_rel_at r w fk_const_n fk_const_n)
  = introduce forall (w': pworld) (y1 y2: pval fv).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
         pcrel r w' (fk_const_n y1) (fk_const_n y2))
    with (introduce _ ==> _
          with (introduce forall (n: nat).
                    pcomp_rel r n w' (PVar (fpv FU)) (PVar (fpv FU))
                with ()))

let lemma_ncl_rel_mono () : Lemma (pcl_mono ncl_rel)
  = introduce forall (n: nat) (w' w: pworld) (c1 c2: ncl).
        (ncl_rel n w c1 c2 /\ pwext w' w ==> ncl_rel n w' c1 c2)
    with (introduce _ ==> _
          with (match c1, c2 with
                | NRet a, NRet b -> lemma_pval_rel_mono w' w a b
                | NResume a, NResume b -> lemma_pval_rel_mono w' w a b
                | _, _ -> ()))

(** `ncl_rel` ignores the step index outright, so downward closure in it is
    immediate. The boundary record carries this alongside `pcl_mono`, so the
    proof has to be in hand where `nboundary` is built. *)
let lemma_ncl_rel_down () : Lemma (pcl_down ncl_rel) = ()

(**
 * **THE REFERENCE LOOKUP IS EQUIVARIANT BY CONSTRUCTION.** PROVED, and it is
 * not a coincidence: `ptable_rel` is DEFINED as "`lookup_handler` through the
 * two tables answers correspondingly", and `pref_lookup` IS `lookup_handler`.
 * So the boundary condition on the lookup is discharged by unfolding, at every
 * clause relation whatever.
 *)
let lemma_pref_lookup_equivariant (#cl: Type) (r: pcl_rel_t cl)
  : Lemma (plookup_equivariant r (pref_lookup #cl))
  = introduce forall (n: nat) (w: pworld) (t1 t2: ptable cl) (eff op: string).
      (ptable_rel r n w t1 t2 ==>
       (match pref_lookup t1 eff op, pref_lookup t2 eff op with
        | None, None -> True
        | Some f1, Some f2 -> f1.kind == f2.kind /\ r n w f1.body f2.body
        | _, _ -> False))
    with (introduce _ ==> _ with ())

(**
 * **AND THE INTERPRETER IS EQUIVARIANT OVER THE TWO-SIDED RELATION.** PROVED,
 * for every shape -- INCLUDING the two that capture, and including the one that
 * hands its captured handle to the continuation.
 *)
#push-options "--fuel 3 --ifuel 3"
let lemma_napply_equivariant () : Lemma (papply_equivariant ncl_rel napply)
  = introduce forall (w: pworld) (c1 c2: ncl) (p1 p2: list (pval fv))
                     (k1 k2: pval fv -> pcomp fv ncl).
      (pwf_world w /\ pclrel ncl_rel w c1 c2 /\ pvals_rel w p1 p2 /\
       pfn_rel_at ncl_rel w k1 k2 ==>
       pcrel ncl_rel w (napply c1 p1 k1) (napply c2 p2 k2))
    with (introduce _ ==> _
          with (lemma_pwext_refl w;
                match c1, c2 with
                | NEcho, NEcho ->
                  (match p1, p2 with
                   | x1 :: _, x2 :: _ -> assert (pval_rel w x1 x2)
                   | [], [] -> assert (pval_rel #fv w (fpv FU) (fpv FU))
                   | _, _ -> ())
                | NRet a, NRet b ->
                  assert (ncl_rel 1 w c1 c2);
                  introduce forall (n: nat). pcomp_rel ncl_rel n w (PVar a) (PVar b)
                  with ()
                | NResume a, NResume b -> assert (ncl_rel 1 w c1 c2)
                | _, _ -> ()))
#pop-options

(**
 * **THE BOUNDARY RECORD, INHABITED.** `ncl_rel` is the data; the three
 * `squash`es are the properties of it. Nothing is admitted or assumed: each
 * field is a lemma with a body.
 *)
let nboundary : pboundary fv ncl = {
  b_rel = ncl_rel;
  b_lk = pref_lookup #ncl;
  b_apply = napply;
  b_mono = lemma_ncl_rel_mono ();
  b_down = lemma_ncl_rel_down ();
  b_lookup = lemma_pref_lookup_equivariant ncl_rel;
  b_apply_eq = lemma_napply_equivariant ();
}

(* ---- and the record is non-vacuous in the way that matters --------- *)

let nw56 : pworld = [(5, 6)]

(**
 * **THE CAPTURING PAIR IS RELATED, AND THE TWO CLAUSES ARE DIFFERENT VALUES.**
 * PROVED. This is what a one-sided condition could not even state.
 *)
let guard_nom_capturing_clauses_related ()
  : Lemma (pwf_world nw56 /\
           (NRet (PCtxKey 5) =!= NRet (PCtxKey 6)) /\
           pclrel ncl_rel nw56 (NRet (PCtxKey 5)) (NRet (PCtxKey 6)) /\
           pclrel ncl_rel nw56 (NResume (PCtxKey 5)) (NResume (PCtxKey 6)) /\
           ~(pclrel ncl_rel ([] <: pworld) (NRet (PCtxKey 5)) (NRet (PCtxKey 6))))
  = assert_norm (pwlookup_l 5 nw56 == Some 6);
    introduce forall (n: nat). ncl_rel n nw56 (NRet (PCtxKey 5)) (NRet (PCtxKey 6))
    with ();
    introduce forall (n: nat).
        ncl_rel n nw56 (NResume (PCtxKey 5)) (NResume (PCtxKey 6))
    with ();
    introduce pclrel ncl_rel ([] <: pworld) (NRet (PCtxKey 5)) (NRet (PCtxKey 6)) ==> False
    with assert (ncl_rel 1 ([] <: pworld) (NRet (PCtxKey 5)) (NRet (PCtxKey 6)))

(** And applying that pair produces RELATED computations, at related arguments
    -- for the shape that returns its capture and for the one that consumes it.
    PROVED, through the boundary condition. *)
let guard_nom_capturing_clauses_apply ()
  : Lemma (pcrel ncl_rel nw56
             (napply (NRet (PCtxKey 5)) [] fk_const_n)
             (napply (NRet (PCtxKey 6)) [] fk_const_n))
  = guard_nom_capturing_clauses_related ();
    lemma_napply_equivariant ();
    lemma_fk_const_n_equivariant ncl_rel nw56;
    assert (pvals_rel #fv nw56 [] [])

(**
 * **THE SAME-CLAUSE CONDITION IS REFUTED HERE TOO, AND BY A WITNESS.** PROVED.
 *
 * Replace the two-sided relation by the one-sided one -- "the two runs hold the
 * very same clause value" -- and the interpreter is no longer equivariant: a
 * clause that captured `PCtxKey 5`, related to ITSELF, forces every world to
 * pin 5 to itself, and a legal world sends it to 6. So the one-sided condition
 * is not merely unable to relate the pair above: it is FALSE of the clause
 * language as soon as capture is expressible in it.
 *)
let ncl_rel_eq : pcl_rel_t ncl = fun _ _ c1 c2 -> c1 == c2

let guard_nom_samecl_refuted ()
  : Lemma (~(papply_equivariant ncl_rel_eq napply))
  = assert_norm (pwlookup_l 5 nw56 == Some 6);
    assert (pwf_world nw56);
    lemma_fk_const_n_equivariant ncl_rel_eq nw56;
    introduce papply_equivariant ncl_rel_eq napply ==> False
    with begin
      assert (pclrel ncl_rel_eq nw56 (NRet (PCtxKey 5)) (NRet (PCtxKey 5)));
      assert (pvals_rel #fv nw56 [] []);
      assert (pcrel ncl_rel_eq nw56
                (napply (NRet (PCtxKey 5)) [] fk_const_n)
                (napply (NRet (PCtxKey 5)) [] fk_const_n));
      assert (pcomp_rel ncl_rel_eq 1 nw56
                (PVar (PCtxKey #fv 5)) (PVar (PCtxKey #fv 5)))
    end

(**
 * **THE COMPARISON, IN ONE STATEMENT.** PROVED. At one world and one pair of
 * clauses: the two-sided relation relates them and the interpreter then
 * produces related results; the one-sided relation does not relate them, and
 * the one-sided boundary condition is false outright.
 *)
let guard_nom_the_boundary_comparison ()
  : Lemma (papply_equivariant ncl_rel napply /\
           plookup_equivariant ncl_rel (pref_lookup #ncl) /\
           pclrel ncl_rel nw56 (NRet (PCtxKey 5)) (NRet (PCtxKey 6)) /\
           (NRet (PCtxKey 5) =!= NRet (PCtxKey 6)) /\
           ~(papply_equivariant ncl_rel_eq napply) /\
           ~(papply_equivariant fcl_rel fapply))
  = lemma_napply_equivariant ();
    lemma_pref_lookup_equivariant ncl_rel;
    guard_nom_capturing_clauses_related ();
    guard_nom_samecl_refuted ();
    guard_nom_fapply_not_equivariant ()

(* ================================================================== *)
(*  B2b.2 -- THE THEOREM, AT THE FIXTURES AND AT THE BOUNDARY          *)
(*                                                                     *)
(*  Two instantiations, and each answers a different question about     *)
(*  the theorem above.                                                  *)
(*                                                                     *)
(*    - THE COUNTEREXAMPLE PAIR, AS A COROLLARY.  B2b.1 established     *)
(*      the consequent of the nominal observation for `ce_l` / `ce_r`   *)
(*      with every witness written down.  Here the same conjunction is  *)
(*      DERIVED: the world is not written anywhere, it is whatever the  *)
(*      theorem's induction accumulated.  What is still computed rather *)
(*      than proved is the two sides' PREFIXES -- eleven transitions on *)
(*      the left, two on the right, to a COMMON configuration -- and    *)
(*      those are runs of the machine, not step constants in a          *)
(*      relational statement.  `lemma_prun_split` is what composes a    *)
(*      prefix with the theorem's suffix.                               *)
(*                                                                     *)
(*    - THE BOUNDARY.  `nboundary` is the record over a clause language *)
(*      that CAPTURES HANDLES.  The theorem is discharged at it, at a   *)
(*      program that produces a context, and then at a PAIR OF RUNS     *)
(*      HOLDING DIFFERENT NAMES: two clauses that captured `PCtxKey 5`  *)
(*      and `PCtxKey 6`, dispatched through two related tables, at the  *)
(*      world `nw56` which is not the identity.  Both runs answer, with *)
(*      the two different handles, and the theorem relates them.  That  *)
(*      is what says the boundary hypotheses are not vacuous.           *)
(* ================================================================== *)

(* ================================================================== *)
(*  CONDITION 3: THE COUNTEREXAMPLE PAIR, AS A COROLLARY               *)
(*                                                                     *)
(*  `guard_nom_ce_related` established the consequent of the nominal    *)
(*  observation at one configuration with EVERY witness written down:   *)
(*  the right-hand run by `assert_norm`, the world `fce_w` by hand, and *)
(*  the store correspondence checked entry by entry.  What follows      *)
(*  derives the same conjunction from the fundamental theorem, and      *)
(*  writes down NO world at all.                                        *)
(*                                                                     *)
(*  ONE THING IS STILL COMPUTED RATHER THAN PROVED, and it is stated    *)
(*  rather than hidden: the two sides reach a COMMON configuration in   *)
(*  DIFFERENT numbers of transitions -- eleven on the left, two on the  *)
(*  right -- and those two prefixes are checked by running the machine. *)
(*  They are not step constants in a relational statement: the theorem  *)
(*  is applied to the common suffix at ONE fuel, and `lemma_prun_split` *)
(*  is what composes a prefix with it.  Nothing below relates the two   *)
(*  sides' transition counts.                                           *)
(*                                                                     *)
(*  AND THE CLAUSE INTERPRETER IS `fapply0`, NOT `fapply`.  `fapply` is *)
(*  PROVED not equivariant (`guard_nom_fapply_not_equivariant`), so the *)
(*  theorem is not available at it and no amount of arrangement would   *)
(*  make it so.  Neither run performs an operation, so neither ever     *)
(*  reaches the interpreter, and the two runs are LITERALLY EQUAL --    *)
(*  checked by running both machines side by side, not argued.          *)
(* ================================================================== *)

(** A clause interpreter that looks at nothing. Equivariant for the reason
    `fk_const` is: it returns one closed value. *)
let fapply0 : papply_t fv fcl = fun _ _ _ -> PVar (fpv FU)

let lemma_fapply0_equivariant () : Lemma (papply_equivariant fcl_rel fapply0)
  = introduce forall (w: pworld) (c1 c2: fcl) (p1 p2: list (pval fv))
                     (k1 k2: pval fv -> pcomp fv fcl).
      (pwf_world w /\ pclrel fcl_rel w c1 c2 /\ pvals_rel w p1 p2 /\
       pfn_rel_at fcl_rel w k1 k2 ==>
       pcrel fcl_rel w (fapply0 c1 p1 k1) (fapply0 c2 p2 k2))
    with (introduce _ ==> _
          with lemma_pcrel_var #fv #fcl fcl_rel w (fpv FU) (fpv FU))

let lemma_fcl_rel_down () : Lemma (pcl_down fcl_rel) = ()

(** The common configuration the two sides reach: the same computation, the same
    ambient stack, and two stores that differ in ONE ENTRY -- the context the
    left allocated and threw away. *)
let ce_cfl : pconf fv fcl =
  { st = PStep (PVar fone) fk_new; store = [(0, fce_cx (FI 1))]; next = 1 }
let ce_cfr : pconf fv fcl =
  { st = PStep (PVar fone) fk_new; store = []; next = 0 }

let guard_nom_ce_prefixes ()
  : Lemma (prun flook fapply0 11 ce_cf_l == (ce_cfl, []) /\
           prun flook fapply0 2 ce_cf_r == (ce_cfr, []))
  = assert_norm (prun flook fapply0 11 ce_cf_l == (ce_cfl, []));
    assert_norm (prun flook fapply0 2 ce_cf_r == (ce_cfr, []))

(** **The two are RELATED AT THE EMPTY WORLD.** PROVED. The left's extra entry is
    named by no key the world speaks for, so `psrel` never looks at it -- and the
    world is `[]`, which is `panchor` of the store both runs started from. *)
let guard_nom_ce_common_related ()
  : Lemma (pcfrel fcl_rel ([] <: pworld) ce_cfl ce_cfr)
  = guard_nom_fk_new_equivariant ();
    assert (pkrel fcl_rel ([] <: pworld) fk_new fk_new);
    lemma_pcrel_var #fv #fcl fcl_rel [] fone fone;
    assert (psrel fcl_rel ([] <: pworld) ce_cfl.store ce_cfr.store)

(**
 * **PAIR 1, RELATED -- AS A COROLLARY OF THE FUNDAMENTAL THEOREM.** PROVED.
 *
 * This is `guard_nom_ce_related`'s conclusion with the witnesses EXISTENTIALLY
 * QUANTIFIED and supplied by the theorem rather than by hand. The world is not
 * written anywhere; it is whatever the theorem's induction accumulated, which by
 * construction is the starting world plus one pair per allocation.
 *)
let guard_nom_ce_related_by_theorem ()
  : Lemma (exists (x2: pval fv) (s2': pstore fv fcl) (w: pworld).
             pnconverges flook fapply ce_cf_r [] x2 s2' /\
             pwf_world w /\ pwext w (panchor ([] <: pstore fv fcl)) /\
             pval_rel w (PCtxKey 1) x2 /\ psrel fcl_rel w fce_sl s2')
  = lemma_fcl_rel_mono ();
    lemma_fcl_rel_down ();
    lemma_flook_equivariant ();
    lemma_fapply0_equivariant ();
    guard_nom_ce_prefixes ();
    guard_nom_ce_common_related ();
    assert_norm (panchor ([] <: pstore fv fcl) == ([] <: pworld));
    assert_norm ((fst (prun flook fapply0 189 ce_cfl)).st == PDone (PCtxKey 1));
    assert_norm ((fst (prun flook fapply0 189 ce_cfl)).store == fce_sl);
    assert_norm (snd (prun flook fapply0 189 ce_cfl) == []);
    lemma_prun_compat fcl_rel flook fapply0 189 [] ce_cfl ce_cfr;
    eliminate exists (w': pworld).
        (pwf_world w' /\ pwext w' ([] <: pworld) /\
         pcfrel fcl_rel w' (fst (prun flook fapply0 189 ce_cfl))
                           (fst (prun flook fapply0 189 ce_cfr)))
    with begin
      let e1 = fst (prun flook fapply0 189 ce_cfl) in
      let e2 = fst (prun flook fapply0 189 ce_cfr) in
      pcfrel_unfold fcl_rel w' e1 e2 ();
      lemma_pstrel_done_inv fcl_rel w' (PCtxKey 1) e2.st;
      let x2 = PDone?.value e2.st in
      lemma_prun_split flook fapply0 2 189 ce_cf_r;
      assert (prun flook fapply0 191 ce_cf_r == (e2, []));
      assert_norm (prun flook fapply 191 ce_cf_r == prun flook fapply0 191 ce_cf_r);
      lemma_pnconverges_at flook fapply ce_cf_r 191 [] x2 e2.store;
      introduce exists (y2: pval fv) (t2: pstore fv fcl) (ww: pworld).
          (pnconverges flook fapply ce_cf_r [] y2 t2 /\
           pwf_world ww /\ pwext ww (panchor ([] <: pstore fv fcl)) /\
           pval_rel ww (PCtxKey 1) y2 /\ psrel fcl_rel ww fce_sl t2)
      with x2 e2.store w' and ()
    end

(* ================================================================== *)
(*  CONDITION 4: THE THEOREM AT `nboundary`                            *)
(*                                                                     *)
(*  `lemma_ncl_rel_down` is proved further up, beside                  *)
(*  `lemma_ncl_rel_mono`: `nboundary` carries downward closure as a    *)
(*  field, so the proof is needed before the record is built.          *)
(* ================================================================== *)

(** A table with no clauses at all, at the capturing clause language. Its lookups
    are `None` everywhere -- read off `mk_handlers`' refinement and
    `assoc_clause []` -- so it is related to itself at every world. *)
let ntbl0 : ptable ncl = { hs = mk_handlers (fun (_: ncl) -> KFast) []; binds = [] }

let lemma_ntbl0_selfrel (n: nat) (w: pworld)
  : Lemma (ptable_rel ncl_rel n w ntbl0 ntbl0)
  = introduce forall (eff op: string).
      (match lookup_handler ntbl0.hs eff op, lookup_handler ntbl0.hs eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ ncl_rel n w f1.body f2.body
       | _, _ -> False)
    with assert (lookup_handler ntbl0.hs eff op == None)

(** The smallest plan, at `ncl`: no layers, an owner with no return clause. *)
let nplan : plan fv ncl = Plan [] (POwner ntbl0 None PFamily)

let lemma_nplan_selfrel (n: nat) (w: pworld)
  : Lemma (pplan_rel ncl_rel n w nplan nplan)
  = if n = 0 then () else lemma_ntbl0_selfrel n w

(** A program that PRODUCES A CONTEXT: it enters a scope, and the scope's floor
    allocates. Nothing in it mentions a handle, so it is related to itself at
    every world. *)
let nprog : pcomp fv ncl = PEnterCtx nplan (PVar (fpv (FI 1)))

let lemma_nprog_selfrel (w: pworld) : Lemma (pcrel ncl_rel w nprog nprog)
  = introduce forall (n: nat). pcomp_rel ncl_rel n w nprog nprog
    with (if n = 0 then () else lemma_nplan_selfrel (n - 1) w)

(**
 * **THE THEOREM, INSTANTIATED AT `nboundary`.** PROVED.
 *
 * `nboundary` is the record over a clause language that CAPTURES HANDLES, and
 * the four conditions it carries -- monotonicity, downward closure, the lookup,
 * the interpreter -- are exactly the ones the fundamental theorem consumes.
 * Discharging the theorem's hypotheses at it is what says they are not vacuous.
 *
 * Nothing is left over: the only hypothesis this guard supplies is that `nprog`
 * is related to itself, which is a fact about the PROGRAM, not about the
 * boundary.
 *)
let guard_nom_fund_at_nboundary ()
  : Lemma (pnobs_tr_le nboundary nprog nprog)
  = introduce forall (w: pworld). (pwf_world w ==> pcrel ncl_rel w nprog nprog)
    with (introduce _ ==> _ with lemma_nprog_selfrel w);
    lemma_pnobs_tr_le_of_crel nboundary nprog nprog

(* ---- and at a pair of runs that hold DIFFERENT NAMES ---------------- *)

(** A table with one clause, and the clause CAPTURES a value -- a handle, in the
    instance below. Two such tables are related exactly when the world relates
    their captures: `ncl_rel` on `NRet` IS `pval_rel`. *)
let ncap_tbl (cap: pval fv) : ptable ncl =
  { hs = mk_handlers (fun (_: ncl) -> KFast) [("E", "op", NRet cap)]; binds = ["E"] }

let lemma_ncap_tbl_rel (n: nat) (w: pworld) (a b: pval fv)
  : Lemma (requires pval_rel w a b)
          (ensures ptable_rel ncl_rel n w (ncap_tbl a) (ncap_tbl b))
  = introduce forall (eff op: string).
      (match lookup_handler (ncap_tbl a).hs eff op, lookup_handler (ncap_tbl b).hs eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ ncl_rel n w f1.body f2.body
       | _, _ -> False)
    with (assert (lookup_handler (ncap_tbl a).hs eff op
                  == map_opt (found_of (fun (_: ncl) -> KFast))
                             (assoc_clause [("E", "op", NRet a)] eff op));
          assert (lookup_handler (ncap_tbl b).hs eff op
                  == map_opt (found_of (fun (_: ncl) -> KFast))
                             (assoc_clause [("E", "op", NRet b)] eff op)))

let ncap_k (cap: pval fv) : pstack fv ncl = [PPromptF (ncap_tbl cap) None PMono]

let ncap_cf (cap: pval fv) (sto: pstore fv ncl) (nx: nat) : pconf fv ncl =
  { st = PStep (PPerform "E" "op" []) (ncap_k cap); store = sto; next = nx }

let ncap_s1 : pstore fv ncl = [(5, PCtxDone (fpv FU))]
let ncap_s2 : pstore fv ncl = [(6, PCtxDone (fpv FU))]

let ncap_cf1 : pconf fv ncl = ncap_cf (PCtxKey 5) ncap_s1 6
let ncap_cf2 : pconf fv ncl = ncap_cf (PCtxKey 6) ncap_s2 7

(** **Two configurations that hold DIFFERENT HANDLES, related by a world that is
    not the identity.** PROVED. The clause on the left captured the key `5`, the
    one on the right captured `6`, and `nw56` is what says they correspond. *)
let guard_nom_nboundary_capture_related ()
  : Lemma (pwf_world nw56 /\ pcfrel ncl_rel nw56 ncap_cf1 ncap_cf2)
  = assert_norm (pwlookup_l 5 nw56 == Some 6);
    assert_norm (pwlookup_r 6 nw56 == Some 5);
    assert (pwf_world nw56);
    assert (pval_rel #fv nw56 (PCtxKey 5) (PCtxKey 6));
    lemma_ncap_tbl_rel 0 nw56 (PCtxKey 5) (PCtxKey 6);
    introduce forall (n: nat). ptable_rel ncl_rel n nw56 (ncap_tbl (PCtxKey 5))
                                                         (ncap_tbl (PCtxKey 6))
    with lemma_ncap_tbl_rel n nw56 (PCtxKey 5) (PCtxKey 6);
    lemma_pfrel_prompt #fv #ncl ncl_rel nw56 (ncap_tbl (PCtxKey 5)) (ncap_tbl (PCtxKey 6))
                       None None PMono;
    lemma_pkrel_nil #fv #ncl ncl_rel nw56;
    lemma_pkrel_cons ncl_rel nw56 (PPromptF (ncap_tbl (PCtxKey 5)) None PMono)
                                  (PPromptF (ncap_tbl (PCtxKey 6)) None PMono)
                                  ([] <: pstack fv ncl) ([] <: pstack fv ncl);
    introduce forall (n: nat).
      pcomp_rel #fv #ncl ncl_rel n nw56 (PPerform "E" "op" []) (PPerform "E" "op" [])
    with ();
    lemma_pxrel_done #fv #ncl ncl_rel nw56 (fpv FU) (fpv FU);
    introduce forall (i j: nat).
        (pwlookup_l i nw56 == Some j ==>
         (Some? (pstore_lookup i ncap_s1) /\ Some? (pstore_lookup j ncap_s2) /\
          pxrel ncl_rel nw56 (psget i ncap_s1) (psget j ncap_s2)))
    with (introduce _ ==> _
          with (assert (i == 5 /\ j == 6);
                assert_norm (psget 5 ncap_s1 == PCtxDone (fpv FU));
                assert_norm (psget 6 ncap_s2 == PCtxDone (fpv FU))))

(**
 * **AND THE THEOREM APPLIES TO THEM, AT EVERY FUEL.** PROVED, at `nboundary`
 * itself -- its lookup, its interpreter and its clause relation, with the three
 * conditions the record carries doing the work.
 *
 * This is the non-vacuity that matters: the hypotheses are met by a pair of
 * configurations whose relation is NOT the identity on names, whose clauses are
 * two DIFFERENT values, and whose dispatch runs the interpreter on them.
 *)
let guard_nom_nboundary_capture_runs (fuel: nat)
  : Lemma (snd (prun nboundary.b_lk nboundary.b_apply fuel ncap_cf1)
             == snd (prun nboundary.b_lk nboundary.b_apply fuel ncap_cf2) /\
           (exists (w': pworld).
              pwf_world w' /\ pwext w' nw56 /\
              pcfrel ncl_rel w' (fst (prun nboundary.b_lk nboundary.b_apply fuel ncap_cf1))
                                (fst (prun nboundary.b_lk nboundary.b_apply fuel ncap_cf2))))
  = let _ : squash (pcl_mono nboundary.b_rel) = nboundary.b_mono in
    let _ : squash (plookup_equivariant nboundary.b_rel nboundary.b_lk) = nboundary.b_lookup in
    let _ : squash (papply_equivariant nboundary.b_rel nboundary.b_apply) = nboundary.b_apply_eq in
    lemma_ncl_rel_down ();
    guard_nom_nboundary_capture_related ();
    lemma_prun_compat ncl_rel nboundary.b_lk nboundary.b_apply fuel nw56 ncap_cf1 ncap_cf2

(** **And the two runs really do answer with DIFFERENT NAMES.** PROVED: two
    transitions on each side -- dispatch through the prompt, then the value --
    and the answers are the two captured handles, which are two different
    values. `assert_norm` is not available here (`lookup_handler` and
    `mk_handlers` are abstract), so the dispatch is read off `mk_handlers`'
    refinement instead. *)
let guard_nom_nboundary_capture_answers ()
  : Lemma ((fst (prun nboundary.b_lk nboundary.b_apply 2 ncap_cf1)).st
             == PDone (PCtxKey 5) /\
           (fst (prun nboundary.b_lk nboundary.b_apply 2 ncap_cf2)).st
             == PDone (PCtxKey 6) /\
           snd (prun nboundary.b_lk nboundary.b_apply 2 ncap_cf1) == [] /\
           (PCtxKey #fv 5 =!= PCtxKey #fv 6))
  = assert (lookup_handler (ncap_tbl (PCtxKey 5)).hs "E" "op"
            == map_opt (found_of (fun (_: ncl) -> KFast))
                       (assoc_clause [("E", "op", NRet (PCtxKey 5))] "E" "op"));
    assert (lookup_handler (ncap_tbl (PCtxKey 6)).hs "E" "op"
            == map_opt (found_of (fun (_: ncl) -> KFast))
                       (assoc_clause [("E", "op", NRet (PCtxKey 6))] "E" "op"));
    assert (nboundary.b_lk (ncap_tbl (PCtxKey 5)) "E" "op"
            == Some ({ body = NRet (PCtxKey 5); kind = KFast }));
    assert (nboundary.b_lk (ncap_tbl (PCtxKey 6)) "E" "op"
            == Some ({ body = NRet (PCtxKey 6); kind = KFast }))

(* ================================================================== *)
(*  B2b.1 AND B2b.2: WHAT IS CHECKED, AND WHAT IS NOT                  *)
(*                                                                     *)
(*  A ledger for the nominal layer, in the same spirit as the header's  *)
(*  list of what this file states rather than proves.  Every line       *)
(*  marked PROVED names a definition above with a body; every line      *)
(*  marked NOT REACHED says why.  The B2b.2 entries are marked as such; *)
(*  everything else is B2b.1's and is unchanged.                        *)
(*                                                                     *)
(*  PROVED                                                              *)
(*                                                                     *)
(*   - the world layer: `pwf_world`'s biconditional makes a world a     *)
(*     partial bijection; `pwextend` adds one pair; `panchor` pins a    *)
(*     store's own keys to themselves                                   *)
(*     (`lemma_pwextend_wf`, `lemma_panchor_wf`, `lemma_panchor_pins`); *)
(*   - re-anchoring is UNSOUND, in general and at the counterexample's  *)
(*     own final store (`guard_nom_no_reanchoring`,                     *)
(*     `guard_nom_reanchor_pins_the_garbage`,                           *)
(*     `guard_nom_ce_not_a_reanchoring`);                               *)
(*   - the step-indexed, world-indexed relation is Kripke monotone,     *)
(*     given a monotone clause relation                                 *)
(*     (`lemma_pcomp_rel_mono` and the six lemmas it recurses with);    *)
(*   - the store lemmas: garbage is ignored SYMMETRICALLY, an           *)
(*     allocation extends the world by EXACTLY ONE PAIR and leaves      *)
(*     every other key unspoken for (`lemma_psrel_garbage`,             *)
(*     `guard_nom_alloc_extends_by_one_pair`);                          *)
(*   - the sibling algebra: the join exists exactly when two            *)
(*     extensions are compatible, compatibility is NECESSARY, a         *)
(*     monotone allocator delivers it for free, and a reset allocator   *)
(*     destroys it (`lemma_pwunion_wf`, `lemma_pwcompat_necessary`,     *)
(*     `lemma_pwcompat_of_ranges`, `guard_nom_fork_no_join`);           *)
(*   - the boundary record is INHABITED, at a clause language that      *)
(*     captures handles, and the one-sided alternative is REFUTED       *)
(*     there (`nboundary`, `guard_nom_the_boundary_comparison`);        *)
(*   - the four counterexample pairs -- six law statements -- have      *)
(*     answers that CORRESPOND UNDER AN EXHIBITED WORLD at the          *)
(*     configurations that refute `pobs_tr_eq`, with the same trace,    *)
(*     the stores related on the world's domain, and the world          *)
(*     extending the starting anchor (`guard_nom_the_six`);             *)
(*   - the configuration is INSIDE the nominal observation's            *)
(*     quantifier: the ambient stack that defeated the old relation is  *)
(*     equivariant (`guard_nom_fk_new_equivariant`), so the repair      *)
(*     does not work by exclusion;                                      *)
(*   - the negatives (`guard_nom_the_negatives`).                       *)
(*                                                                     *)
(*  PROVED IN B2b.2 -- THE FUNDAMENTAL THEOREM                          *)
(*                                                                     *)
(*   - TRANSITION COMPATIBILITY, for every rule of the machine:         *)
(*     two configurations related at `w` step to two configurations     *)
(*     related at a world EXTENDING `w`, and the two steps emit the     *)
(*     SAME event list (`lemma_pstep_tr_compat`, and the rule lemmas   *)
(*     it dispatches to -- one per node, and two more beneath the       *)
(*     value rule).  The world grows by exactly one pair at each of     *)
(*     the three rules that allocate -- the scope                       *)
(*     floor, production (`lemma_pyield_compat`) and `bindScope`        *)
(*     (`lemma_step_extendctxc`) -- and by nothing anywhere else;       *)
(*   - THE FUNDAMENTAL THEOREM: the same, for `prun` at any fuel, with  *)
(*     the trace compared by EQUALITY (`lemma_prun_compat`).  The       *)
(*     induction is on the fuel BOTH sides are run at, so no transition *)
(*     count is related to any other and no step constant appears;      *)
(*   - **`pnobs_tr_le` IS NOW DERIVABLE**: two computations related at  *)
(*     every well-formed world satisfy it, AT EVERY equivariant ambient *)
(*     stack, every equivariant initial store and every counter fresh   *)
(*     for it -- the universal quantification B2b.1 could not reach     *)
(*     (`lemma_pnobs_tr_le_of_crel`).  It requires NOTHING BEYOND THE   *)
(*     BOUNDARY RECORD: downward closure is the field `b_down`, so a    *)
(*     caller holding a `pboundary` and a relatedness proof has no      *)
(*     further hypothesis to discharge;                                 *)
(*   - the auxiliary compatibilities the rules are made of, each an     *)
(*     induction of its own: the four stack searches                    *)
(*     (`lemma_pfind_prompt_rel`, `lemma_pfind_param_rel`,              *)
(*     `lemma_pset_param_rel`, `lemma_pfind_mode_rel`,                  *)
(*     `lemma_pcut_scope_rel`), plan construction and its three         *)
(*     projections (`lemma_plan_of_rel`, `lemma_plan_enter_frames_rel`  *)
(*     and the two beside it), handle resolution                        *)
(*     (`lemma_presolve_rel`) and the three consuming meanings          *)
(*     (`lemma_ctx_drive_rel`, `lemma_extend_ctx_C_rel`);               *)
(*   - two RELATED TABLES BLOCK THE SAME EFFECTS and therefore agree on *)
(*     borrowability and on the classification of a prompt              *)
(*     (`lemma_blocking_effects_agree`, `lemma_classify_agree`);        *)
(*   - runs compose: `a + b` transitions are `a` then `b`, and the      *)
(*     trace is the concatenation (`lemma_prun_split`);                 *)
(*   - THE COUNTEREXAMPLE PAIR AS A COROLLARY: the conjunction          *)
(*     `guard_nom_ce_related` established by hand is DERIVED from the   *)
(*     theorem, with the world existentially quantified and supplied by *)
(*     the induction rather than written down                           *)
(*     (`guard_nom_ce_related_by_theorem`);                             *)
(*   - THE THEOREM AT `nboundary`: discharged at a program that         *)
(*     produces a context (`guard_nom_fund_at_nboundary`), and at a     *)
(*     PAIR OF RUNS HOLDING DIFFERENT NAMES -- two clauses that         *)
(*     captured `PCtxKey 5` and `PCtxKey 6`, dispatched through two     *)
(*     related tables at a world that is not the identity, both         *)
(*     answering with their own handle                                  *)
(*     (`guard_nom_nboundary_capture_related`,                          *)
(*     `guard_nom_nboundary_capture_runs`,                              *)
(*     `guard_nom_nboundary_capture_answers`).                          *)
(*                                                                     *)
(*  NOT REACHED, AND NAMED                                              *)
(*                                                                     *)
(*   - **`pnobs_tr_eq` IS STILL NOT PROVED OF ANY PAIR, AND NEITHER IS  *)
(*     `pnobs_tr_le`.**  What B2b.2 proves is the IMPLICATION:          *)
(*     relatedness at every world gives the observation.  The two sides *)
(*     of a LAW are not related as computations -- they are different   *)
(*     nodes, and `pcomp_rel` relates a node only to the same node --   *)
(*     so obtaining `pnobs_tr_le` for a law's two sides means reducing  *)
(*     both to a common configuration first.  That is done for the      *)
(*     counterexample pair AT ONE CONFIGURATION                         *)
(*     (`guard_nom_ce_related_by_theorem`) and NOT in general: the      *)
(*     general version needs the two prefixes stepped SYMBOLICALLY, in  *)
(*     an arbitrary ambient stack and store, which is the next gate and *)
(*     is exactly "proving the laws";                                   *)
(*   - consequently the five retargeted laws are STATED and not proved, *)
(*     which is what this gate's scope says they should be;             *)
(*   - WHETHER `pcl_down` IS DERIVABLE from the other three conditions  *)
(*     the record carries is NOT SETTLED here, in either direction.     *)
(*     The record now carries it as `b_down` -- it constrains the       *)
(*     RELATION alone, exactly as `b_mono` does, and both the           *)
(*     fundamental theorem and the observation corollary need it, so    *)
(*     leaving it loose meant a use site could forget it.  It is used   *)
(*     at index ZERO only, where `ptable_rel` is not trivial and a      *)
(*     table inverted out of a frame speaks only from index 1 up, and   *)
(*     it is PROVED of both inhabited clause relations                  *)
(*     (`lemma_fcl_rel_down`, `lemma_ncl_rel_down`), which ignore the   *)
(*     index -- so the field adds no trusted assumption.  Should it     *)
(*     turn out derivable, `b_down` becomes redundant rather than       *)
(*     wrong.  The two transition theorems are STILL STATED AT A BARE   *)
(*     RELATION (`lemma_pstep_tr_compat`, `lemma_prun_compat`) and      *)
(*     still take `pcl_down r` explicitly: they are usable without a    *)
(*     boundary, and that is deliberate;                                *)
(*   - REJECTIONS ARE COMPARED WITH THE BLOCKING LABELS AS A SET, not   *)
(*     as a list (`prej_rel`).  `blocking_effects` is pinned by its     *)
(*     refinement as a SET, so two tables that answer every lookup      *)
(*     alike may report the labels in a different order and no proof    *)
(*     can close that gap; `plan_layers` puts the list it is given into *)
(*     the rejection verbatim.  A rejection is terminal and is not a    *)
(*     `PDone`, so nothing `pnconverges` looks at can see the           *)
(*     difference -- but the transition theorem's conclusion is         *)
(*     therefore weaker on that one state than equality would be, and   *)
(*     that is recorded rather than glossed;                            *)
(*   - the counterexample corollary runs the two programs under         *)
(*     `fapply0`, a constant interpreter, and not under `fapply`, which *)
(*     is PROVED not equivariant.  The two runs are checked to be       *)
(*     LITERALLY EQUAL at the fuel used, by running both machines; that *)
(*     is a computation on two closed programs and not an argument      *)
(*     about which clauses are reachable in general;                    *)
(*   - the two PREFIXES in that corollary -- eleven transitions on the  *)
(*     left, two on the right -- are computed by `assert_norm` rather   *)
(*     than derived.  They are runs of the machine on closed            *)
(*     configurations; no relational statement below mentions either    *)
(*     number, and `lemma_prun_split` is what joins a prefix to the     *)
(*     theorem's suffix;                                                *)
(*   - no relation is claimed between `pobs_tr_eq` and `pnobs_tr_eq`,   *)
(*     in either direction.  Neither implication is established and     *)
(*     neither is obvious; see the block comment on the retargeted      *)
(*     laws;                                                            *)
(*   - "exactly the UNREACHABLE store entries are ignored" is not       *)
(*     proved in general, and cannot be stated as a computable          *)
(*     property here: a `PCtxRequests` carries a `post` whose returned  *)
(*     keys cannot be enumerated.  What is proved is the domain         *)
(*     restriction, its symmetry, and the instance at the               *)
(*     counterexample (`guard_nom_only_garbage_ignored`);               *)
(*   - `fcl_rel` is equality, which is sound HERE because no `fcl`      *)
(*     constructor carries a `pval` -- a fact read off the type         *)
(*     declaration, not a proposition proved.  The general case is      *)
(*     `ncl`, where the relation is not equality and equality is        *)
(*     REFUTED (`guard_nom_samecl_refuted`);                            *)
(*   - `fapply` is NOT equivariant and the negation is PROVED           *)
(*     (`guard_nom_fapply_not_equivariant`).  So no `pboundary fv fcl`  *)
(*     exists with `b_apply = fapply`, and the nominal observation is   *)
(*     not available at the fixtures' own clause language.  It costs    *)
(*     the results above nothing -- none of the four counterexample     *)
(*     pairs performs an operation, so `fapply` is never reached -- but *)
(*     it is a real limit and is recorded as one rather than worked     *)
(*     around.                                                          *)
(*                                                                     *)
(*  WHAT DID NOT CHANGE, and is worth saying because a repair to an     *)
(*  observation is exactly the kind of change that quietly weakens      *)
(*  things:                                                             *)
(*                                                                     *)
(*   - `prun`, `pstep_tr`, `pconverges_tr`, `pobs_tr_le` and            *)
(*     `pobs_tr_eq` are untouched, so every earlier result stated over  *)
(*     them means what it meant;                                        *)
(*   - the trace is compared by EQUALITY in the nominal observation     *)
(*     too (`guard_nom_trace_not_weakened`), and the residual /         *)
(*     suspension separation survives in the strong form: the           *)
(*     suspension does not converge with the residual's trace AT ALL,   *)
(*     so no world can rescue it (`guard_nom_trace_separation_survives`);*)
(*   - production is still an object-language transition, `ctx_ops` has *)
(*     gained no interpreter argument, `presolve` is still given no     *)
(*     stack, and `lemma_reachable_residual_wf` still has no            *)
(*     `requires`;                                                      *)
(*   - the counter is mentioned NOWHERE in the nominal observation, on  *)
(*     either side, and no machine-specific step constant occurs in any *)
(*     proof above: each side's step count is existentially quantified  *)
(*     inside `pnconverges`, independently.                             *)
(*                                                                     *)
(*  AND WHAT B2b.2 DID NOT CHANGE:                                      *)
(*                                                                     *)
(*   - no definition of B2b.1 or earlier was edited.  The relation,     *)
(*     the world, the anchor, the boundary record and the observation   *)
(*     are the ones B2b.1 left.  The two `_p` propositions are the      *)
(*     same propositions with a `{:pattern}`, and every `_unfold` is    *)
(*     the same proposition unfolded; each is related to its original   *)
(*     BY CONVERSION -- the casts have no proof obligation at all, so   *)
(*     there is no room for a discrepancy between them;                 *)
(*   - no `rlimit`, `fuel` or `ifuel` was raised anywhere in B2b.2:     *)
(*     the section adds no `#push-options` at all;                      *)
(*   - `prun`, `pstep`, `pstep_tr` and `pconf` are untouched, so the    *)
(*     theorem is about the machine the rest of the file runs.          *)
(* ================================================================== *)

(**
 * **THE GATE, IN ONE CHECKED STATEMENT.** PROVED -- every conjunct is one of
 * the guards above.
 *)
let guard_nom_b2b1 ()
  : Lemma (
      // 1: the six counterexamples correspond under an exhibited world
      pval_rel #fv fce_w (PCtxKey 1) (PCtxKey 0) /\
      psrel fcl_rel fce_w fce_sl fce_sr /\
      pval_rel #fv fce_aa_w (PCtxKey 2) (PCtxKey 1) /\
      psrel fcl_rel fce_aa_w fce_aa_sl fce_aa_sr /\
      pval_rel #fv fce_ac_w (PCtxKey 2) (PCtxKey 0) /\
      psrel fcl_rel fce_ac_w fce_aa_sl fce_sr /\
      // ... and the offending ambient continuation is inside the quantifier
      pequivariant_k fcl_rel fk_new /\
      // 2: B1.7's two live handles are not collapsed
      (forall (w: pworld). pwext w (panchor fs17) ==>
         ~(pval_rel #fv w (PCtxKey 0) (PCtxKey 1))) /\
      // 3: aliasing
      (forall (w: pworld) (a1 a2 b1 b2: pval fv).
         pwf_world w /\ pval_rel w a1 a2 /\ pval_rel w b1 b2 ==>
         ((a1 == b1) <==> (a2 == b2))) /\
      // 4: contexts that behave differently
      (forall (w: pworld) (a: fv).
         pwf_world w ==> ~(pxrel fcl_rel w (fce_cx a) (fce_cx_b a))) /\
      // 5: forged and stale handles
      (forall (w: pworld) (n1 n2 i: nat) (x2: pval fv).
         pwbound w n1 n2 /\ i >= n1 ==> ~(pval_rel #fv w (PCtxKey i) x2)) /\
      // 7: the trace-based separation survives
      (forall (x2: pval fv) (s2: pstore fv fcl).
         ~(pnconverges flook fapply (pload prog_susp)
                       ["prefix"; "c1"; "c2"] x2 s2)) /\
      // and re-anchoring is refuted, before anything positive rests on it
      ~(pwext fce_w (panchor fce_sl)))
  = guard_nom_the_six ();
    guard_nom_fk_new_equivariant ();
    guard_nom_the_negatives ();
    guard_nom_ce_not_a_reanchoring ()

(**
 * **B2b.2, IN ONE CHECKED STATEMENT.** PROVED -- the two theorems, at an
 * arbitrary clause relation, lookup and interpreter satisfying the boundary's
 * conditions, together with the derivability of the nominal observation from
 * relatedness. Nothing here is specific to a fixture, and nothing here mentions
 * a transition count.
 *)
let guard_nom_b2b2 (#v #cl: Type) (r: pcl_rel_t cl) (lk: plookup_t cl)
                   (apply: papply_t v cl)
  : Lemma (requires pcl_mono r /\ pcl_down r /\
                    plookup_equivariant r lk /\ papply_equivariant r apply)
          (ensures
            // 1: one step of related configurations goes to related
            //    configurations, with the same trace and a world extension
            (forall (w: pworld) (cf1 cf2: pconf v cl).
               pwf_world w /\ pcfrel r w cf1 cf2 ==>
               pstep_compat_at r lk apply w cf1 cf2) /\
            // 2: and that lifts to finite runs
            (forall (fuel: nat) (w: pworld) (cf1 cf2: pconf v cl).
               pwf_world w /\ pcfrel r w cf1 cf2 ==>
               (snd (prun lk apply fuel cf1) == snd (prun lk apply fuel cf2) /\
                (exists (w': pworld).
                   pwf_world w' /\ pwext w' w /\
                   pcfrel r w' (fst (prun lk apply fuel cf1))
                               (fst (prun lk apply fuel cf2))))) /\
            // 2': so `pnobs_tr_le`'s universal quantification is derivable
            (forall (b: pboundary v cl) (c1 c2: pcomp v cl).
               (forall (w: pworld). pwf_world w ==> pcrel b.b_rel w c1 c2) ==>
               pnobs_tr_le b c1 c2))
  = introduce forall (w: pworld) (cf1 cf2: pconf v cl).
        (pwf_world w /\ pcfrel r w cf1 cf2 ==> pstep_compat_at r lk apply w cf1 cf2)
    with (introduce _ ==> _ with lemma_pstep_tr_compat r lk apply w cf1 cf2);
    introduce forall (fuel: nat) (w: pworld) (cf1 cf2: pconf v cl).
        (pwf_world w /\ pcfrel r w cf1 cf2 ==>
         (snd (prun lk apply fuel cf1) == snd (prun lk apply fuel cf2) /\
          (exists (w': pworld).
             pwf_world w' /\ pwext w' w /\
             pcfrel r w' (fst (prun lk apply fuel cf1))
                         (fst (prun lk apply fuel cf2)))))
    with (introduce _ ==> _ with lemma_prun_compat r lk apply fuel w cf1 cf2);
    introduce forall (b: pboundary v cl) (c1 c2: pcomp v cl).
        ((forall (w: pworld). pwf_world w ==> pcrel b.b_rel w c1 c2) ==>
         pnobs_tr_le b c1 c2)
    with (introduce _ ==> _ with lemma_pnobs_tr_le_of_crel b c1 c2)

(**
 * **AND THE TWO INSTANTIATIONS, IN ONE CHECKED STATEMENT.** PROVED: the
 * counterexample pair's consequent derived rather than written down, and the
 * theorem at `nboundary` -- at a producing program, and at two runs that answer
 * with two different handles under a world that is not the identity.
 *)
let guard_nom_b2b2_instances ()
  : Lemma (
      // 3: the counterexample instance, as a corollary
      (exists (x2: pval fv) (s2': pstore fv fcl) (w: pworld).
         pnconverges flook fapply ce_cf_r [] x2 s2' /\
         pwf_world w /\ pwext w (panchor ([] <: pstore fv fcl)) /\
         pval_rel w (PCtxKey 1) x2 /\ psrel fcl_rel w fce_sl s2') /\
      // 4: the theorem at the capturing boundary
      pnobs_tr_le nboundary nprog nprog /\
      pwf_world nw56 /\ pcfrel ncl_rel nw56 ncap_cf1 ncap_cf2 /\
      (fst (prun nboundary.b_lk nboundary.b_apply 2 ncap_cf1)).st == PDone (PCtxKey 5) /\
      (fst (prun nboundary.b_lk nboundary.b_apply 2 ncap_cf2)).st == PDone (PCtxKey 6) /\
      (PCtxKey #fv 5 =!= PCtxKey #fv 6))
  = guard_nom_ce_related_by_theorem ();
    guard_nom_fund_at_nboundary ();
    guard_nom_nboundary_capture_related ();
    guard_nom_nboundary_capture_answers ()

(* ================================================================== *)
(*  B2b.3: THE SIX PROPOSITIONS, ADVANCED SYMBOLICALLY                 *)
(*                                                                     *)
(*  The fundamental theorem (`lemma_prun_compat`) relates two runs      *)
(*  STARTED FROM RELATED CONFIGURATIONS.  A law's two sides are not     *)
(*  related as computations -- they are different nodes -- so proving   *)
(*  a law means advancing each side, by ITS OWN number of transitions,  *)
(*  to a configuration the theorem can be started from, and joining     *)
(*  the two prefixes to the theorem's suffix with `lemma_prun_split`.   *)
(*                                                                     *)
(*  That programme has three judgement points, and this section         *)
(*  settles the FIRST of them for all six propositions and reports on   *)
(*  the SECOND.  Nothing below relates the two sides' transition        *)
(*  counts: each prefix lemma names one side's own count and no         *)
(*  statement mentions both.                                           *)
(*                                                                     *)
(*  THE ALIGNMENT LAYER FIRST.  Every prefix below runs through the     *)
(*  three stack searches at frame lists built from a SYMBOLIC plan, so  *)
(*  the searches have to be discharged by induction on the plan rather  *)
(*  than by normalisation.  `plan_protocol_frames` is the only one of   *)
(*  the three projections these searches meet, and what they need of it *)
(*  is that it contains neither a floor nor a marker.                   *)
(* ================================================================== *)

(** **The residual projection carries no floor and no marker.** PROVED, by
    induction on the plan's items: `protocol_layer_frames` emits only `PSiteF`,
    `PParamF` and `PPromptF`, and `owner_frame` is a prompt. This is what makes
    `pfind_mode` walk THROUGH a plan's protocol segment and `pcut_scope` cut
    BENEATH it, at every plan, with no fixture involved. *)
let rec lemma_protocol_layer_frames_flat (#v #cl: Type) (ls: list (plan_item v cl))
  : Lemma (ensures pno_floor (protocol_layer_frames ls) /\
                   pno_mode (protocol_layer_frames ls))
          (decreases ls)
  = match ls with
    | [] -> ()
    | _ :: rest -> lemma_protocol_layer_frames_flat rest

let lemma_plan_protocol_frames_flat (#v #cl: Type) (pl: plan v cl)
  : Lemma (ensures pno_floor (plan_protocol_frames pl) /\
                   pno_mode (plan_protocol_frames pl))
  = lemma_protocol_layer_frames_flat (Plan?.layers pl);
    lemma_pno_floor_append (protocol_layer_frames (Plan?.layers pl))
                           [owner_frame (Plan?.owner pl)];
    lemma_pno_mode_append (protocol_layer_frames (Plan?.layers pl))
                          [owner_frame (Plan?.owner pl)]

(** **The nearest cut through a floor-free segment is that segment.** PROVED, by
    induction, and it is `lemma_find_mode_through`'s counterpart for the other
    search: production pushes `PScopeF` beneath the protocol segment, so this is
    what says the residual the yield stores is the segment and nothing else. *)
let rec lemma_pcut_scope_through (#v #cl: Type) (a: pstack v cl) (rest: pstack v cl)
  : Lemma (requires pno_floor a)
          (ensures pcut_scope (a @ (PScopeF :: rest)) == Some (a, rest))
          (decreases a)
  = match a with
    | [] -> ()
    | _ :: tl -> lemma_pcut_scope_through tl rest

(* ---- Composing a run out of named segments ------------------------ *)

(** One transition, as a run of one. PROVED. *)
let lemma_prun_one (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                   (cf cf': pconf v cl)
  : Lemma (requires PStep? cf.st /\ pstep_tr lk apply cf == (cf', ([] <: list string)))
          (ensures prun lk apply 1 cf == (cf', ([] <: list string)))
  = ()

(** Two silent segments compose into one. PROVED, from `lemma_prun_split`; the
    trace is `[] @ []`. This is the only composition used below, and it is what
    keeps each prefix's count local to its own side. *)
let lemma_prun_cat (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
                   (a b: nat) (cf cfa cfb: pconf v cl)
  : Lemma (requires prun lk apply a cf == (cfa, ([] <: list string)) /\
                    prun lk apply b cfa == (cfb, ([] <: list string)))
          (ensures prun lk apply (a + b) cf == (cfb, ([] <: list string)))
  = lemma_prun_split lk apply a b cf

(* ------------------------------------------------------------------ *)
(*  JUDGEMENT POINT 1: THE PREFIXES, IN GENERAL FORM                   *)
(*                                                                     *)
(*  Every lemma below runs the machine from a SYMBOLIC configuration:   *)
(*  the plan, the inner computation, the continuation, the ambient      *)
(*  stack, the store and the counter are all variables.  No lemma       *)
(*  mentions two sides' counts, and none is stated at a fixture.        *)
(* ------------------------------------------------------------------ *)

(** **Production's prefix, and it is TWO transitions at every plan.** PROVED.
    The bind installs the frame that will receive the handle, and `PEnterCtx`
    lays down boundary, protocol segment and floor above the ambient stack. The
    inner computation is UNTOUCHED and is what the machine goes on with, which is
    why this one lemma serves right identity, transparency and the anchored half
    of associativity alike -- the three whose left-hand side runs an arbitrary
    `c` inside the scope. *)
let lemma_prefix_produce (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (c: pcomp v cl) (f: pval v -> pcomp v cl)
    (k: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 2 ({ st = PStep (pbind (ref_ops.o_enter_ctx pl c) f) k;
                              store = sto; next = n0 })
           == ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                              @ (PScopeF :: PBindF f :: k)));
                 store = sto; next = n0 }, ([] <: list string)))
  = assert_norm (prun lk apply 2 ({ st = PStep (pbind (ref_ops.o_enter_ctx pl c) f) k;
                                    store = sto; next = n0 })
                 == ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                                    @ (PScopeF :: PBindF f :: k)));
                       store = sto; next = n0 }, ([] <: list string)))

(** **Entering's prefix, and it is ONE transition.** PROVED. The splice puts the
    plan's ENTER segment on the ambient stack and hands it the same `c`. *)
let lemma_prefix_enter (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (c: pcomp v cl) (k: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 1 ({ st = PStep (ref_ops.o_enter pl c) k;
                              store = sto; next = n0 })
           == ({ st = PStep c (plan_enter_frames pl @ k);
                 store = sto; next = n0 }, ([] <: list string)))
  = assert_norm (prun lk apply 1 ({ st = PStep (ref_ops.o_enter pl c) k;
                                    store = sto; next = n0 })
                 == ({ st = PStep c (plan_enter_frames pl @ k);
                       store = sto; next = n0 }, ([] <: list string)))

(** **The anchored half's right-hand side, and it is THREE transitions.** PROVED:
    the splice, then the two binds of `pbind (pbind c g) h`, which leave the same
    `c` under two recorded frames. *)
let lemma_prefix_enter_bind2 (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (c: pcomp v cl) (g h: pval v -> pcomp v cl)
    (k: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 3
             ({ st = PStep (PSplice (plan_enter_frames pl) (pbind (pbind c g) h)) k;
                store = sto; next = n0 })
           == ({ st = PStep c (PBindF g :: PBindF h :: (plan_enter_frames pl @ k));
                 store = sto; next = n0 }, ([] <: list string)))
  = assert_norm (prun lk apply 3
                   ({ st = PStep (PSplice (plan_enter_frames pl)
                                          (pbind (pbind c g) h)) k;
                      store = sto; next = n0 })
                 == ({ st = PStep c (PBindF g :: PBindF h
                                     :: (plan_enter_frames pl @ k));
                       store = sto; next = n0 }, ([] <: list string)))

(** **Resumption's right-hand side, and it is ONE transition.** PROVED. *)
let lemma_prefix_resume_rhs (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (c: pcomp v cl) (k: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 1 ({ st = PStep (PSplice (plan_resume_frames pl) c) k;
                              store = sto; next = n0 })
           == ({ st = PStep c (plan_resume_frames pl @ k);
                 store = sto; next = n0 }, ([] <: list string)))
  = assert_norm (prun lk apply 1
                   ({ st = PStep (PSplice (plan_resume_frames pl) c) k;
                      store = sto; next = n0 })
                 == ({ st = PStep c (plan_resume_frames pl @ k);
                       store = sto; next = n0 }, ([] <: list string)))

(* ---- The four transitions the symbolic prefixes need --------------- *)

(** The responder `ctx_drive` appends over a FRESHLY produced residual, as a
    NAMED function. `ctx_drive` builds its lambda internally, so the equality
    between it and the same lambda written at a use site is not something Z3 can
    see (the note at `lemma_ctx_drive_answers_head` records why); naming it once
    and normalising once is what keeps every statement below speaking of one SMT
    symbol. The `post` of a fresh residual is `PVar`, so the responder is just
    "hand the value to the consumer's function".

    It is `unfold` on purpose: the SMT encoding of a lambda occurring inside a
    definition is its own, so a NAMED symbol here would be a second lambda that
    Z3 cannot identify with the one `ctx_drive` builds. Unfolding at elaboration
    makes every occurrence below the SAME term, which is what
    `lemma_ctx_drive_answers_head` achieves with a local `let` and an
    `assert_norm`. *)
unfold
let presp0 (#v #cl: Type) (f: pval v -> pcomp v cl) : pval v -> pcomp v cl
  = fun z -> pbind (PVar z) f

let lemma_ctx_drive_fresh (#v #cl: Type) (m: weave_mode) (x: pval v)
                          (resid: pstack v cl) (f: pval v -> pcomp v cl)
  : Lemma (ctx_drive m (PCtxRequests x resid (PVar #v #cl)) f
           == PSplice (resid @ [PModeF m (presp0 f)]) (PVar x))
  = assert_norm (ctx_drive m (PCtxRequests x resid (PVar #v #cl)) f
                 == PSplice (resid @ [PModeF m (presp0 f)]) (PVar x))

let lemma_presp0_at (#v #cl: Type) (f: pval v -> pcomp v cl) (x: pval v)
  : Lemma (presp0 f x == POp (PVar x) f)
  = assert_norm (presp0 #v #cl f x == POp (PVar #v #cl x) f)

(** **The yield, at a symbolic protocol segment.** PROVED. The value meets the
    boundary, the mode search walks the whole segment and stops at the floor the
    same `PEnterCtx` pushed, the nearest cut is the segment itself, and the
    handle allocated is the counter the configuration came in with. Nothing here
    is about a particular plan: the two hypotheses are `lemma_plan_protocol_frames_flat`'s
    conclusion. *)
let lemma_step_yield_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (x: pval v) (a: pstack v cl) (below: pstack v cl) (cf: pconf v cl)
  : Lemma (requires pno_floor a /\ pno_mode a /\
                    cf.st == PStep (PVar x) (PBoundaryF :: (a @ (PScopeF :: below))))
          (ensures pstep_tr lk apply cf
                   == ({ cf with
                         st = PStep (PVar (PCtxKey cf.next)) below;
                         store = (cf.next, PCtxRequests x (PBoundaryF :: a)
                                                        (PVar #v #cl)) :: cf.store;
                         next = cf.next + 1 }, ([] <: list string)))
  = lemma_find_mode_through a (PScopeF :: below);
    lemma_pcut_scope_through a below

(** **The boundary that finds a consumer's marker.** PROVED, by
    `lemma_find_mode_marker`. *)
let lemma_step_boundary_marker (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (x: pval v) (a: pstack v cl) (m: weave_mode) (resp: pval v -> pcomp v cl)
    (rest: pstack v cl) (cf: pconf v cl)
  : Lemma (requires pno_floor a /\ pno_mode a /\
                    cf.st == PStep (PVar x) (PBoundaryF :: (a @ (PModeF m resp :: rest))))
          (ensures pstep_tr lk apply cf
                   == ({ cf with st = PStep (resp x) (a @ (PModeF m resp :: rest)) },
                       ([] <: list string)))
  = lemma_find_mode_marker a m resp rest

(** **The two consuming rules, with the resolution supplied.** PROVED. *)
let lemma_step_extendc_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (hv: pval v) (f: pval v -> pcomp v cl) (k: pstack v cl)
    (cf: pconf v cl) (cx: pctx v cl)
  : Lemma (requires cf.st == PStep (PExtendC pl hv f) k /\
                    presolve cf.store hv == Some cx)
          (ensures pstep_tr lk apply cf
                   == ({ cf with st = PStep (ctx_drive MExtend cx f) k },
                       ([] <: list string)))
  = ()

let lemma_step_resumec_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (hv: pval v) (f: pval v -> pcomp v cl) (k: pstack v cl)
    (cf: pconf v cl) (cx: pctx v cl)
  : Lemma (requires cf.st == PStep (PResumeC pl hv f) k /\
                    presolve cf.store hv == Some cx)
          (ensures pstep_tr lk apply cf
                   == ({ cf with st = PStep (ctx_drive MResume cx f) k },
                       ([] <: list string)))
  = ()

(**
 * **LEFT IDENTITY'S LEFT-HAND SIDE, ADVANCED SYMBOLICALLY.** PROVED, at an
 * ARBITRARY plan, value, extension function, ambient stack, store and counter.
 *
 * Nine transitions, and every one of them is named: the bind, the production
 * node, the yield at the boundary (which is where the handle is allocated and
 * the residual stored), the frame that receives the handle, `bindScope`'s
 * resolution, the splice that puts the residual back with the consumer's marker
 * beneath it, the boundary that finds THAT marker, and the two that hand the
 * value to `g`.
 *
 * The count is this side's own. Nothing in this statement mentions the other
 * side, and nothing below relates it to the other side's count: the two are
 * joined only through `lemma_prun_split`, which composes a prefix with a suffix
 * on ONE side.
 *)
let lemma_prefix_li_l (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (x: pval v) (g: pval v -> pcomp v cl)
    (k: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 9
             ({ st = PStep (pbind (ref_ops.o_enter_ctx pl (PVar x))
                                  (fun cx -> ref_ops.o_extend pl cx g)) k;
                store = sto; next = n0 })
           == ({ st = PStep (g x)
                            (plan_protocol_frames pl
                             @ (PModeF MExtend (presp0 g) :: k));
                 store = (n0, PCtxRequests x (PBoundaryF :: plan_protocol_frames pl)
                                           (PVar #v #cl)) :: sto;
                 next = n0 + 1 },
               ([] <: list string)))
  = let ppf : pstack v cl = plan_protocol_frames pl in
    let f : pval v -> pcomp v cl = fun cx -> ref_ops.o_extend pl cx g in
    let resid : pstack v cl = PBoundaryF :: ppf in
    let cxr : pctx v cl = PCtxRequests x resid (PVar #v #cl) in
    let st1 : pstore v cl = (n0, cxr) :: sto in
    let mfr : pframe v cl = PModeF MExtend (presp0 g) in
    let cf0 : pconf v cl =
      { st = PStep (pbind (ref_ops.o_enter_ctx pl (PVar x)) f) k;
        store = sto; next = n0 } in
    let cfa : pconf v cl =
      { st = PStep (PVar x) (PBoundaryF :: (ppf @ (PScopeF :: PBindF f :: k)));
        store = sto; next = n0 } in
    let cfb : pconf v cl =
      { st = PStep (PVar (PCtxKey n0)) (PBindF f :: k); store = st1; next = n0 + 1 } in
    let cfc : pconf v cl =
      { st = PStep (PExtendC pl (PCtxKey n0) g) k; store = st1; next = n0 + 1 } in
    let cfd : pconf v cl =
      { st = PStep (PSplice (resid @ [mfr]) (PVar x)) k; store = st1; next = n0 + 1 } in
    let cfe : pconf v cl =
      { st = PStep (PVar x) (PBoundaryF :: (ppf @ (mfr :: k)));
        store = st1; next = n0 + 1 } in
    let cff : pconf v cl =
      { st = PStep (POp (PVar x) g) (ppf @ (mfr :: k)); store = st1; next = n0 + 1 } in
    let cfg : pconf v cl =
      { st = PStep (PVar x) (PBindF g :: (ppf @ (mfr :: k)));
        store = st1; next = n0 + 1 } in
    let cfh : pconf v cl =
      { st = PStep (g x) (ppf @ (mfr :: k)); store = st1; next = n0 + 1 } in
    lemma_plan_protocol_frames_flat pl;
    // 1-2: the bind and the production node
    lemma_prefix_produce lk apply pl (PVar x) f k sto n0;
    // 3: the yield -- allocates the handle and stores the residual
    lemma_step_yield_at lk apply x ppf (PBindF f :: k) cfa;
    lemma_prun_one lk apply cfa cfb;
    lemma_prun_cat lk apply 2 1 cf0 cfa cfb;
    // 4: the frame that receives the handle
    lemma_prun_one lk apply cfb cfc;
    lemma_prun_cat lk apply 3 1 cf0 cfb cfc;
    // 5: `bindScope`'s resolution, and the drive it delegates to
    assert (presolve st1 (PCtxKey n0) == Some cxr);
    lemma_step_extendc_at lk apply pl (PCtxKey n0) g k cfc cxr;
    lemma_ctx_drive_fresh MExtend x resid g;
    lemma_prun_one lk apply cfc cfd;
    lemma_prun_cat lk apply 4 1 cf0 cfc cfd;
    // 6: the splice -- the residual goes back with the marker beneath it
    append_assoc resid [mfr] k;
    lemma_prun_one lk apply cfd cfe;
    lemma_prun_cat lk apply 5 1 cf0 cfd cfe;
    // 7: the boundary finds THIS consumer's marker
    lemma_step_boundary_marker lk apply x ppf MExtend (presp0 g) k cfe;
    lemma_presp0_at g x;
    lemma_prun_one lk apply cfe cff;
    lemma_prun_cat lk apply 6 1 cf0 cfe cff;
    // 8-9: and the value reaches `g`
    lemma_prun_one lk apply cff cfg;
    lemma_prun_cat lk apply 7 1 cf0 cff cfg;
    lemma_prun_one lk apply cfg cfh;
    lemma_prun_cat lk apply 8 1 cf0 cfg cfh

(**
 * **RESUMPTION'S LEFT-HAND SIDE, ADVANCED SYMBOLICALLY.** PROVED, at an
 * arbitrary plan, value, continuation, ambient stack, store and counter.
 *
 * The same nine transitions as left identity's, with `MResume` in place of
 * `MExtend` -- which is the entire difference between the two consumers, and it
 * is visible here as one constructor and nothing else.
 *)
let lemma_prefix_rm_l (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (x: pval v) (kk: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (prun lk apply 9
             ({ st = PStep (pbind (ref_ops.o_enter_ctx pl (PVar x))
                                  (fun cx -> ref_ops.o_resume pl cx kk)) amb;
                store = sto; next = n0 })
           == ({ st = PStep (kk x)
                            (plan_protocol_frames pl
                             @ (PModeF MResume (presp0 kk) :: amb));
                 store = (n0, PCtxRequests x (PBoundaryF :: plan_protocol_frames pl)
                                           (PVar #v #cl)) :: sto;
                 next = n0 + 1 },
               ([] <: list string)))
  = let ppf : pstack v cl = plan_protocol_frames pl in
    let f : pval v -> pcomp v cl = fun cx -> ref_ops.o_resume pl cx kk in
    let resid : pstack v cl = PBoundaryF :: ppf in
    let cxr : pctx v cl = PCtxRequests x resid (PVar #v #cl) in
    let st1 : pstore v cl = (n0, cxr) :: sto in
    let mfr : pframe v cl = PModeF MResume (presp0 kk) in
    let cf0 : pconf v cl =
      { st = PStep (pbind (ref_ops.o_enter_ctx pl (PVar x)) f) amb;
        store = sto; next = n0 } in
    let cfa : pconf v cl =
      { st = PStep (PVar x) (PBoundaryF :: (ppf @ (PScopeF :: PBindF f :: amb)));
        store = sto; next = n0 } in
    let cfb : pconf v cl =
      { st = PStep (PVar (PCtxKey n0)) (PBindF f :: amb); store = st1; next = n0 + 1 } in
    let cfc : pconf v cl =
      { st = PStep (PResumeC pl (PCtxKey n0) kk) amb; store = st1; next = n0 + 1 } in
    let cfd : pconf v cl =
      { st = PStep (PSplice (resid @ [mfr]) (PVar x)) amb; store = st1; next = n0 + 1 } in
    let cfe : pconf v cl =
      { st = PStep (PVar x) (PBoundaryF :: (ppf @ (mfr :: amb)));
        store = st1; next = n0 + 1 } in
    let cff : pconf v cl =
      { st = PStep (POp (PVar x) kk) (ppf @ (mfr :: amb)); store = st1; next = n0 + 1 } in
    let cfg : pconf v cl =
      { st = PStep (PVar x) (PBindF kk :: (ppf @ (mfr :: amb)));
        store = st1; next = n0 + 1 } in
    let cfh : pconf v cl =
      { st = PStep (kk x) (ppf @ (mfr :: amb)); store = st1; next = n0 + 1 } in
    lemma_plan_protocol_frames_flat pl;
    lemma_prefix_produce lk apply pl (PVar x) f amb sto n0;
    lemma_step_yield_at lk apply x ppf (PBindF f :: amb) cfa;
    lemma_prun_one lk apply cfa cfb;
    lemma_prun_cat lk apply 2 1 cf0 cfa cfb;
    lemma_prun_one lk apply cfb cfc;
    lemma_prun_cat lk apply 3 1 cf0 cfb cfc;
    assert (presolve st1 (PCtxKey n0) == Some cxr);
    lemma_step_resumec_at lk apply pl (PCtxKey n0) kk amb cfc cxr;
    lemma_ctx_drive_fresh MResume x resid kk;
    lemma_prun_one lk apply cfc cfd;
    lemma_prun_cat lk apply 4 1 cf0 cfc cfd;
    append_assoc resid [mfr] amb;
    lemma_prun_one lk apply cfd cfe;
    lemma_prun_cat lk apply 5 1 cf0 cfd cfe;
    lemma_step_boundary_marker lk apply x ppf MResume (presp0 kk) amb cfe;
    lemma_presp0_at kk x;
    lemma_prun_one lk apply cfe cff;
    lemma_prun_cat lk apply 6 1 cf0 cfe cff;
    lemma_prun_one lk apply cff cfg;
    lemma_prun_cat lk apply 7 1 cf0 cff cfg;
    lemma_prun_one lk apply cfg cfh;
    lemma_prun_cat lk apply 8 1 cf0 cfg cfh

(* ---- The algebraic half's two prefixes ---------------------------- *)

(** `bindScope`, with the resolution supplied. PROVED. It ALLOCATES -- condition
    8 -- so the configuration it hands on carries one entry and one counter more
    than the one it received. *)
let lemma_step_extendctxc_at (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (hv: pval v) (f: pval v -> pcomp v cl) (amb: pstack v cl)
    (cf: pconf v cl) (cx: pctx v cl)
  : Lemma (requires cf.st == PStep (PExtendCtxC pl hv f) amb /\
                    presolve cf.store hv == Some cx)
          (ensures pstep_tr lk apply cf
                   == ({ cf with
                         st = PStep (PVar (PCtxKey cf.next)) amb;
                         store = (cf.next, extend_ctx_C pl cx f) :: cf.store;
                         next = cf.next + 1 }, ([] <: list string)))
  = ()

(** A handle that does not resolve. PROVED, and both consuming rules answer with
    the SAME stuck state -- which is why the algebraic half's two sides reach a
    common configuration when the context they name is absent. *)
let lemma_step_consume_stuck (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (hv: pval v) (f: pval v -> pcomp v cl) (amb: pstack v cl)
    (cf: pconf v cl)
  : Lemma (requires presolve cf.store hv == None)
          (ensures
            (cf.st == PStep (PExtendC pl hv f) amb ==>
             pstep_tr lk apply cf
               == ({ cf with st = PStuck pctx_eff pctx_missing_op },
                   ([] <: list string))) /\
            (cf.st == PStep (PExtendCtxC pl hv f) amb ==>
             pstep_tr lk apply cf
               == ({ cf with st = PStuck pctx_eff pctx_missing_op },
                   ([] <: list string))))
  = ()

(**
 * **THE ALGEBRAIC HALF'S LEFT-HAND SIDE, ADVANCED SYMBOLICALLY.** PROVED, at an
 * arbitrary plan, handle, pair of extension functions, ambient stack, store and
 * counter, WHEN THE HANDLE RESOLVES.
 *
 * Four transitions: the bind, `bindScope` (which allocates the extended
 * context), the frame that receives the new handle, and `runScope`'s resolution
 * of it. The result is a drive of the EXTENDED context by `h`.
 *)
let lemma_prefix_aa_l (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat) (cxv: pctx v cl)
  : Lemma (requires presolve sto cxh == Some cxv)
          (ensures
            prun lk apply 4
              ({ st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g)
                                   (fun cy -> ref_ops.o_extend pl cy h)) amb;
                 store = sto; next = n0 })
            == ({ st = PStep (ctx_drive MExtend (extend_ctx_C pl cxv g) h) amb;
                  store = (n0, extend_ctx_C pl cxv g) :: sto;
                  next = n0 + 1 }, ([] <: list string)))
  = let f : pval v -> pcomp v cl = fun cy -> ref_ops.o_extend pl cy h in
    let cy0 : pctx v cl = extend_ctx_C pl cxv g in
    let st1 : pstore v cl = (n0, cy0) :: sto in
    let cf0 : pconf v cl =
      { st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g) f) amb;
        store = sto; next = n0 } in
    let cfa : pconf v cl =
      { st = PStep (PExtendCtxC pl cxh g) (PBindF f :: amb); store = sto; next = n0 } in
    let cfb : pconf v cl =
      { st = PStep (PVar (PCtxKey n0)) (PBindF f :: amb); store = st1; next = n0 + 1 } in
    let cfc : pconf v cl =
      { st = PStep (PExtendC pl (PCtxKey n0) h) amb; store = st1; next = n0 + 1 } in
    let cfd : pconf v cl =
      { st = PStep (ctx_drive MExtend cy0 h) amb; store = st1; next = n0 + 1 } in
    lemma_prun_one lk apply cf0 cfa;
    lemma_step_extendctxc_at lk apply pl cxh g (PBindF f :: amb) cfa cxv;
    lemma_prun_one lk apply cfa cfb;
    lemma_prun_cat lk apply 1 1 cf0 cfa cfb;
    lemma_prun_one lk apply cfb cfc;
    lemma_prun_cat lk apply 2 1 cf0 cfb cfc;
    assert (presolve st1 (PCtxKey n0) == Some cy0);
    lemma_step_extendc_at lk apply pl (PCtxKey n0) h amb cfc cy0;
    lemma_prun_one lk apply cfc cfd;
    lemma_prun_cat lk apply 3 1 cf0 cfc cfd

(** **The algebraic half's right-hand side, and it is ONE transition.** PROVED,
    under the same resolution: the composite extension drives the ORIGINAL
    context. Neither this side's count nor the other's appears in any statement
    that mentions both. *)
let lemma_prefix_aa_r (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat) (cxv: pctx v cl)
  : Lemma (requires presolve sto cxh == Some cxv)
          (ensures
            prun lk apply 1
              ({ st = PStep (ref_ops.o_extend pl cxh (fun z -> pbind (g z) h)) amb;
                 store = sto; next = n0 })
            == ({ st = PStep (ctx_drive MExtend cxv (fun z -> pbind (g z) h)) amb;
                  store = sto; next = n0 }, ([] <: list string)))
  = let f : pval v -> pcomp v cl = fun z -> pbind (g z) h in
    let cf0 : pconf v cl =
      { st = PStep (ref_ops.o_extend pl cxh f) amb; store = sto; next = n0 } in
    let cfa : pconf v cl =
      { st = PStep (ctx_drive MExtend cxv f) amb; store = sto; next = n0 } in
    lemma_step_extendc_at lk apply pl cxh f amb cf0 cxv;
    lemma_prun_one lk apply cf0 cfa

(** **And when the handle does not resolve, the two sides reach the SAME
    configuration.** PROVED -- two transitions on the left, one on the right, and
    the stuck state, the store and the counter all agree. *)
let lemma_prefix_aa_stuck_l (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (requires presolve sto cxh == None)
          (ensures
            prun lk apply 2
              ({ st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g)
                                   (fun cy -> ref_ops.o_extend pl cy h)) amb;
                 store = sto; next = n0 })
            == ({ st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 },
                ([] <: list string)))
  = let f : pval v -> pcomp v cl = fun cy -> ref_ops.o_extend pl cy h in
    let cf0 : pconf v cl =
      { st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g) f) amb;
        store = sto; next = n0 } in
    let cfa : pconf v cl =
      { st = PStep (PExtendCtxC pl cxh g) (PBindF f :: amb); store = sto; next = n0 } in
    let cfb : pconf v cl =
      { st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 } in
    lemma_prun_one lk apply cf0 cfa;
    lemma_step_consume_stuck lk apply pl cxh g (PBindF f :: amb) cfa;
    lemma_prun_one lk apply cfa cfb;
    lemma_prun_cat lk apply 1 1 cf0 cfa cfb

let lemma_prefix_aa_stuck_r (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (requires presolve sto cxh == None)
          (ensures
            prun lk apply 1
              ({ st = PStep (ref_ops.o_extend pl cxh (fun z -> pbind (g z) h)) amb;
                 store = sto; next = n0 })
            == ({ st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 },
                ([] <: list string)))
  = let f : pval v -> pcomp v cl = fun z -> pbind (g z) h in
    let cf0 : pconf v cl =
      { st = PStep (ref_ops.o_extend pl cxh f) amb; store = sto; next = n0 } in
    lemma_step_consume_stuck lk apply pl cxh f amb cf0;
    lemma_prun_one lk apply cf0 ({ st = PStuck pctx_eff pctx_missing_op;
                                   store = sto; next = n0 })

(* ================================================================== *)
(*  JUDGEMENT POINT 2: THE POST-PREFIX CONFIGURATIONS                  *)
(*                                                                     *)
(*  The prefixes above are the whole of judgement point 1, and they     *)
(*  answer it: every one of the six propositions has a FINITE prefix    *)
(*  on each side, computable with the plan, the inner computation, the  *)
(*  ambient stack, the store and the counter left as variables, and     *)
(*  the two prefixes land on the SAME node -- `c`, `g x`, `kk x`, or a  *)
(*  drive of the same context.                                         *)
(*                                                                     *)
(*  Judgement point 2 asks whether the fundamental theorem can be       *)
(*  STARTED there, and it CANNOT, for a reason that is structural and   *)
(*  has nothing to do with names.  `pframes_rel` matches a stack        *)
(*  cons-for-cons; the two post-prefix stacks have DIFFERENT LENGTHS,   *)
(*  at EVERY plan and EVERY ambient stack, because                      *)
(*                                                                     *)
(*    - the left side is inside the scope's protocol segment and the    *)
(*      right side is inside the plan's ENTER (or RESUME) segment, and  *)
(*      `protocol_layer_frames` keeps a `PSiteF` exactly where          *)
(*      `enter_layer_frames` drops the item; and                        *)
(*    - the left side carries the frames the residual protocol needs    *)
(*      -- a boundary and a floor before production, a `PModeF` marker  *)
(*      after consumption -- and the right side carries none of them.   *)
(*                                                                     *)
(*  The four lemmas below prove exactly that, unconditionally in the    *)
(*  plan.  They are the localisation of the failure: it is NOT the      *)
(*  nominal relation, which never looks at a stack's length, and it is  *)
(*  NOT the prefixes, which are exact.  It is that the laws equate two  *)
(*  computations whose machine configurations differ by frames, and     *)
(*  the logical relation this module carries is a CONGRUENCE, not a     *)
(*  bisimulation.                                                       *)
(* ================================================================== *)

(** **Related stacks have the same length.** PROVED, by induction; one index is
    enough, since `pframes_rel` is `False` on a length mismatch from index 1 up. *)
let rec lemma_pframes_rel_length (#v #cl: Type) (r: pcl_rel_t cl) (n: nat) (w: pworld)
    (a b: pstack v cl)
  : Lemma (requires n >= 1 /\ pframes_rel r n w a b)
          (ensures length a == length b)
          (decreases a)
  = match a, b with
    | [], [] -> ()
    | _ :: t1, _ :: t2 -> lemma_pframes_rel_length r n w t1 t2
    | _, _ -> ()

let lemma_pkrel_length (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (a b: pstack v cl)
  : Lemma (requires pkrel r w a b) (ensures length a == length b)
  = lemma_pframes_rel_length r 1 w a b

(** **The three projections, measured.** PROVED, by induction on the plan's
    items. The residual projection is the longest: it keeps a frame for every
    item, where entering drops the `PIBind`s. Resumption keeps one for every item
    too, so it has the residual's length exactly -- which is why the marker, and
    not the segment, is what separates the two sides of the resumption law. *)
let rec lemma_layer_frames_lengths (#v #cl: Type) (ls: list (plan_item v cl))
  : Lemma (ensures length (enter_layer_frames ls) <= length (protocol_layer_frames ls) /\
                   length (resume_layer_frames ls) == length (protocol_layer_frames ls))
          (decreases ls)
  = match ls with
    | [] -> ()
    | _ :: rest -> lemma_layer_frames_lengths rest

let lemma_plan_frames_lengths (#v #cl: Type) (pl: plan v cl)
  : Lemma (length (plan_enter_frames pl) <= length (plan_protocol_frames pl) /\
           length (plan_resume_frames pl) == length (plan_protocol_frames pl))
  = lemma_layer_frames_lengths (Plan?.layers pl);
    append_length (enter_layer_frames (Plan?.layers pl)) [owner_frame (Plan?.owner pl)];
    append_length (resume_layer_frames (Plan?.layers pl)) [owner_frame (Plan?.owner pl)];
    append_length (protocol_layer_frames (Plan?.layers pl)) [owner_frame (Plan?.owner pl)]

(**
 * **PRODUCTION'S STACK IS NEVER ENTERING'S.** PROVED, at every plan, every
 * continuation and every ambient stack, and at every world.
 *
 * This is the obstruction for RIGHT IDENTITY and for TRANSPARENCY, whose two
 * sides reach the very same inner computation `c` -- the prefixes are exact --
 * under stacks that differ by the boundary, the floor, the frame that will
 * receive the handle, and whatever `PSiteF`s the plan's `PIBind`s contribute.
 * Three frames at the very least, and never fewer.
 *)
let guard_align_produce_vs_enter (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (f: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (~(pkrel r w (PBoundaryF :: (plan_protocol_frames pl
                                       @ (PScopeF :: PBindF f :: amb)))
                       (plan_enter_frames pl @ amb)))
  = lemma_plan_frames_lengths pl;
    append_length (plan_protocol_frames pl)
                  ((PScopeF :: PBindF f :: amb) <: pstack v cl);
    append_length (plan_enter_frames pl) amb;
    introduce pkrel r w (PBoundaryF :: (plan_protocol_frames pl
                                        @ (PScopeF :: PBindF f :: amb)))
                        (plan_enter_frames pl @ amb) ==> False
    with
      lemma_pkrel_length r w (PBoundaryF :: (plan_protocol_frames pl
                                             @ (PScopeF :: PBindF f :: amb)))
                             (plan_enter_frames pl @ amb)

(**
 * **AND IT IS NOT ENTERING WITH THE TWO BINDS EITHER.** PROVED. This is the
 * obstruction for the ANCHORED HALF of associativity, whose right-hand side
 * reaches `c` under the enter segment with `PBindF g` and `PBindF h` above it.
 * The left side is still one frame longer, and would be at every plan even if
 * the two segments agreed.
 *)
let guard_align_produce_vs_enter_bind2 (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (f g h: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (~(pkrel r w (PBoundaryF :: (plan_protocol_frames pl
                                       @ (PScopeF :: PBindF f :: amb)))
                       (PBindF g :: PBindF h :: (plan_enter_frames pl @ amb))))
  = lemma_plan_frames_lengths pl;
    append_length (plan_protocol_frames pl)
                  ((PScopeF :: PBindF f :: amb) <: pstack v cl);
    append_length (plan_enter_frames pl) amb;
    introduce pkrel r w (PBoundaryF :: (plan_protocol_frames pl
                                        @ (PScopeF :: PBindF f :: amb)))
                        (PBindF g :: PBindF h :: (plan_enter_frames pl @ amb)) ==> False
    with
      lemma_pkrel_length r w (PBoundaryF :: (plan_protocol_frames pl
                                             @ (PScopeF :: PBindF f :: amb)))
                             (PBindF g :: PBindF h :: (plan_enter_frames pl @ amb))

(**
 * **THE CONSUMER'S MARKER IS NOT NOTHING.** PROVED. This is the obstruction for
 * LEFT IDENTITY: both sides reach `g x`, the left inside the residual's protocol
 * segment with the extension's `MExtend` marker beneath it, the right inside the
 * plan's enter segment with nothing beneath it but the ambient stack. The marker
 * alone already separates them, and the `PSiteF`s separate them further.
 *)
let guard_align_marker_vs_enter (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (m: weave_mode) (resp: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (~(pkrel r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                       (plan_enter_frames pl @ amb)))
  = lemma_plan_frames_lengths pl;
    append_length (plan_protocol_frames pl) ((PModeF m resp :: amb) <: pstack v cl);
    append_length (plan_enter_frames pl) amb;
    introduce pkrel r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                        (plan_enter_frames pl @ amb) ==> False
    with
      lemma_pkrel_length r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                             (plan_enter_frames pl @ amb)

(**
 * **AND IT IS NOT NOTHING AT THE RESUME PROJECTION EITHER.** PROVED, and this
 * one is the sharpest of the four: `plan_resume_frames` and
 * `plan_protocol_frames` have the SAME LENGTH, so the two sides of the
 * resumption law differ by the marker and by NOTHING ELSE. The anchoring is not
 * what fails -- the segment on the left is the segment on the right, frame for
 * frame in length -- it is that a consumed residual carries the consumer's
 * marker and an independent description of resumption has nowhere to put one.
 *)
let guard_align_marker_vs_resume (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (m: weave_mode) (resp: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (~(pkrel r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                       (plan_resume_frames pl @ amb)))
  = lemma_plan_frames_lengths pl;
    append_length (plan_protocol_frames pl) ((PModeF m resp :: amb) <: pstack v cl);
    append_length (plan_resume_frames pl) amb;
    introduce pkrel r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                        (plan_resume_frames pl @ amb) ==> False
    with
      lemma_pkrel_length r w (plan_protocol_frames pl @ (PModeF m resp :: amb))
                             (plan_resume_frames pl @ amb)

(* ---- The algebraic half's obstruction, which is a DIFFERENT one ---- *)

(**
 * **Composing an extension onto a context's `post`**, named once so that the
 * two bracketings below are two applications of ONE symbol. `unfold` for the
 * reason `presp0` is.
 *)
unfold
let pcompose (#v #cl: Type) (p f: pval v -> pcomp v cl) : pval v -> pcomp v cl
  = fun u -> pbind (p u) f

let lemma_extend_ctx_C_compose (#v #cl: Type) (pl: plan v cl) (z: pval v)
                               (resid: pstack v cl) (post f: pval v -> pcomp v cl)
  : Lemma (extend_ctx_C pl (PCtxRequests z resid post) f
           == PCtxRequests z resid (pcompose post f))
  = assert_norm (extend_ctx_C pl (PCtxRequests z resid post) f
                 == PCtxRequests z resid (pcompose post f))

let lemma_ctx_drive_requests (#v #cl: Type) (m: weave_mode) (z: pval v)
                             (resid: pstack v cl) (post f: pval v -> pcomp v cl)
  : Lemma (ctx_drive m (PCtxRequests z resid post) f
           == PSplice (resid @ [PModeF m (pcompose post f)]) (PVar z))
  = assert_norm (ctx_drive m (PCtxRequests z resid post) f
                 == PSplice (resid @ [PModeF m (pcompose post f)]) (PVar z))

(** The last frame of two stacks with a common prefix. PROVED, by induction. *)
let rec lemma_pkrel_snoc_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (a: pstack v cl) (x y: pframe v cl)
  : Lemma (requires pkrel r w (a @ [x]) (a @ [y]))
          (ensures pfrel r w x y)
          (decreases a)
  = match a with
    | [] -> lemma_pkrel_cons_inv r w x y ([] <: pstack v cl) ([] <: pstack v cl)
    | e :: rest ->
      lemma_pkrel_cons_inv r w e e (rest @ [x]) (rest @ [y]);
      lemma_pkrel_snoc_inv r w rest x y

(**
 * **A COMPUTATION IS NEVER RELATED TO A BIND OF ITSELF.** PROVED, by structural
 * induction on the computation.
 *
 * `POp a f` related to `a` would need `a` to be a `POp` whose first component is
 * related to a `POp` whose first component is ..., without end -- and a term is
 * finite. The step index does the counting: the relation at index `n + 1`
 * hands down the relation at `n` one constructor in.
 *)
let rec lemma_no_op_self (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (a: pcomp v cl) (f: pval v -> pcomp v cl)
  : Lemma (ensures ~(pcrel r w (POp a f) a)) (decreases a)
  = match a with
    | POp a' f' ->
      lemma_no_op_self r w a' f';
      introduce pcrel r w (POp a f) a ==> False
      with lemma_pcrel_op_inv r w a a' f f'
    | _ ->
      introduce pcrel r w (POp a f) a ==> False
      with assert (pcomp_rel r 1 w (POp a f) a)

(**
 * **THE ALGEBRAIC HALF'S TWO SIDES CARRY THE TWO BRACKETINGS, AND THOSE ARE NOT
 * RELATED.** PROVED, at every plan, every stored residual, every `post`, every
 * `g` and `h`, and every world with a value related to itself in it.
 *
 * This is a DIFFERENT obstruction from the other four and it is worth keeping
 * apart. Here the two post-prefix stacks are LITERALLY THE SAME -- the ambient
 * stack, untouched -- and the two computations are drives of the same residual.
 * What differs is the responder the marker carries: extending by `g` and then by
 * `h` records `fun u -> (post u >>= g) >>= h`, extending by the composite records
 * `fun u -> post u >>= (fun x -> g x >>= h)`, and those are the two bracketings
 * of one chain. They are equal computations of the machine and are NOT related
 * terms: `pcomp_rel` matches `POp` against `POp` and then asks for the FIRST
 * COMPONENTS to be related, which here is `post u >>= g` against `post u`.
 *
 * So the algebraic half's failure is not the residual protocol at all. It is
 * that the relation is a congruence and the law is an equation of the inner
 * monad.
 *)
let guard_align_bracketing (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (z: pval v) (resid: pstack v cl)
    (post g h: pval v -> pcomp v cl) (y: pval v)
  : Lemma (requires pwf_world w /\ pval_rel w y y)
          (ensures
            ~(pcrel r w
                (ctx_drive MExtend
                   (extend_ctx_C pl (PCtxRequests z resid post) g) h)
                (ctx_drive MExtend (PCtxRequests z resid post) (pcompose g h))))
  = lemma_extend_ctx_C_compose pl z resid post g;
    lemma_ctx_drive_requests MExtend z resid (pcompose post g) h;
    lemma_ctx_drive_requests MExtend z resid post (pcompose g h);
    lemma_no_op_self r w (post y) g;
    lemma_pwext_refl w;
    introduce pcrel r w
                (ctx_drive MExtend (extend_ctx_C pl (PCtxRequests z resid post) g) h)
                (ctx_drive MExtend (PCtxRequests z resid post) (pcompose g h)) ==> False
    with begin
      lemma_pcrel_splice_inv r w
        (resid @ [PModeF MExtend (pcompose (pcompose post g) h)])
        (resid @ [PModeF MExtend (pcompose post (pcompose g h))])
        (PVar z) (PVar z);
      lemma_pkrel_snoc_inv r w resid
        (PModeF MExtend (pcompose (pcompose post g) h))
        (PModeF MExtend (pcompose post (pcompose g h)));
      lemma_pfrel_mode_inv r w MExtend MExtend
        (pcompose (pcompose post g) h) (pcompose post (pcompose g h));
      assert (pcrel r w (POp (POp (post y) g) h) (POp (post y) (pcompose g h)));
      lemma_pcrel_op_inv r w (POp (post y) g) (post y) h (pcompose g h)
    end

(* ================================================================== *)
(*  JUDGEMENT POINT 3, WHERE IT IS REACHED: JOINING TWO PREFIXES TO    *)
(*  THE FUNDAMENTAL THEOREM                                            *)
(*                                                                     *)
(*  The four obstructions above say the two sides do NOT reach related *)
(*  configurations in general.  Where they DO -- and the algebraic     *)
(*  half of associativity does, at every configuration whose named     *)
(*  handle is absent or holds no requests -- the composition below is  *)
(*  what closes the obligation, and it never re-anchors: the world it  *)
(*  hands back is the theorem's, which is `panchor sto` plus one pair  *)
(*  per allocation.                                                    *)
(*                                                                     *)
(*  THE TWO PREFIX LENGTHS ARE INDEPENDENT PARAMETERS.  `a1` and `a2`  *)
(*  are quantified separately, nothing relates them, and the theorem   *)
(*  is applied at ONE fuel to the COMMON configuration -- so no        *)
(*  transition offset can appear.                                       *)
(* ================================================================== *)

(** A resolved context is self-related at the store's own anchor. PROVED, from
    `pstore_equivariant_at` and nothing else; the handle must be a `PCtxKey`,
    since `presolve` answers `None` on a payload. *)
let lemma_presolve_selfrel (#v #cl: Type) (r: pcl_rel_t cl) (sto: pstore v cl)
    (hv: pval v) (cx: pctx v cl)
  : Lemma (requires pstore_equivariant_at r sto /\ presolve sto hv == Some cx)
          (ensures pxrel r (panchor sto) cx cx)
  = lemma_panchor_wf sto;
    lemma_pwext_refl (panchor sto);
    match hv with
    | PCtxKey id -> assert (pstore_lookup id sto == Some cx)
    | PV _ -> ()

(**
 * **TWO PREFIXES AND THE THEOREM, COMPOSED.** PROVED.
 *
 * Each side is advanced by ITS OWN number of silent transitions to a
 * configuration; the two configurations are related at the store's anchor; and
 * the conclusion is the nominal observation's consequent at THAT ambient stack,
 * store and counter. `lemma_prun_stable` is what lets the left run's own fuel be
 * pushed past its prefix, `lemma_prun_split` is what decomposes both runs, and
 * `lemma_prun_compat` is applied ONCE, at ONE fuel, to the common pair.
 *)
let lemma_obs_from_common (#v #cl: Type) (b: pboundary v cl)
    (c1 c2: pcomp v cl) (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
    (a1 a2: nat) (d1 d2: pconf v cl)
    (tr: list string) (x1: pval v) (s1': pstore v cl)
  : Lemma (requires
             (let cf1 : pconf v cl = { st = PStep c1 amb; store = sto; next = n0 } in
              let cf2 : pconf v cl = { st = PStep c2 amb; store = sto; next = n0 } in
              prun b.b_lk b.b_apply a1 cf1 == (d1, ([] <: list string)) /\
              prun b.b_lk b.b_apply a2 cf2 == (d2, ([] <: list string)) /\
              pcfrel b.b_rel (panchor sto) d1 d2 /\
              pnconverges b.b_lk b.b_apply cf1 tr x1 s1'))
          (ensures
             (let cf2 : pconf v cl = { st = PStep c2 amb; store = sto; next = n0 } in
              exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                pnconverges b.b_lk b.b_apply cf2 tr x2 s2' /\
                pwf_world w /\ pwext w (panchor sto) /\
                pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = let _ : squash (pcl_mono b.b_rel) = b.b_mono in
    let _ : squash (pcl_down b.b_rel) = b.b_down in
    let _ : squash (plookup_equivariant b.b_rel b.b_lk) = b.b_lookup in
    let _ : squash (papply_equivariant b.b_rel b.b_apply) = b.b_apply_eq in
    let w0 = panchor sto in
    let cf1 : pconf v cl = { st = PStep c1 amb; store = sto; next = n0 } in
    let cf2 : pconf v cl = { st = PStep c2 amb; store = sto; next = n0 } in
    lemma_panchor_wf sto;
    lemma_pwext_refl w0;
    pnconverges_unfold b.b_lk b.b_apply cf1 tr x1 s1' ();
    eliminate exists (n: nat).
        ((fst (prun b.b_lk b.b_apply n cf1)).st == PDone x1 /\
         snd (prun b.b_lk b.b_apply n cf1) == tr /\
         (fst (prun b.b_lk b.b_apply n cf1)).store == s1')
    with begin
      lemma_prun_stable b.b_lk b.b_apply n a1 cf1;
      lemma_prun_split b.b_lk b.b_apply a1 n cf1;
      assert ((fst (prun b.b_lk b.b_apply n d1)).st == PDone x1);
      assert (snd (prun b.b_lk b.b_apply n d1) == tr);
      assert ((fst (prun b.b_lk b.b_apply n d1)).store == s1');
      lemma_prun_compat b.b_rel b.b_lk b.b_apply n w0 d1 d2;
      eliminate exists (w': pworld).
          (pwf_world w' /\ pwext w' w0 /\
           pcfrel b.b_rel w' (fst (prun b.b_lk b.b_apply n d1))
                             (fst (prun b.b_lk b.b_apply n d2)))
      with begin
        let e1 = fst (prun b.b_lk b.b_apply n d1) in
        let e2 = fst (prun b.b_lk b.b_apply n d2) in
        pcfrel_unfold b.b_rel w' e1 e2 ();
        lemma_pstrel_done_inv b.b_rel w' x1 e2.st;
        let x2 = PDone?.value e2.st in
        lemma_prun_split b.b_lk b.b_apply a2 n cf2;
        lemma_pnconverges_at b.b_lk b.b_apply cf2 (a2 + n) tr x2 e2.store;
        introduce exists (y2: pval v) (t2: pstore v cl) (ww: pworld).
            (pnconverges b.b_lk b.b_apply cf2 tr y2 t2 /\
             pwf_world ww /\ pwext ww w0 /\
             pval_rel ww x1 y2 /\ psrel b.b_rel ww s1' t2)
        with x2 e2.store w' and ()
      end
    end

(* ------------------------------------------------------------------ *)
(*  THE ONE OBLIGATION THAT CLOSES: THE ALGEBRAIC HALF, WHERE THE      *)
(*  NAMED CONTEXT HOLDS NO REQUESTS                                     *)
(*                                                                     *)
(*  `law_assoc_nom`'s first conjunct names a context the program did    *)
(*  not itself produce, so it stands at whatever the store says.  At    *)
(*  the two shapes below the two sides reach configurations that ARE    *)
(*  related, in BOTH directions, and the observation's consequent       *)
(*  follows from the fundamental theorem with no world written by hand. *)
(*                                                                     *)
(*  THIS IS NOT THE LAW.  `pnobs_tr_le` quantifies over every store,    *)
(*  and the third shape -- a context that HOLDS REQUESTS -- is the one  *)
(*  `guard_align_bracketing` refutes.  What is proved below is the      *)
(*  obligation AT the configurations named and nowhere else.            *)
(* ------------------------------------------------------------------ *)

(** **Absent handle: the two sides reach the SAME configuration.** PROVED --
    same stuck state, same store, same counter -- so the obligation holds in
    both directions. *)
let lemma_aa_common_absent (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
  : Lemma (requires pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
                    presolve sto cxh == None)
          (ensures
            (let d : pconf v cl =
               { st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 } in
             prun b.b_lk b.b_apply 2
               ({ st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g)
                                    (fun cy -> ref_ops.o_extend pl cy h)) amb;
                  store = sto; next = n0 }) == (d, ([] <: list string)) /\
             prun b.b_lk b.b_apply 1
               ({ st = PStep (ref_ops.o_extend pl cxh (pcompose g h)) amb;
                  store = sto; next = n0 }) == (d, ([] <: list string)) /\
             pcfrel b.b_rel (panchor sto) d d))
  = lemma_prefix_aa_stuck_l b.b_lk b.b_apply pl cxh g h amb sto n0;
    lemma_prefix_aa_stuck_r b.b_lk b.b_apply pl cxh g h amb sto n0;
    lemma_panchor_wf sto;
    lemma_panchor_bound sto n0;
    lemma_psrel_anchor_at b.b_rel sto

(** **A context that holds no requests: the two sides reach related
    configurations.** PROVED. The left allocated a copy of it and the right did
    not, so the two stores differ in one entry -- and that entry is named by no
    key the anchor speaks for, which is `lemma_psrel_garbage`. Both computations
    are `PVar y`, because extending a `PCtxDone` absorbs the extension and
    driving one returns the value. *)
let lemma_aa_common_done (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat) (y: pval v)
  : Lemma (requires pequivariant_k_at b.b_rel (panchor sto) amb /\
                    pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
                    presolve sto cxh == Some (PCtxDone y))
          (ensures
            (let d1 : pconf v cl =
               { st = PStep (PVar y) amb;
                 store = (n0, PCtxDone y) :: sto; next = n0 + 1 } in
             let d2 : pconf v cl =
               { st = PStep (PVar y) amb; store = sto; next = n0 } in
             prun b.b_lk b.b_apply 4
               ({ st = PStep (pbind (ref_ops.o_extend_ctx pl cxh g)
                                    (fun cy -> ref_ops.o_extend pl cy h)) amb;
                  store = sto; next = n0 }) == (d1, ([] <: list string)) /\
             prun b.b_lk b.b_apply 1
               ({ st = PStep (ref_ops.o_extend pl cxh (pcompose g h)) amb;
                  store = sto; next = n0 }) == (d2, ([] <: list string)) /\
             pcfrel b.b_rel (panchor sto) d1 d2 /\
             pcfrel b.b_rel (panchor sto) d2 d1))
  = let w0 = panchor sto in
    lemma_prefix_aa_l b.b_lk b.b_apply pl cxh g h amb sto n0 (PCtxDone y);
    lemma_prefix_aa_r b.b_lk b.b_apply pl cxh g h amb sto n0 (PCtxDone y);
    assert (extend_ctx_C pl (PCtxDone y) g == PCtxDone y);
    assert (ctx_drive MExtend (PCtxDone y) h == PVar y);
    assert (ctx_drive MExtend (PCtxDone y) (pcompose g h) == PVar y);
    lemma_panchor_wf sto;
    lemma_panchor_bound sto n0;
    lemma_pwext_refl w0;
    lemma_presolve_selfrel b.b_rel sto cxh (PCtxDone y);
    lemma_pxrel_done_inv b.b_rel w0 y y;
    lemma_pcrel_var b.b_rel w0 y y;
    pequivariant_k_at_unfold b.b_rel w0 amb ();
    assert (pkrel b.b_rel w0 amb amb);
    lemma_psrel_garbage b.b_rel sto n0 (PCtxDone y)

(**
 * **THE ALGEBRAIC HALF'S OBLIGATION, DISCHARGED WHERE THE NAMED HANDLE IS
 * ABSENT.** PROVED, IN BOTH DIRECTIONS, for an arbitrary boundary, plan,
 * handle, pair of extensions, ambient stack, store and counter.
 *
 * The world is not written anywhere: it is whatever the fundamental theorem's
 * induction accumulated, which by construction is `panchor sto` plus one pair
 * per allocation. Here it accumulates nothing, because neither side allocates.
 *)
let lemma_aa_obs_absent (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
    (tr: list string) (x1: pval v) (s1': pstore v cl)
  : Lemma (requires
             (let lhs : pcomp v cl =
                pbind (ref_ops.o_extend_ctx pl cxh g)
                      (fun cy -> ref_ops.o_extend pl cy h) in
              let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
              pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
              presolve sto cxh == None /\
              pnconverges b.b_lk b.b_apply
                ({ st = PStep lhs amb; store = sto; next = n0 }) tr x1 s1'))
          (ensures
             (let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
              exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                pnconverges b.b_lk b.b_apply
                  ({ st = PStep rhs amb; store = sto; next = n0 }) tr x2 s2' /\
                pwf_world w /\ pwext w (panchor sto) /\
                pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = let lhs : pcomp v cl =
      pbind (ref_ops.o_extend_ctx pl cxh g) (fun cy -> ref_ops.o_extend pl cy h) in
    let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
    let d : pconf v cl =
      { st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 } in
    lemma_aa_common_absent b pl cxh g h amb sto n0;
    lemma_obs_from_common b lhs rhs amb sto n0 2 1 d d tr x1 s1'

(** The same, the other way round. PROVED, by the same two facts: the two
    configurations are literally equal, so the composition applies with the two
    prefixes exchanged. *)
let lemma_aa_obs_absent_rev (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat)
    (tr: list string) (x1: pval v) (s1': pstore v cl)
  : Lemma (requires
             (let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
              pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
              presolve sto cxh == None /\
              pnconverges b.b_lk b.b_apply
                ({ st = PStep rhs amb; store = sto; next = n0 }) tr x1 s1'))
          (ensures
             (let lhs : pcomp v cl =
                pbind (ref_ops.o_extend_ctx pl cxh g)
                      (fun cy -> ref_ops.o_extend pl cy h) in
              exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                pnconverges b.b_lk b.b_apply
                  ({ st = PStep lhs amb; store = sto; next = n0 }) tr x2 s2' /\
                pwf_world w /\ pwext w (panchor sto) /\
                pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = let lhs : pcomp v cl =
      pbind (ref_ops.o_extend_ctx pl cxh g) (fun cy -> ref_ops.o_extend pl cy h) in
    let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
    let d : pconf v cl =
      { st = PStuck pctx_eff pctx_missing_op; store = sto; next = n0 } in
    lemma_aa_common_absent b pl cxh g h amb sto n0;
    lemma_obs_from_common b rhs lhs amb sto n0 1 2 d d tr x1 s1'

(**
 * **AND WHERE THE NAMED CONTEXT HOLDS NO REQUESTS.** PROVED, in both
 * directions. The left allocated one entry the right did not; the anchor names
 * neither, so `psrel` never looks at it, and the values the two sides answer
 * with are the same one.
 *)
let lemma_aa_obs_done (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat) (y: pval v)
    (tr: list string) (x1: pval v) (s1': pstore v cl)
  : Lemma (requires
             (let lhs : pcomp v cl =
                pbind (ref_ops.o_extend_ctx pl cxh g)
                      (fun cy -> ref_ops.o_extend pl cy h) in
              pequivariant_k_at b.b_rel (panchor sto) amb /\
              pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
              presolve sto cxh == Some (PCtxDone y) /\
              pnconverges b.b_lk b.b_apply
                ({ st = PStep lhs amb; store = sto; next = n0 }) tr x1 s1'))
          (ensures
             (let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
              exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                pnconverges b.b_lk b.b_apply
                  ({ st = PStep rhs amb; store = sto; next = n0 }) tr x2 s2' /\
                pwf_world w /\ pwext w (panchor sto) /\
                pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = let lhs : pcomp v cl =
      pbind (ref_ops.o_extend_ctx pl cxh g) (fun cy -> ref_ops.o_extend pl cy h) in
    let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
    let d1 : pconf v cl =
      { st = PStep (PVar y) amb; store = (n0, PCtxDone y) :: sto; next = n0 + 1 } in
    let d2 : pconf v cl = { st = PStep (PVar y) amb; store = sto; next = n0 } in
    lemma_aa_common_done b pl cxh g h amb sto n0 y;
    lemma_obs_from_common b lhs rhs amb sto n0 4 1 d1 d2 tr x1 s1'

let lemma_aa_obs_done_rev (#v #cl: Type) (b: pboundary v cl)
    (pl: plan v cl) (cxh: pval v) (g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto: pstore v cl) (n0: nat) (y: pval v)
    (tr: list string) (x1: pval v) (s1': pstore v cl)
  : Lemma (requires
             (let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
              pequivariant_k_at b.b_rel (panchor sto) amb /\
              pstore_equivariant_at b.b_rel sto /\ psfresh sto n0 /\
              presolve sto cxh == Some (PCtxDone y) /\
              pnconverges b.b_lk b.b_apply
                ({ st = PStep rhs amb; store = sto; next = n0 }) tr x1 s1'))
          (ensures
             (let lhs : pcomp v cl =
                pbind (ref_ops.o_extend_ctx pl cxh g)
                      (fun cy -> ref_ops.o_extend pl cy h) in
              exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                pnconverges b.b_lk b.b_apply
                  ({ st = PStep lhs amb; store = sto; next = n0 }) tr x2 s2' /\
                pwf_world w /\ pwext w (panchor sto) /\
                pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = let lhs : pcomp v cl =
      pbind (ref_ops.o_extend_ctx pl cxh g) (fun cy -> ref_ops.o_extend pl cy h) in
    let rhs : pcomp v cl = ref_ops.o_extend pl cxh (pcompose g h) in
    let d1 : pconf v cl =
      { st = PStep (PVar y) amb; store = (n0, PCtxDone y) :: sto; next = n0 + 1 } in
    let d2 : pconf v cl = { st = PStep (PVar y) amb; store = sto; next = n0 } in
    lemma_aa_common_done b pl cxh g h amb sto n0 y;
    lemma_obs_from_common b rhs lhs amb sto n0 1 4 d2 d1 tr x1 s1'

(* ------------------------------------------------------------------ *)
(*  THE OBSTRUCTIONS, AT THE CONFIGURATIONS THE PREFIXES ACTUALLY      *)
(*  REACH                                                              *)
(* ------------------------------------------------------------------ *)

let lemma_pcfrel_stacks_inv (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (c1 c2: pcomp v cl) (k1 k2: pstack v cl) (s1 s2: pstore v cl) (m1 m2: nat)
  : Lemma (requires pcfrel r w ({ st = PStep c1 k1; store = s1; next = m1 })
                               ({ st = PStep c2 k2; store = s2; next = m2 }))
          (ensures pkrel r w k1 k2)
  = pcfrel_unfold r w ({ st = PStep c1 k1; store = s1; next = m1 })
                      ({ st = PStep c2 k2; store = s2; next = m2 }) ();
    pstrel_unfold r w (PStep c1 k1) (PStep c2 k2) ()

(** **RIGHT IDENTITY AND TRANSPARENCY: the prefixes are exact and the theorem
    cannot be started.** PROVED, at every plan, inner computation, continuation,
    ambient stack, store, counter and world. The two sides reach the SAME node
    `c`; the stacks differ. *)
let guard_align_ri_post_unrelated (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (c: pcomp v cl) (f: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto1 sto2: pstore v cl) (m1 m2: nat)
  : Lemma (~(pcfrel r w
               ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                               @ (PScopeF :: PBindF f :: amb)));
                  store = sto1; next = m1 })
               ({ st = PStep c (plan_enter_frames pl @ amb);
                  store = sto2; next = m2 })))
  = guard_align_produce_vs_enter r w pl f amb;
    introduce pcfrel r w
                ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                                @ (PScopeF :: PBindF f :: amb)));
                   store = sto1; next = m1 })
                ({ st = PStep c (plan_enter_frames pl @ amb);
                   store = sto2; next = m2 }) ==> False
    with
      lemma_pcfrel_stacks_inv r w c c
        (PBoundaryF :: (plan_protocol_frames pl @ (PScopeF :: PBindF f :: amb)))
        (plan_enter_frames pl @ amb) sto1 sto2 m1 m2

(** **THE ANCHORED HALF OF ASSOCIATIVITY: the same, with the two binds in
    place.** PROVED. *)
let guard_align_ac_post_unrelated (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (c: pcomp v cl) (f g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto1 sto2: pstore v cl) (m1 m2: nat)
  : Lemma (~(pcfrel r w
               ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                               @ (PScopeF :: PBindF f :: amb)));
                  store = sto1; next = m1 })
               ({ st = PStep c (PBindF g :: PBindF h :: (plan_enter_frames pl @ amb));
                  store = sto2; next = m2 })))
  = guard_align_produce_vs_enter_bind2 r w pl f g h amb;
    introduce pcfrel r w
                ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                                @ (PScopeF :: PBindF f :: amb)));
                   store = sto1; next = m1 })
                ({ st = PStep c (PBindF g :: PBindF h
                                 :: (plan_enter_frames pl @ amb));
                   store = sto2; next = m2 }) ==> False
    with
      lemma_pcfrel_stacks_inv r w c c
        (PBoundaryF :: (plan_protocol_frames pl @ (PScopeF :: PBindF f :: amb)))
        (PBindF g :: PBindF h :: (plan_enter_frames pl @ amb)) sto1 sto2 m1 m2

(** **LEFT IDENTITY: both sides reach `g x`, and the stacks differ.** PROVED. *)
let guard_align_li_post_unrelated (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (c: pcomp v cl) (m: weave_mode) (resp: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto1 sto2: pstore v cl) (m1 m2: nat)
  : Lemma (~(pcfrel r w
               ({ st = PStep c (plan_protocol_frames pl @ (PModeF m resp :: amb));
                  store = sto1; next = m1 })
               ({ st = PStep c (plan_enter_frames pl @ amb);
                  store = sto2; next = m2 })))
  = guard_align_marker_vs_enter r w pl m resp amb;
    introduce pcfrel r w
                ({ st = PStep c (plan_protocol_frames pl @ (PModeF m resp :: amb));
                   store = sto1; next = m1 })
                ({ st = PStep c (plan_enter_frames pl @ amb);
                   store = sto2; next = m2 }) ==> False
    with
      lemma_pcfrel_stacks_inv r w c c
        (plan_protocol_frames pl @ (PModeF m resp :: amb))
        (plan_enter_frames pl @ amb) sto1 sto2 m1 m2

(** **RESUMPTION: both sides reach `k x`, and the stacks differ by the marker
    and by nothing else.** PROVED. *)
let guard_align_rm_post_unrelated (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (c: pcomp v cl) (m: weave_mode) (resp: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto1 sto2: pstore v cl) (m1 m2: nat)
  : Lemma (~(pcfrel r w
               ({ st = PStep c (plan_protocol_frames pl @ (PModeF m resp :: amb));
                  store = sto1; next = m1 })
               ({ st = PStep c (plan_resume_frames pl @ amb);
                  store = sto2; next = m2 })))
  = guard_align_marker_vs_resume r w pl m resp amb;
    introduce pcfrel r w
                ({ st = PStep c (plan_protocol_frames pl @ (PModeF m resp :: amb));
                   store = sto1; next = m1 })
                ({ st = PStep c (plan_resume_frames pl @ amb);
                   store = sto2; next = m2 }) ==> False
    with
      lemma_pcfrel_stacks_inv r w c c
        (plan_protocol_frames pl @ (PModeF m resp :: amb))
        (plan_resume_frames pl @ amb) sto1 sto2 m1 m2

(* ------------------------------------------------------------------ *)
(*  TWO OF THE SIX PROPOSITIONS ARE ONE                                *)
(* ------------------------------------------------------------------ *)

(**
 * **AT `ref_ops`, TRANSPARENCY IS RIGHT IDENTITY.** PROVED, and it is an
 * equality of PROPOSITIONS rather than an implication either way: `o_enter` of
 * the reference algebra IS `PSplice (plan_enter_frames pl)`, so the two
 * statements have the same two sides.
 *
 * What this does NOT say: it says nothing about any other `ctx_ops`, where the
 * two differ exactly as much as `o_enter` differs from the plan. The
 * transparency law's hypothesis -- that every layer is transparent -- is not
 * stated in `law_transparent_agrees_nom` at all, so it plays no part here.
 *)
let guard_align_transparent_is_right_identity (#v #cl: Type)
    (b: pboundary v cl) (pl: plan v cl) (c: pcomp v cl)
  : Lemma (law_transparent_agrees_nom b ref_ops pl c
           == law_right_identity_nom b ref_ops pl c)
  = ()

(**
 * **AND LEFT IDENTITY AT `PVar` IS RIGHT IDENTITY AT A VALUE.** PROVED, the same
 * way. It leaves left identity at a GENERAL `g` untouched: nothing here says the
 * two are the same proposition for any other extension function.
 *)
let guard_align_left_identity_at_pure (#v #cl: Type)
    (b: pboundary v cl) (pl: plan v cl) (x: pval v)
  : Lemma (law_left_identity_nom b ref_ops pl x (PVar #v #cl)
           == law_right_identity_nom b ref_ops pl (PVar x))
  = assert_norm (law_left_identity_nom b ref_ops pl x (PVar #v #cl)
                 == law_right_identity_nom b ref_ops pl (PVar x))

(* ================================================================== *)
(*  B2b.3, PART 2: A COUNTEREXAMPLE, AND IT IS NOT ABOUT NAMES         *)
(*                                                                     *)
(*  The four obstructions above say the fundamental theorem cannot be   *)
(*  STARTED at the post-prefix configurations.  That is a statement     *)
(*  about a proof route and not about the laws, so it is not yet a      *)
(*  refutation.  What follows IS one.                                   *)
(*                                                                     *)
(*  THE MECHANISM, AND IT IS THE ONE THE FOUR OBSTRUCTIONS POINT AT.    *)
(*  A residual is produced under `plan_protocol_frames`, which keeps a  *)
(*  `PSiteF` where `plan_enter_frames` drops the plan item; a consumer  *)
(*  appends its `PModeF` marker BENEATH the residual, and under         *)
(*  `MExtend` a `PSiteF` that finds that marker is skipped -- so as     *)
(*  long as the marker stays below the site frame, the two sides agree, *)
(*  and every fixture in this file stays in that regime.                *)
(*                                                                     *)
(*  A CLAUSE CAN TAKE THE SITE FRAME AWAY FROM ITS MARKER.  Dispatch    *)
(*  captures the segment ABOVE the matching prompt and hands it to the  *)
(*  interpreter as a continuation; a clause that resumes that           *)
(*  continuation INSIDE A FRESH SCOPE puts the captured `PSiteF` above  *)
(*  a floor with no marker in scope, and the site frame YIELDS where    *)
(*  the right-hand side, which never had one, does not.  The two runs   *)
(*  then store residuals of DIFFERENT LENGTHS and answer with handles   *)
(*  to them, and no world can relate two contexts whose residuals do    *)
(*  not correspond frame for frame.                                     *)
(*                                                                     *)
(*  Resuming a captured continuation inside a new scope is what an      *)
(*  effect handler does; nothing here is pathological, and the          *)
(*  interpreter below is PROVED equivariant.  The store the            *)
(*  counterexample stands at is the EMPTY one, the ambient stack is     *)
(*  EMPTY, and the counter is ZERO, so it is not a configuration the    *)
(*  observation reaches only by quantifying over odd stacks.            *)
(* ================================================================== *)

(** A table binding nothing: `flook` answers `None` for every effect, because
    `flook` consults `binds` first. *)
let xtbl0 : ptable fcl = { hs = fhs; binds = [] }

(** A table binding `"Echo"`, which `flook` answers with `FEcho` at kind
    `KFull` -- so a perform of it dispatches through the ordinary path. *)
let xltbl : ptable fcl = { hs = fhs; binds = ["Echo"] }

(** The plan the law is taken at: ONE recorded bind site, and ONE layer prompt
    beneath it. The site frame is what `plan_protocol_frames` keeps and
    `plan_enter_frames` drops; the prompt beneath it is what makes the capture
    stop between the two. *)
let xpl : plan fv fcl =
  Plan [PIBind (PVar #fv #fcl); PIReenter xltbl None] (POwner xtbl0 None PFamily)

(** The plan the CLAUSE opens. Any plan with a floor would do; this is the
    smallest. *)
let xplan : plan fv fcl = Plan [] (POwner xtbl0 None PFamily)

(** **The clause interpreter: resume the captured continuation inside a fresh
    scope.** This is `withF`-style handling, not a forgery: it builds one
    ordinary node and applies the continuation it was given. *)
let xapply : papply_t fv fcl = fun _ _ kk -> PEnterCtx xplan (kk (fpv FU))

let lemma_xtbl0_selfrel (n: nat) (w: pworld)
  : Lemma (ptable_rel fcl_rel n w xtbl0 xtbl0)
  = introduce forall (eff op: string).
      (match lookup_handler xtbl0.hs eff op, lookup_handler xtbl0.hs eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ fcl_rel n w f1.body f2.body
       | _, _ -> False)
    with (lookup_handler_mk_handlers #fcl (fun _ -> KFast) [] eff op;
          assert (lookup_handler xtbl0.hs eff op == None))

let lemma_xplan_selfrel (n: nat) (w: pworld)
  : Lemma (pplan_rel fcl_rel n w xplan xplan)
  = if n = 0 then () else lemma_xtbl0_selfrel n w

(** **The interpreter is EQUIVARIANT.** PROVED. It reads no handle, and the plan
    it opens is related to itself at every world, so related continuations go to
    related computations -- which is all the boundary asks of it. *)
let lemma_xapply_equivariant () : Lemma (papply_equivariant fcl_rel xapply)
  = introduce forall (w: pworld) (c1 c2: fcl) (p1 p2: list (pval fv))
                     (kk1 kk2: pval fv -> pcomp fv fcl).
      (pwf_world w /\ pclrel fcl_rel w c1 c2 /\ pvals_rel w p1 p2 /\
       pfn_rel_at fcl_rel w kk1 kk2 ==>
       pcrel fcl_rel w (xapply c1 p1 kk1) (xapply c2 p2 kk2))
    with (introduce _ ==> _
          with begin
            lemma_pwext_refl w;
            assert (pval_rel #fv w (fpv FU) (fpv FU));
            assert (pcrel fcl_rel w (kk1 (fpv FU)) (kk2 (fpv FU)));
            introduce forall (n: nat).
                pcomp_rel fcl_rel n w (PEnterCtx xplan (kk1 (fpv FU)))
                                      (PEnterCtx xplan (kk2 (fpv FU)))
            with (if n = 0 then ()
                  else (lemma_xplan_selfrel (n - 1) w;
                        assert (pcomp_rel fcl_rel (n - 1) w (kk1 (fpv FU))
                                                            (kk2 (fpv FU)))))
          end)

(** The boundary this counterexample stands at. Every one of the four conditions
    is discharged; none of them is weakened. *)
let xboundary : pboundary fv fcl = {
  b_rel = fcl_rel;
  b_lk = flook;
  b_apply = xapply;
  b_mono = lemma_fcl_rel_mono ();
  b_down = lemma_fcl_rel_down ();
  b_lookup = lemma_flook_equivariant ();
  b_apply_eq = lemma_xapply_equivariant ();
}

(** The extension: perform the effect the layer prompt binds. *)
let xg : pval fv -> pcomp fv fcl = fun _ -> PPerform "Echo" "op" []

let xlhs : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx xpl (PVar fone)) (fun cx -> ref_ops.o_extend xpl cx xg)
let xrhs : pcomp fv fcl = ref_ops.o_enter xpl (xg fone)

let xcf_l : pconf fv fcl = { st = PStep xlhs ([] <: pstack fv fcl); store = []; next = 0 }
let xcf_r : pconf fv fcl = { st = PStep xrhs ([] <: pstack fv fcl); store = []; next = 0 }

let xsl : pstore fv fcl = (fst (prun flook xapply 30 xcf_l)).store
let xsr : pstore fv fcl = (fst (prun flook xapply 30 xcf_r)).store

(** **BOTH SIDES CONVERGE, SILENTLY, AND ANSWER WITH A HANDLE.** PROVED by
    running the machine: `flook` is an ordinary function of the table's `binds`,
    so the whole run normalises. *)
let guard_xce_runs ()
  : Lemma ((fst (prun flook xapply 30 xcf_l)).st == PDone (PCtxKey 1) /\
           snd (prun flook xapply 30 xcf_l) == ([] <: list string) /\
           (fst (prun flook xapply 30 xcf_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 30 xcf_r) == ([] <: list string))
  = assert_norm ((fst (prun flook xapply 30 xcf_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook xapply 30 xcf_l) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 30 xcf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 30 xcf_r) == ([] <: list string))


(** The residual a context holds, as a TOTAL accessor with a junk default. A
    projector under a discriminator would put a precondition inside a `prop`,
    which is exactly what stops SMT instantiation. *)
let presid_of (#v #cl: Type) (cx: pctx v cl) : pstack v cl
  = match cx with
    | PCtxRequests _ rs _ -> rs
    | PCtxDone _ -> []

(** Two related contexts hold related residuals. PROVED, from the shape lemma
    and the requests inversion. *)
let lemma_pxrel_resid (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (cx1 cx2: pctx v cl)
  : Lemma (requires pxrel r w cx1 cx2)
          (ensures pkrel r w (presid_of cx1) (presid_of cx2))
  = lemma_pxrel_shape r w cx1 cx2;
    match cx1, cx2 with
    | PCtxRequests a1 r1 p1, PCtxRequests a2 r2 p2 ->
      lemma_pxrel_requests_inv r w a1 a2 r1 r2 p1 p2
    | PCtxDone _, PCtxDone _ -> lemma_pkrel_nil #v #cl r w
    | _, _ -> ()

(** **AND THE TWO CONTEXTS THE ANSWERS NAME HOLD RESIDUALS OF DIFFERENT
    LENGTHS.** PROVED by running the machine. The left's carries the plan's
    recorded site frame and the layer prompt the capture took with it; the
    right's carries neither. *)
let guard_xce_residuals ()
  : Lemma (length (presid_of (psget 1 xsl)) == 4 /\
           length (presid_of (psget 0 xsr)) == 2)
  = assert_norm (length (presid_of (psget 1 xsl)) == 4);
    assert_norm (length (presid_of (psget 0 xsr)) == 2)

(* ---- The two casts the refutation needs, each BY CONVERSION -------- *)

(** A `GTot prop` definition applied in HYPOTHESIS position is an atom to the
    SMT encoding, so the quantifier inside `pnobs_tr_le` is invisible. This cast
    puts the body in the context; it has no proof obligation at all. *)
let pnobs_tr_le_unfold (#v #cl: Type) (b: pboundary v cl) (c1 c2: pcomp v cl)
                       (h: squash (pnobs_tr_le b c1 c2))
  : squash (forall (k: pstack v cl) (sto: pstore v cl) (n0: nat)
                   (tr: list string) (x1: pval v) (s1': pstore v cl).
              (pequivariant_k_at b.b_rel (panchor sto) k /\
               pstore_equivariant_at b.b_rel sto /\
               psfresh sto n0 /\
               pnconverges b.b_lk b.b_apply
                           ({ st = PStep c1 k; store = sto; next = n0 }) tr x1 s1') ==>
              (exists (x2: pval v) (s2': pstore v cl) (w: pworld).
                 pnconverges b.b_lk b.b_apply
                             ({ st = PStep c2 k; store = sto; next = n0 }) tr x2 s2' /\
                 pwf_world w /\ pwext w (panchor sto) /\
                 pval_rel w x1 x2 /\ psrel b.b_rel w s1' s2'))
  = h

let psrel_unfold (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (s1 s2: pstore v cl)
                 (h: squash (psrel r w s1 s2))
  : squash (forall (i j: nat). {:pattern (pstore_lookup i s1); (pstore_lookup j s2)}
              pwlookup_l i w == Some j ==>
              (Some? (pstore_lookup i s1) /\ Some? (pstore_lookup j s2) /\
               pxrel r w (psget i s1) (psget j s2)))
  = h

let pval_rel_key_unfold (#v: Type) (w: pworld) (i j: nat)
                        (h: squash (pval_rel #v w (PCtxKey i) (PCtxKey j)))
  : squash (pwlookup_l i w == Some j)
  = h

let law_li_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (x: pval v) (g: pval v -> pcomp v cl)
    (h: squash (law_left_identity_nom b ops pl x g))
  : squash (pnobs_tr_le b
              (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_extend pl cx g))
              (ops.o_enter pl (g x)))
  = h

(**
 * **`law_left_identity_nom` IS FALSE OF `ref_ops`, AND THE NEGATION IS PROVED.**
 *
 * At the boundary `xboundary`, the plan `xpl`, the value `fone` and the
 * extension `xg` -- on the EMPTY ambient stack, at the EMPTY store and at
 * counter ZERO, all three of which satisfy the nominal observation's
 * hypotheses.
 *
 * **What this refutation is NOT.** It is not the counter, and it is not a name:
 * the two sides allocate the same NUMBER of contexts, both answer with a handle,
 * and a world relating the two handles is available for the asking. What no
 * world can do is relate the two CONTEXTS those handles name, because their
 * residuals differ by two frames -- and `psrel` compares the entries a world
 * speaks for, which is exactly the repair B2b.1 made. So the repaired relation
 * is doing its work here and the law fails anyway.
 *
 * **Where the difference comes from.** The left-hand side's `g x` runs inside
 * the residual protocol, so the segment the dispatch captures contains the
 * plan's recorded `PSiteF`; the right-hand side's runs inside
 * `plan_enter_frames`, which dropped it. The clause resumes what it captured
 * inside a scope of its own, and there the site frame finds a floor instead of
 * the extension's marker, so it yields -- storing a residual two frames longer
 * than the one the right-hand side stores.
 *)
(** **NO WORLD RELATES THE TWO ANSWERS.** PROVED, and it is the whole of the
    refutation, factored out so that the query above stays small. The right run's
    convergence is unique, so the witness the observation offers must be `PCtxKey
    0` at the store the right run left; the world must then speak for the pair,
    and `psrel` at that pair asks the two residuals to correspond frame for
    frame, which four frames against two do not. *)
let lemma_xce_no_world (w: pworld) (x2: pval fv) (s2': pstore fv fcl)
  : Lemma (requires pnconverges flook xapply xcf_r ([] <: list string) x2 s2' /\
                    pval_rel w (PCtxKey 1) x2 /\ psrel fcl_rel w xsl s2')
          (ensures False)
  = guard_xce_runs ();
    guard_xce_residuals ();
    lemma_pnconverges_at flook xapply xcf_r 30 [] (PCtxKey 0) xsr;
    lemma_pnconverges_unique flook xapply xcf_r [] [] x2 (PCtxKey 0) s2' xsr;
    pval_rel_key_unfold #fv w 1 0 ();
    assert_norm (Some? (pstore_lookup 1 xsl));
    assert_norm (Some? (pstore_lookup 0 xsr));
    psrel_unfold fcl_rel w xsl xsr ();
    lemma_pxrel_resid fcl_rel w (psget 1 xsl) (psget 0 xsr);
    lemma_pkrel_length fcl_rel w (presid_of (psget 1 xsl))
                                 (presid_of (psget 0 xsr))

let guard_ref_ops_refutes_left_identity_nom ()
  : Lemma (~(law_left_identity_nom xboundary ref_ops xpl fone xg))
  = guard_xce_runs ();
    lemma_pnconverges_at flook xapply xcf_l 30 [] (PCtxKey 1) xsl;
    assert_norm (panchor ([] <: pstore fv fcl) == ([] <: pworld));
    introduce forall (w: pworld). pkrel #fv #fcl fcl_rel w [] []
    with lemma_pkrel_nil #fv #fcl fcl_rel w;
    assert (pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl))
                              ([] <: pstack fv fcl));
    assert (pstore_equivariant_at fcl_rel ([] <: pstore fv fcl));
    assert (psfresh ([] <: pstore fv fcl) 0);
    assert_norm (xboundary.b_rel == fcl_rel);
    assert_norm (xboundary.b_lk == flook);
    assert_norm (xboundary.b_apply == xapply);
    introduce law_left_identity_nom xboundary ref_ops xpl fone xg ==> False
    with begin
      law_li_nom_unfold xboundary ref_ops xpl fone xg ();
      pnobs_tr_le_unfold xboundary xlhs xrhs ();
      assert (pnconverges xboundary.b_lk xboundary.b_apply
                ({ st = PStep xlhs ([] <: pstack fv fcl);
                   store = ([] <: pstore fv fcl); next = 0 })
                ([] <: list string) (PCtxKey 1) xsl);
      eliminate exists (x2: pval fv) (s2': pstore fv fcl) (w: pworld).
          (pnconverges flook xapply xcf_r ([] <: list string) x2 s2' /\
           pwf_world w /\ pwext w (panchor ([] <: pstore fv fcl)) /\
           pval_rel w (PCtxKey 1) x2 /\ psrel fcl_rel w xsl s2')
      with lemma_xce_no_world w x2 s2'
    end

let xc : pcomp fv fcl = PPerform "Echo" "op" []
let ylhs : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx xpl xc) (fun cx -> ref_ops.o_extend xpl cx (PVar #fv #fcl))
let yrhs : pcomp fv fcl = ref_ops.o_enter xpl xc
let ycf_l : pconf fv fcl = { st = PStep ylhs ([] <: pstack fv fcl); store = []; next = 0 }
let ycf_r : pconf fv fcl = { st = PStep yrhs ([] <: pstack fv fcl); store = []; next = 0 }
let zlhs : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx xpl (PVar fone)) (fun cx -> ref_ops.o_resume xpl cx xg)
let zrhs : pcomp fv fcl = PSplice (plan_resume_frames xpl) (xg fone)
let zcf_l : pconf fv fcl = { st = PStep zlhs ([] <: pstack fv fcl); store = []; next = 0 }
let zcf_r : pconf fv fcl = { st = PStep zrhs ([] <: pstack fv fcl); store = []; next = 0 }

let ysl : pstore fv fcl = (fst (prun flook xapply 40 ycf_l)).store
let ysr : pstore fv fcl = (fst (prun flook xapply 40 ycf_r)).store
let zsl : pstore fv fcl = (fst (prun flook xapply 40 zcf_l)).store
let zsr : pstore fv fcl = (fst (prun flook xapply 40 zcf_r)).store

let guard_yce_runs ()
  : Lemma ((fst (prun flook xapply 40 ycf_l)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 40 ycf_l) == ([] <: list string) /\
           (fst (prun flook xapply 40 ycf_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 40 ycf_r) == ([] <: list string) /\
           length (presid_of (psget 0 ysl)) == 5 /\
           length (presid_of (psget 0 ysr)) == 2)
  = assert_norm ((fst (prun flook xapply 40 ycf_l)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 40 ycf_l) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 40 ycf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 40 ycf_r) == ([] <: list string));
    assert_norm (length (presid_of (psget 0 ysl)) == 5);
    assert_norm (length (presid_of (psget 0 ysr)) == 2)

let guard_zce_runs ()
  : Lemma ((fst (prun flook xapply 40 zcf_l)).st == PDone (PCtxKey 1) /\
           snd (prun flook xapply 40 zcf_l) == ([] <: list string) /\
           (fst (prun flook xapply 40 zcf_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 40 zcf_r) == ([] <: list string) /\
           length (presid_of (psget 1 zsl)) == 4 /\
           length (presid_of (psget 0 zsr)) == 2)
  = assert_norm ((fst (prun flook xapply 40 zcf_l)).st == PDone (PCtxKey 1));
    assert_norm (snd (prun flook xapply 40 zcf_l) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 40 zcf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 40 zcf_r) == ([] <: list string));
    assert_norm (length (presid_of (psget 1 zsl)) == 4);
    assert_norm (length (presid_of (psget 0 zsr)) == 2)

let alhs : pcomp fv fcl =
  pbind (ref_ops.o_enter_ctx xpl xc)
        (fun c0 -> pbind (ref_ops.o_extend_ctx xpl c0 (PVar #fv #fcl))
                         (fun cy -> ref_ops.o_extend xpl cy (PVar #fv #fcl)))
let arhs : pcomp fv fcl =
  PSplice (plan_enter_frames xpl) (pbind (pbind xc (PVar #fv #fcl)) (PVar #fv #fcl))
let acf_l : pconf fv fcl = { st = PStep alhs ([] <: pstack fv fcl); store = []; next = 0 }
let acf_r : pconf fv fcl = { st = PStep arhs ([] <: pstack fv fcl); store = []; next = 0 }
let asl : pstore fv fcl = (fst (prun flook xapply 40 acf_l)).store
let asr : pstore fv fcl = (fst (prun flook xapply 40 acf_r)).store

let guard_ace_runs ()
  : Lemma ((fst (prun flook xapply 40 acf_l)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 40 acf_l) == ([] <: list string) /\
           (fst (prun flook xapply 40 acf_r)).st == PDone (PCtxKey 0) /\
           snd (prun flook xapply 40 acf_r) == ([] <: list string) /\
           length (presid_of (psget 0 asl)) == 5 /\
           length (presid_of (psget 0 asr)) == 2)
  = assert_norm ((fst (prun flook xapply 40 acf_l)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 40 acf_l) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 40 acf_r)).st == PDone (PCtxKey 0));
    assert_norm (snd (prun flook xapply 40 acf_r) == ([] <: list string));
    assert_norm (length (presid_of (psget 0 asl)) == 5);
    assert_norm (length (presid_of (psget 0 asr)) == 2)

(* ---- the refutations, from one shared argument -------------------- *)

(** **NO WORLD CAN RELATE TWO ANSWERS WHOSE CONTEXTS HOLD RESIDUALS OF DIFFERENT
    LENGTHS.** PROVED, once, for every pair of runs below. *)
let lemma_ce_no_world (cfr: pconf fv fcl) (sl sr: pstore fv fcl)
    (i j: nat) (w: pworld) (x2: pval fv) (s2': pstore fv fcl)
  : Lemma (requires pnconverges flook xapply cfr ([] <: list string) x2 s2' /\
                    pnconverges flook xapply cfr ([] <: list string) (PCtxKey j) sr /\
                    pval_rel w (PCtxKey i) x2 /\ psrel fcl_rel w sl s2' /\
                    Some? (pstore_lookup i sl) /\ Some? (pstore_lookup j sr) /\
                    ~(length (presid_of (psget i sl))
                      == length (presid_of (psget j sr))))
          (ensures False)
  = lemma_pnconverges_unique flook xapply cfr [] [] x2 (PCtxKey j) s2' sr;
    pval_rel_key_unfold #fv w i j ();
    psrel_unfold fcl_rel w sl sr ();
    lemma_pxrel_resid fcl_rel w (psget i sl) (psget j sr);
    lemma_pkrel_length fcl_rel w (presid_of (psget i sl)) (presid_of (psget j sr))

let law_ri_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (c: pcomp v cl)
    (hh: squash (law_right_identity_nom b ops pl c))
  : squash (pnobs_tr_le b
              (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
              (ops.o_enter pl c))
  = hh

let law_ta_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (c: pcomp v cl)
    (hh: squash (law_transparent_agrees_nom b ops pl c))
  : squash (pnobs_tr_le b
              (pbind (ops.o_enter_ctx pl c) (fun cx -> ops.o_extend pl cx (PVar #v #cl)))
              (PSplice (plan_enter_frames pl) c))
  = hh

let law_rm_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (x: pval v) (kk: pval v -> pcomp v cl)
    (hh: squash (law_resume_matches_continuation_nom b ops pl x kk))
  : squash (pnobs_tr_le b
              (pbind (ops.o_enter_ctx pl (PVar x)) (fun cx -> ops.o_resume pl cx kk))
              (PSplice (plan_resume_frames pl) (kk x)))
  = hh

let law_ac_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (c: pcomp v cl) (cxv: pval v) (g hf: pval v -> pcomp v cl)
    (hh: squash (law_assoc_nom b ops pl c cxv g hf))
  : squash (pnobs_tr_le b
              (pbind (ops.o_enter_ctx pl c)
                     (fun c0 -> pbind (ops.o_extend_ctx pl c0 g)
                                      (fun cy -> ops.o_extend pl cy hf)))
              (PSplice (plan_enter_frames pl) (pbind (pbind c g) hf)))
  = hh

(** The three hypotheses the nominal observation puts on the ambient stack, the
    store and the counter, at the empty ones. PROVED. *)
let guard_xce_config_ok ()
  : Lemma (pequivariant_k_at fcl_rel (panchor ([] <: pstore fv fcl))
                             ([] <: pstack fv fcl) /\
           pstore_equivariant_at fcl_rel ([] <: pstore fv fcl) /\
           psfresh ([] <: pstore fv fcl) 0 /\
           xboundary.b_rel == fcl_rel /\ xboundary.b_lk == flook /\
           xboundary.b_apply == xapply)
  = assert_norm (panchor ([] <: pstore fv fcl) == ([] <: pworld));
    introduce forall (w: pworld). pkrel #fv #fcl fcl_rel w [] []
    with lemma_pkrel_nil #fv #fcl fcl_rel w;
    assert_norm (xboundary.b_rel == fcl_rel);
    assert_norm (xboundary.b_lk == flook);
    assert_norm (xboundary.b_apply == xapply)

(** **THE REFUTATION ARGUMENT, ONCE.** PROVED. Given that the two sides converge
    to two handles and that the contexts those handles name hold residuals of
    different lengths, the nominal observation's consequent is unsatisfiable: the
    right run's convergence is unique, so its answer and its store are forced,
    the world is then forced to speak for the pair, and `psrel` at that pair asks
    for a frame-for-frame correspondence that does not exist. *)
let lemma_le_refuted (c1 c2: pcomp fv fcl) (sl sr: pstore fv fcl) (i j: nat)
  : Lemma (requires
             (let cfl : pconf fv fcl =
                { st = PStep c1 ([] <: pstack fv fcl); store = []; next = 0 } in
              let cfr : pconf fv fcl =
                { st = PStep c2 ([] <: pstack fv fcl); store = []; next = 0 } in
              pnobs_tr_le xboundary c1 c2 /\
              pnconverges flook xapply cfl ([] <: list string) (PCtxKey i) sl /\
              pnconverges flook xapply cfr ([] <: list string) (PCtxKey j) sr /\
              Some? (pstore_lookup i sl) /\ Some? (pstore_lookup j sr) /\
              ~(length (presid_of (psget i sl))
                == length (presid_of (psget j sr)))))
          (ensures False)
  = guard_xce_config_ok ();
    let cfl : pconf fv fcl =
      { st = PStep c1 ([] <: pstack fv fcl); store = []; next = 0 } in
    let cfr : pconf fv fcl =
      { st = PStep c2 ([] <: pstack fv fcl); store = []; next = 0 } in
    let hle : squash (pnobs_tr_le xboundary c1 c2) = () in
    pnobs_tr_le_unfold xboundary c1 c2 hle;
    assert (pnconverges xboundary.b_lk xboundary.b_apply cfl
                        ([] <: list string) (PCtxKey i) sl);
    eliminate exists (x2: pval fv) (s2': pstore fv fcl) (w: pworld).
        (pnconverges flook xapply cfr ([] <: list string) x2 s2' /\
         pwf_world w /\ pwext w (panchor ([] <: pstore fv fcl)) /\
         pval_rel w (PCtxKey i) x2 /\ psrel fcl_rel w sl s2')
    with lemma_ce_no_world cfr sl sr i j w x2 s2'

(**
 * **`law_right_identity_nom` IS FALSE OF `ref_ops`, AND THE NEGATION IS
 * PROVED** -- and with it `law_transparent_agrees_nom`, which
 * `guard_align_transparent_is_right_identity` proves is the same proposition.
 *
 * The two sides answer with the SAME handle, `PCtxKey 0`, so the world is forced
 * to relate that key to itself -- there is no freedom left in the choice -- and
 * the contexts it then names hold residuals of five frames and of two.
 *)
let guard_ref_ops_refutes_right_identity_nom ()
  : Lemma (~(law_right_identity_nom xboundary ref_ops xpl xc))
  = guard_yce_runs ();
    lemma_pnconverges_at flook xapply ycf_l 40 [] (PCtxKey 0) ysl;
    lemma_pnconverges_at flook xapply ycf_r 40 [] (PCtxKey 0) ysr;
    assert_norm (Some? (pstore_lookup 0 ysl));
    assert_norm (Some? (pstore_lookup 0 ysr));
    introduce law_right_identity_nom xboundary ref_ops xpl xc ==> False
    with (law_ri_nom_unfold xboundary ref_ops xpl xc ();
          lemma_le_refuted ylhs yrhs ysl ysr 0 0)

let guard_ref_ops_refutes_transparent_agrees_nom ()
  : Lemma (~(law_transparent_agrees_nom xboundary ref_ops xpl xc))
  = guard_align_transparent_is_right_identity xboundary xpl xc;
    guard_ref_ops_refutes_right_identity_nom ()

(**
 * **`law_resume_matches_continuation_nom` IS FALSE OF `ref_ops`, AND THE
 * NEGATION IS PROVED.**
 *
 * Here the two sides answer with DIFFERENT handles -- `PCtxKey 1` and
 * `PCtxKey 0` -- so a world relating them is available; and it does not help,
 * because the contexts hold residuals of four frames and of two. What separates
 * them is the plan's recorded bind site: `plan_resume_frames` renders it as the
 * `PBindF` it was, which fires and disappears, while `plan_protocol_frames`
 * renders it as a `PSiteF`, which the clause carried into its own scope and
 * which yielded there.
 *)
let guard_ref_ops_refutes_resume_nom ()
  : Lemma (~(law_resume_matches_continuation_nom xboundary ref_ops xpl fone xg))
  = guard_zce_runs ();
    lemma_pnconverges_at flook xapply zcf_l 40 [] (PCtxKey 1) zsl;
    lemma_pnconverges_at flook xapply zcf_r 40 [] (PCtxKey 0) zsr;
    assert_norm (Some? (pstore_lookup 1 zsl));
    assert_norm (Some? (pstore_lookup 0 zsr));
    introduce law_resume_matches_continuation_nom xboundary ref_ops xpl fone xg
              ==> False
    with (law_rm_nom_unfold xboundary ref_ops xpl fone xg ();
          lemma_le_refuted zlhs zrhs zsl zsr 1 0)

(**
 * **THE ANCHORED HALF OF `law_assoc_nom` IS FALSE OF `ref_ops`, AND THE
 * NEGATION IS PROVED** -- hence so is the conjunction.
 *
 * The two `bindScope`s on the left allocate, but that is NOT what fails: the
 * entries they add are named by no key the world speaks for and `psrel` ignores
 * them. What fails is the same site frame as everywhere else.
 *)
let guard_ref_ops_refutes_assoc_nom ()
  : Lemma (~(law_assoc_nom xboundary ref_ops xpl xc fone
                           (PVar #fv #fcl) (PVar #fv #fcl)))
  = guard_ace_runs ();
    lemma_pnconverges_at flook xapply acf_l 40 [] (PCtxKey 0) asl;
    lemma_pnconverges_at flook xapply acf_r 40 [] (PCtxKey 0) asr;
    assert_norm (Some? (pstore_lookup 0 asl));
    assert_norm (Some? (pstore_lookup 0 asr));
    introduce law_assoc_nom xboundary ref_ops xpl xc fone
                            (PVar #fv #fcl) (PVar #fv #fcl) ==> False
    with (law_ac_nom_unfold xboundary ref_ops xpl xc fone
                            (PVar #fv #fcl) (PVar #fv #fcl) ();
          lemma_le_refuted alhs arhs asl asr 0 0)

(* ------------------------------------------------------------------ *)
(*  THE ALGEBRAIC HALF, REFUTED -- BY A STRICTLY STRONGER INTERPRETER  *)
(*                                                                     *)
(*  The four refutations above use an interpreter that only APPLIES     *)
(*  the continuation it is handed, inside a scope of its own, which is  *)
(*  what an ordinary handler does.  The algebraic half is NOT refuted   *)
(*  by any such interpreter in this file, and the reason is in          *)
(*  `guard_align_bracketing`'s neighbourhood: the two bracketings put   *)
(*  DIFFERENT NUMBERS OF `PBindF` FRAMES on the stack, and a `PBindF`   *)
(*  is transparent to a value and is consumed before any boundary       *)
(*  beneath it -- so the difference never reaches a residual.           *)
(*                                                                     *)
(*  It does reach the CAPTURED SEGMENT, and the interpreter below reads *)
(*  that segment's length.  THAT IS A STRONGER CAPABILITY and it is     *)
(*  named as such: `papply_t` is an arbitrary F* function, so an        *)
(*  interpreter may inspect the continuation as a term, where a shipped *)
(*  FFI closure receives a function and can only call it.  The          *)
(*  refutation below is therefore SOUND AGAINST THE LAW AS STATED and   *)
(*  says less about the design than the other four do.  Which of the    *)
(*  two readings `papply_t` is meant to have is a question about the    *)
(*  statement, and it is reported rather than decided here.             *)
(* ------------------------------------------------------------------ *)

(** Related computations have the same head constructor at `PSplice`. PROVED, at
    index 1, where every mismatched pair is `False`. *)
let lemma_pcrel_splice_shape (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (c1 c2: pcomp v cl)
  : Lemma (requires pcrel r w c1 c2) (ensures PSplice? c1 == PSplice? c2)
  = assert (pcomp_rel r 1 w c1 c2)

let xklen (#v #cl: Type) (c: pcomp v cl) : nat
  = match c with
    | PSplice fs _ -> length fs
    | _ -> 0

let lemma_xklen_rel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld) (c1 c2: pcomp v cl)
  : Lemma (requires pcrel r w c1 c2) (ensures xklen c1 == xklen c2)
  = lemma_pcrel_splice_shape r w c1 c2;
    match c1, c2 with
    | PSplice fs1 b1, PSplice fs2 b2 ->
      lemma_pcrel_splice_inv r w fs1 fs2 b1 b2;
      lemma_pkrel_length r w fs1 fs2
    | _, _ -> ()

(** **The measuring interpreter.** It reads the LENGTH of the segment its
    continuation would splice back. Equivariant -- related continuations splice
    related segments, and related segments have equal length -- and that is the
    whole of the point: equivariance does not stop an interpreter from seeing
    how many frames it was handed. *)
let xapply2 : papply_t fv fcl = fun _ _ kk -> PVar (PV (FI (xklen (kk (fpv FU)))))

let lemma_xapply2_equivariant () : Lemma (papply_equivariant fcl_rel xapply2)
  = introduce forall (w: pworld) (c1 c2: fcl) (p1 p2: list (pval fv))
                     (kk1 kk2: pval fv -> pcomp fv fcl).
      (pwf_world w /\ pclrel fcl_rel w c1 c2 /\ pvals_rel w p1 p2 /\
       pfn_rel_at fcl_rel w kk1 kk2 ==>
       pcrel fcl_rel w (xapply2 c1 p1 kk1) (xapply2 c2 p2 kk2))
    with (introduce _ ==> _
          with begin
            lemma_pwext_refl w;
            assert (pval_rel #fv w (fpv FU) (fpv FU));
            assert (pcrel fcl_rel w (kk1 (fpv FU)) (kk2 (fpv FU)));
            lemma_xklen_rel fcl_rel w (kk1 (fpv FU)) (kk2 (fpv FU));
            lemma_pcrel_var fcl_rel w (PV (FI (xklen (kk1 (fpv FU)))))
                                      (PV (FI (xklen (kk2 (fpv FU)))))
          end)

let x2boundary : pboundary fv fcl = {
  b_rel = fcl_rel;
  b_lk = flook;
  b_apply = xapply2;
  b_mono = lemma_fcl_rel_mono ();
  b_down = lemma_fcl_rel_down ();
  b_lookup = lemma_flook_equivariant ();
  b_apply_eq = lemma_xapply2_equivariant ();
}

(** A stored context whose `post` PERFORMS. Nothing about it is exotic: the two
    bracketings differ only in how many `PBindF` frames stand between `post`'s
    computation and the prompt beneath, and a `post` that never performs never
    puts one there. *)
let xpost : pval fv -> pcomp fv fcl = fun _ -> PPerform "Echo" "op" []
let xsto : pstore fv fcl = [(0, PCtxRequests (fpv FU) [PBoundaryF] xpost)]
let xamb : pstack fv fcl = [PPromptF xltbl None PFamily]

let lemma_xltbl_selfrel (n: nat) (w: pworld)
  : Lemma (ptable_rel fcl_rel n w xltbl xltbl)
  = introduce forall (eff op: string).
      (match lookup_handler xltbl.hs eff op, lookup_handler xltbl.hs eff op with
       | None, None -> True
       | Some f1, Some f2 -> f1.kind == f2.kind /\ fcl_rel n w f1.body f2.body
       | _, _ -> False)
    with (lookup_handler_mk_handlers #fcl (fun _ -> KFast) [] eff op;
          assert (lookup_handler xltbl.hs eff op == None))

let lemma_xamb_equivariant (w: pworld) : Lemma (pkrel fcl_rel w xamb xamb)
  = introduce forall (n: nat). ptable_rel fcl_rel n w xltbl xltbl
    with lemma_xltbl_selfrel n w;
    lemma_pfrel_prompt #fv #fcl fcl_rel w xltbl xltbl None None PFamily;
    lemma_pkrel_nil #fv #fcl fcl_rel w;
    lemma_pkrel_cons fcl_rel w (PPromptF xltbl None PFamily)
                               (PPromptF xltbl None PFamily)
                               ([] <: pstack fv fcl) ([] <: pstack fv fcl)

let lemma_xpost_selfrel (w: pworld) : Lemma (pfn_rel_at fcl_rel w xpost xpost)
  = introduce forall (w': pworld) (y1 y2: pval fv).
      (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
       pcrel fcl_rel w' (xpost y1) (xpost y2))
    with (introduce _ ==> _
          with introduce forall (n: nat).
                   pcomp_rel #fv #fcl fcl_rel n w' (PPerform "Echo" "op" [])
                                                   (PPerform "Echo" "op" [])
               with ())

let lemma_xsto_entry_selfrel (w: pworld)
  : Lemma (pxrel fcl_rel w (PCtxRequests (fpv FU) [PBoundaryF] xpost)
                           (PCtxRequests (fpv FU) [PBoundaryF] xpost))
  = introduce forall (n: nat).
      pframes_rel #fv #fcl fcl_rel n w [PBoundaryF] [PBoundaryF]
    with ();
    lemma_xpost_selfrel w;
    lemma_pxrel_requests fcl_rel w (fpv FU) (fpv FU)
                         [PBoundaryF] [PBoundaryF] xpost xpost

let guard_bce_config_ok ()
  : Lemma (pequivariant_k_at fcl_rel (panchor xsto) xamb /\
           pstore_equivariant_at fcl_rel xsto /\ psfresh xsto 1 /\
           x2boundary.b_rel == fcl_rel /\ x2boundary.b_lk == flook /\
           x2boundary.b_apply == xapply2)
  = introduce forall (w: pworld). pkrel fcl_rel w xamb xamb
    with lemma_xamb_equivariant w;
    introduce forall (w: pworld).
      pxrel fcl_rel w (PCtxRequests (fpv FU) [PBoundaryF] xpost)
                      (PCtxRequests (fpv FU) [PBoundaryF] xpost)
    with lemma_xsto_entry_selfrel w;
    assert_norm (x2boundary.b_rel == fcl_rel);
    assert_norm (x2boundary.b_lk == flook);
    assert_norm (x2boundary.b_apply == xapply2)

let blhs : pcomp fv fcl =
  pbind (ref_ops.o_extend_ctx xpl (PCtxKey 0) (PVar #fv #fcl))
        (fun cy -> ref_ops.o_extend xpl cy (PVar #fv #fcl))
let brhs : pcomp fv fcl =
  ref_ops.o_extend xpl (PCtxKey 0) (fun z -> pbind (PVar #fv #fcl z) (PVar #fv #fcl))
let bcf_l : pconf fv fcl = { st = PStep blhs xamb; store = xsto; next = 1 }
let bcf_r : pconf fv fcl = { st = PStep brhs xamb; store = xsto; next = 1 }
let bsr : pstore fv fcl = (fst (prun flook xapply2 40 bcf_r)).store
let bsl : pstore fv fcl = (fst (prun flook xapply2 40 bcf_l)).store

(** **THE TWO BRACKETINGS ARE COUNTED, AND THEY DIFFER BY ONE FRAME.** PROVED by
    running the machine: four frames on the left, three on the right. *)
let guard_bce_runs ()
  : Lemma ((fst (prun flook xapply2 40 bcf_l)).st == PDone (PV (FI 4)) /\
           snd (prun flook xapply2 40 bcf_l) == ([] <: list string) /\
           (fst (prun flook xapply2 40 bcf_r)).st == PDone (PV (FI 3)) /\
           snd (prun flook xapply2 40 bcf_r) == ([] <: list string))
  = assert_norm ((fst (prun flook xapply2 40 bcf_l)).st == PDone (PV (FI 4)));
    assert_norm (snd (prun flook xapply2 40 bcf_l) == ([] <: list string));
    assert_norm ((fst (prun flook xapply2 40 bcf_r)).st == PDone (PV (FI 3)));
    assert_norm (snd (prun flook xapply2 40 bcf_r) == ([] <: list string))

let pval_rel_pv_unfold (#v: Type) (w: pworld) (a b: v)
                       (h: squash (pval_rel #v w (PV a) (PV b)))
  : squash (a == b)
  = h

let law_aa_nom_unfold (#v #cl: Type) (b: pboundary v cl) (ops: ctx_ops v cl)
    (pl: plan v cl) (c: pcomp v cl) (cxv: pval v) (g hf: pval v -> pcomp v cl)
    (hh: squash (law_assoc_nom b ops pl c cxv g hf))
  : squash (pnobs_tr_le b
              (pbind (ops.o_extend_ctx pl cxv g) (fun cy -> ops.o_extend pl cy hf))
              (ops.o_extend pl cxv (fun x -> pbind (g x) hf)))
  = hh

let lemma_bce_no_world (w: pworld) (x2: pval fv) (s2': pstore fv fcl)
  : Lemma (requires pnconverges flook xapply2 bcf_r ([] <: list string) x2 s2' /\
                    pval_rel w (PV (FI 4)) x2)
          (ensures False)
  = guard_bce_runs ();
    lemma_pnconverges_at flook xapply2 bcf_r 40 [] (PV (FI 3)) bsr;
    lemma_pnconverges_unique flook xapply2 bcf_r [] [] x2 (PV (FI 3)) s2' bsr;
    pval_rel_pv_unfold #fv w (FI 4) (FI 3) ()

(**
 * **THE ALGEBRAIC HALF OF `law_assoc_nom` IS FALSE OF `ref_ops`, AND THE
 * NEGATION IS PROVED** -- at `x2boundary`, whose interpreter MEASURES the
 * segment it is handed.
 *
 * The two sides answer with two PAYLOADS, `PV (FI 4)` and `PV (FI 3)`, and
 * `pval_rel` demands payloads be EQUAL -- so no world enters the argument at
 * all. That is worth saying plainly: this failure has nothing to do with names,
 * with allocation or with the store. It is the two bracketings of one bind
 * chain putting two frames on the stack where the other puts one.
 *
 * **AND IT IS A WEAKER RESULT THAN THE OTHER FOUR.** The interpreter here reads
 * the continuation as a TERM. The other four use one that only applies it. See
 * the block comment above for why the difference matters and what it leaves
 * open.
 *)
let guard_ref_ops_refutes_assoc_algebraic_nom ()
  : Lemma (~(law_assoc_nom x2boundary ref_ops xpl (PVar fone) (PCtxKey 0)
                           (PVar #fv #fcl) (PVar #fv #fcl)))
  = guard_bce_runs ();
    guard_bce_config_ok ();
    lemma_pnconverges_at flook xapply2 bcf_l 40 [] (PV (FI 4)) bsl;
    lemma_pnconverges_at flook xapply2 bcf_r 40 [] (PV (FI 3)) bsr;
    introduce law_assoc_nom x2boundary ref_ops xpl (PVar fone) (PCtxKey 0)
                            (PVar #fv #fcl) (PVar #fv #fcl) ==> False
    with begin
      law_aa_nom_unfold x2boundary ref_ops xpl (PVar fone) (PCtxKey 0)
                        (PVar #fv #fcl) (PVar #fv #fcl) ();
      pnobs_tr_le_unfold x2boundary blhs brhs ();
      assert (pnconverges x2boundary.b_lk x2boundary.b_apply
                ({ st = PStep blhs xamb; store = xsto; next = 1 })
                ([] <: list string) (PV (FI 4)) bsl);
      eliminate exists (x2: pval fv) (s2': pstore fv fcl) (w: pworld).
          (pnconverges flook xapply2 bcf_r ([] <: list string) x2 s2' /\
           pwf_world w /\ pwext w (panchor xsto) /\
           pval_rel w (PV (FI 4)) x2 /\ psrel fcl_rel w bsl s2')
      with lemma_bce_no_world w x2 s2'
    end

(* ================================================================== *)
(*  B2b.3 IN TWO CHECKED STATEMENTS                                    *)
(* ================================================================== *)

(**
 * **JUDGEMENT POINTS 1 AND 2, IN ONE CHECKED STATEMENT.** PROVED, at an
 * arbitrary plan, inner computation, value, extension functions, ambient stack,
 * store, counter, clause relation and world.
 *
 * The first three conjuncts are the prefixes: every side of every proposition
 * reaches a named configuration in a fixed number of transitions, computed with
 * everything symbolic. The last four are the obstruction: the configurations so
 * reached are NOT related, at any world, at any plan.
 *
 * No conjunct relates two sides' transition counts, and none mentions a
 * transition count outside a `prun`.
 *)
let guard_nom_b2b3_prefixes (#v #cl: Type) (lk: plookup_t cl) (apply: papply_t v cl)
    (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (c: pcomp v cl) (x: pval v) (f g h: pval v -> pcomp v cl)
    (amb: pstack v cl) (sto sto1 sto2: pstore v cl) (n0 m1 m2: nat)
    (m: weave_mode) (resp: pval v -> pcomp v cl)
  : Lemma (
      // JUDGEMENT POINT 1 -- the prefixes, in general form
      prun lk apply 2 ({ st = PStep (pbind (ref_ops.o_enter_ctx pl c) f) amb;
                         store = sto; next = n0 })
        == ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                           @ (PScopeF :: PBindF f :: amb)));
              store = sto; next = n0 }, ([] <: list string)) /\
      prun lk apply 1 ({ st = PStep (ref_ops.o_enter pl c) amb;
                         store = sto; next = n0 })
        == ({ st = PStep c (plan_enter_frames pl @ amb);
              store = sto; next = n0 }, ([] <: list string)) /\
      prun lk apply 9
        ({ st = PStep (pbind (ref_ops.o_enter_ctx pl (PVar x))
                             (fun cx -> ref_ops.o_extend pl cx g)) amb;
           store = sto; next = n0 })
        == ({ st = PStep (g x) (plan_protocol_frames pl
                                @ (PModeF MExtend (presp0 g) :: amb));
              store = (n0, PCtxRequests x (PBoundaryF :: plan_protocol_frames pl)
                                        (PVar #v #cl)) :: sto;
              next = n0 + 1 }, ([] <: list string)) /\
      // JUDGEMENT POINT 2 -- and the theorem cannot be started there
      ~(pcfrel r w ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                                   @ (PScopeF :: PBindF f :: amb)));
                      store = sto1; next = m1 })
                   ({ st = PStep c (plan_enter_frames pl @ amb);
                      store = sto2; next = m2 })) /\
      ~(pcfrel r w ({ st = PStep c (PBoundaryF :: (plan_protocol_frames pl
                                                   @ (PScopeF :: PBindF f :: amb)));
                      store = sto1; next = m1 })
                   ({ st = PStep c (PBindF g :: PBindF h
                                    :: (plan_enter_frames pl @ amb));
                      store = sto2; next = m2 })) /\
      ~(pcfrel r w ({ st = PStep c (plan_protocol_frames pl
                                    @ (PModeF m resp :: amb));
                      store = sto1; next = m1 })
                   ({ st = PStep c (plan_enter_frames pl @ amb);
                      store = sto2; next = m2 })) /\
      ~(pcfrel r w ({ st = PStep c (plan_protocol_frames pl
                                    @ (PModeF m resp :: amb));
                      store = sto1; next = m1 })
                   ({ st = PStep c (plan_resume_frames pl @ amb);
                      store = sto2; next = m2 })))
  = lemma_prefix_produce lk apply pl c f amb sto n0;
    lemma_prefix_enter lk apply pl c amb sto n0;
    lemma_prefix_li_l lk apply pl x g amb sto n0;
    guard_align_ri_post_unrelated r w pl c f amb sto1 sto2 m1 m2;
    guard_align_ac_post_unrelated r w pl c f g h amb sto1 sto2 m1 m2;
    guard_align_li_post_unrelated r w pl c m resp amb sto1 sto2 m1 m2;
    guard_align_rm_post_unrelated r w pl c m resp amb sto1 sto2 m1 m2

(**
 * **THE VERDICT ON THE SIX PROPOSITIONS, IN ONE CHECKED STATEMENT.** PROVED.
 *
 * All six are FALSE of `ref_ops` under the REPAIRED observation, and every
 * negation below is a proof and not an obligation left undone. Two of the six
 * are the same proposition at `ref_ops`, which is the third conjunct.
 *)
let guard_nom_b2b3_verdict ()
  : Lemma (
      ~(law_left_identity_nom xboundary ref_ops xpl fone xg) /\
      ~(law_right_identity_nom xboundary ref_ops xpl xc) /\
      ~(law_transparent_agrees_nom xboundary ref_ops xpl xc) /\
      ~(law_resume_matches_continuation_nom xboundary ref_ops xpl fone xg) /\
      ~(law_assoc_nom xboundary ref_ops xpl xc fone
                      (PVar #fv #fcl) (PVar #fv #fcl)) /\
      ~(law_assoc_nom x2boundary ref_ops xpl (PVar fone) (PCtxKey 0)
                      (PVar #fv #fcl) (PVar #fv #fcl)))
  = guard_ref_ops_refutes_left_identity_nom ();
    guard_ref_ops_refutes_right_identity_nom ();
    guard_ref_ops_refutes_transparent_agrees_nom ();
    guard_ref_ops_refutes_resume_nom ();
    guard_ref_ops_refutes_assoc_nom ();
    guard_ref_ops_refutes_assoc_algebraic_nom ()

(* ================================================================== *)
(*  B2b.3 LEDGER -- WHAT IS ESTABLISHED, AND WHAT IS NOT               *)
(*                                                                     *)
(*  ESTABLISHED, EACH BY A CHECKED PROOF                                *)
(*                                                                     *)
(*   - JUDGEMENT POINT 1 IS ANSWERED YES, FOR ALL SIX PROPOSITIONS.     *)
(*     Each side of each has a finite prefix computed in GENERAL FORM   *)
(*     -- plan, inner computation, value, extension functions, ambient  *)
(*     stack, store and counter all variables -- and the two prefixes   *)
(*     land on the SAME NODE.  Production is two transitions and        *)
(*     entering is one (`lemma_prefix_produce`, `lemma_prefix_enter`,   *)
(*     `lemma_prefix_enter_bind2`, `lemma_prefix_resume_rhs`); left     *)
(*     identity and resumption are nine on the left and one on the      *)
(*     right (`lemma_prefix_li_l`, `lemma_prefix_rm_l`); the algebraic  *)
(*     half is four against one where its handle resolves and two       *)
(*     against one where it does not (`lemma_prefix_aa_l`,              *)
(*     `lemma_prefix_aa_r`, and the two stuck lemmas).  The three stack *)
(*     searches are discharged by INDUCTION ON THE PLAN, not by         *)
(*     normalisation (`lemma_plan_protocol_frames_flat`,               *)
(*     `lemma_pcut_scope_through`, and `lemma_find_mode_through` which  *)
(*     was already there);                                              *)
(*                                                                     *)
(*   - JUDGEMENT POINT 2 IS ANSWERED NO, AND THE REASON IS STRUCTURAL.  *)
(*     `pframes_rel` matches a stack cons for cons, and the two         *)
(*     post-prefix stacks have DIFFERENT LENGTHS at every plan and      *)
(*     every ambient stack -- because `plan_protocol_frames` keeps a    *)
(*     `PSiteF` where `plan_enter_frames` drops the item, and because   *)
(*     the residual protocol's boundary, floor and `PModeF` marker have *)
(*     no counterpart on the anchored side                              *)
(*     (`guard_align_produce_vs_enter`,                                 *)
(*     `guard_align_produce_vs_enter_bind2`,                            *)
(*     `guard_align_marker_vs_enter`, `guard_align_marker_vs_resume`,   *)
(*     and the four configuration-level corollaries).  At the RESUME    *)
(*     projection the two segments have EQUAL length, so the resumption *)
(*     law's two sides differ by the marker and by nothing else;        *)
(*                                                                     *)
(*   - THE ALGEBRAIC HALF'S OBSTRUCTION IS A DIFFERENT ONE and is kept  *)
(*     apart.  There the two post-prefix STACKS are identical and the   *)
(*     two computations are drives of the same residual; what differs   *)
(*     is the marker's responder, which carries the two BRACKETINGS of  *)
(*     one bind chain.  Those are not related terms, at any world, for  *)
(*     any `post`, `g` and `h` (`guard_align_bracketing`, resting on    *)
(*     `lemma_no_op_self`: a computation is never related to a bind of  *)
(*     itself, because a term is finite);                               *)
(*                                                                     *)
(*   - JUDGEMENT POINT 3 IS REACHED ONLY WHERE POINT 2 SUCCEEDS, and    *)
(*     there it closes.  `lemma_obs_from_common` composes two prefixes  *)
(*     of INDEPENDENT lengths with the fundamental theorem at ONE fuel  *)
(*     on the common pair; the world is the theorem's and is written    *)
(*     nowhere.  It discharges the algebraic half's obligation, IN BOTH *)
(*     DIRECTIONS, at every configuration whose named handle is absent  *)
(*     or holds no requests (`lemma_aa_obs_absent`,                     *)
(*     `lemma_aa_obs_absent_rev`, `lemma_aa_obs_done`,                  *)
(*     `lemma_aa_obs_done_rev`).  That is an obligation discharged at   *)
(*     named configurations and is NOT the law;                         *)
(*                                                                     *)
(*   - TWO OF THE SIX PROPOSITIONS ARE ONE.  At `ref_ops`,             *)
(*     `law_transparent_agrees_nom` and `law_right_identity_nom` are    *)
(*     the same proposition, and `law_left_identity_nom` at `PVar` is   *)
(*     `law_right_identity_nom` at a value                              *)
(*     (`guard_align_transparent_is_right_identity`,                    *)
(*     `guard_align_left_identity_at_pure`).  Equalities of `prop`s,    *)
(*     not implications, and they say nothing about any other           *)
(*     `ctx_ops`;                                                       *)
(*                                                                     *)
(*   - ALL SIX PROPOSITIONS ARE FALSE OF `ref_ops` UNDER THE REPAIRED   *)
(*     OBSERVATION, and all six negations are PROVED                    *)
(*     (`guard_nom_b2b3_verdict`).                                      *)
(*                                                                     *)
(*  WHAT THE COUNTEREXAMPLES ARE, AND WHAT THEY ARE NOT                 *)
(*                                                                     *)
(*   - THEY ARE NOT ABOUT NAMES, AND NOT ABOUT THE COUNTER.  Four of    *)
(*     the six stand at the EMPTY store, the EMPTY ambient stack and    *)
(*     counter ZERO; two of those four answer with the SAME handle on   *)
(*     both sides, so the world is forced rather than chosen, and the   *)
(*     sixth answers with two PAYLOADS and never mentions a world.      *)
(*     The repair B2b.1 made is doing its work in every one of them:    *)
(*     the extra entries the left side allocates are ignored as garbage *)
(*     exactly as designed.  What no world can do is relate two         *)
(*     CONTEXTS whose residuals differ in length, and that is what      *)
(*     happens;                                                         *)
(*                                                                     *)
(*   - THE MECHANISM IS THE RESIDUAL PROTOCOL LEAVING ITS MARKER.  A    *)
(*     `PSiteF` under a live `MExtend` marker is skipped and under      *)
(*     `MResume` fires, which is what makes `plan_protocol_frames` both *)
(*     of the other two projections -- and it is true only while the    *)
(*     marker stays BELOW the site frame.  Dispatch captures the        *)
(*     segment above the matching prompt; a clause that resumes that    *)
(*     segment INSIDE A SCOPE OF ITS OWN puts the captured `PSiteF`     *)
(*     above a floor with no marker in scope, and it YIELDS there,      *)
(*     storing a residual the other side has no counterpart for.        *)
(*     `xapply` does exactly that and NOTHING ELSE: it builds one       *)
(*     `PEnterCtx` and applies the continuation it was handed, which is *)
(*     what an ordinary handler does.  It is PROVED equivariant         *)
(*     (`lemma_xapply_equivariant`), so the boundary's four conditions  *)
(*     are met and none of them is weakened;                            *)
(*                                                                     *)
(*   - THE ALGEBRAIC HALF'S COUNTEREXAMPLE IS WEAKER AND IS LABELLED    *)
(*     AS SUCH.  Its interpreter, `xapply2`, READS THE LENGTH of the    *)
(*     segment it is handed, which is a capability `papply_t` grants    *)
(*     because it is an arbitrary F* function and which a shipped FFI   *)
(*     closure -- given a continuation it can only CALL -- does not     *)
(*     have.  It is equivariant (`lemma_xapply2_equivariant`) and the   *)
(*     refutation is sound against the law AS STATED.  NO INTERPRETER   *)
(*     IN THIS FILE THAT ONLY APPLIES ITS CONTINUATION REFUTES THE      *)
(*     ALGEBRAIC HALF, and it is NOT established here that none can:    *)
(*     a `PBindF` is transparent to a value and is consumed before any  *)
(*     boundary beneath it, so the bracketing difference does not reach *)
(*     a residual by the route the other four take -- that is an        *)
(*     observation about the four counterexamples and not a theorem.    *)
(*                                                                     *)
(*  NOT ESTABLISHED, AND NAMED                                          *)
(*                                                                     *)
(*   - THAT THE FIVE LAWS ARE FALSE FOR ALL `ops`, or for all plans,    *)
(*     or at every configuration.  Each refutation is ONE instance.     *)
(*     What is general is the OBSTRUCTION (judgement point 2), which is *)
(*     proved at every plan and every world;                            *)
(*                                                                     *)
(*   - THAT THE ALGEBRAIC HALF IS FALSE UNDER AN INTERPRETER THAT ONLY  *)
(*     APPLIES ITS CONTINUATION.  Open, in both directions;             *)
(*                                                                     *)
(*   - ANY AMENDMENT TO ANY LAW.  No statement above `guard_nom_laws_`  *)
(*     `are_statable` is edited.  Three amendments are visible from     *)
(*     here and NONE is taken: restrict `papply_t` so an interpreter    *)
(*     may only APPLY the continuation it is given; require the two     *)
(*     sides' final stores to correspond only on handles the           *)
(*     PROGRAM can still name rather than on the world's whole domain;  *)
(*     or relate `plan_protocol_frames` to `plan_enter_frames` by an    *)
(*     erasure and state the laws up to it.  Each changes what the      *)
(*     laws CLAIM, which is a design decision and not a step in a       *)
(*     proof;                                                           *)
(*                                                                     *)
(*   - THAT THE OBSTRUCTION IS UNAVOIDABLE.  It is an obstruction to    *)
(*     the route this file has -- the fundamental theorem started at a  *)
(*     common configuration.  A bisimulation up to the residual         *)
(*     protocol's erasure would be a different route and nothing here   *)
(*     refutes it; what the counterexamples show is that such a         *)
(*     bisimulation would have to be FALSE at `xapply`, so the route    *)
(*     is closed for a reason and not merely unbuilt.                   *)
(*                                                                     *)
(*  WHAT DID NOT CHANGE                                                 *)
(*                                                                     *)
(*   - NO DEFINITION OF B2b.2 OR EARLIER WAS EDITED.  B2b.3 appends;    *)
(*     the two amendments it makes above are to COMMENTS, and each      *)
(*     records that a question the comment left open is now decided;    *)
(*   - `prun`, `pstep`, `pstep_tr`, `pconverges_tr`, `pobs_tr_le`,      *)
(*     `pnobs_tr_le` and `pnobs_tr_eq` are untouched, so every earlier  *)
(*     result means what it meant; production is still an               *)
(*     object-language transition, `presolve` is still given no stack,  *)
(*     `settles`, `PTokenF` and `pfind_token` are still absent, and     *)
(*     `lemma_reachable_residual_wf` still has no `requires`;           *)
(*   - NO `rlimit`, NO `#push-options`, NO `admit`, NO `assume` was     *)
(*     added.  B2b.3 adds none of the four, and the two `unfold`s it    *)
(*     introduces (`presp0`, `pcompose`) are abbreviations that         *)
(*     disappear at elaboration, which is what keeps a lambda the       *)
(*     machine builds and a lambda a statement writes the SAME TERM;    *)
(*   - the counter is still mentioned nowhere in the observation, and   *)
(*     no statement in B2b.3 relates two sides' transition counts:      *)
(*     `lemma_obs_from_common` takes the two prefix lengths as          *)
(*     INDEPENDENT parameters and applies the theorem at one fuel to    *)
(*     the common pair.                                                 *)
(* ================================================================== *)

(* ================================================================== *)
(*  B2b.4 -- FEASIBILITY GATE: THE ADMINISTRATIVE MIDDLE LAYER         *)
(*                                                                     *)
(*  Everything below is ADDITIVE.  `pcrel`, `pframes_rel`,             *)
(*  `pnobs_tr_le` and every other definition above is untouched; the   *)
(*  new relation is BUILT OUT OF `pframe_rel` and `pframes_rel`        *)
(*  rather than replacing them, so the fundamental theorem still       *)
(*  means what it meant.                                               *)
(*                                                                     *)
(*  WHAT IS BEING TESTED.  Between the strong lockstep congruence the  *)
(*  fundamental theorem carries (`pcrel`) and the weak observation     *)
(*  the laws are stated over (`pnobs_tr_eq`) there is room for ONE     *)
(*  more relation, whose job is to absorb the transitions the machine  *)
(*  takes for its own bookkeeping.  This section states such a         *)
(*  relation and checks five things about it.  IT DOES NOT PROVE       *)
(*  OBSERVATIONAL SOUNDNESS and it attempts NO LAW.                    *)
(*                                                                     *)
(*  WHAT MAKES A FRAME ADMINISTRATIVE, read off the value rules of     *)
(*  `pstep` and from nowhere else:                                     *)
(*                                                                     *)
(*   - `PSiteF g` under a live `MExtend` marker steps to `PVar value`  *)
(*     under the rest -- it is NOTHING;                                *)
(*   - `PSiteF g` under a live `MResume` marker steps to `g value`     *)
(*     under the rest -- it is `PBindF g`.                             *)
(*                                                                     *)
(*  Those two lines are the whole of the erasure, and the mode is      *)
(*  what decides between them, so the relation is MODE-INDEXED and     *)
(*  the two modes cannot be collapsed: at `MExtend` the site frame is  *)
(*  matched against NO frame at all, at `MResume` against a `PBindF`.  *)
(*                                                                     *)
(*  WHAT IS *NOT* ADMINISTRATIVE, and each is refused rather than      *)
(*  argued away:                                                       *)
(*                                                                     *)
(*   - `PScopeF` ALLOCATES.  A value reaching a floor stores a         *)
(*     `PCtxDone` and goes on with a handle.  It is never erased and   *)
(*     it BLOCKS the mode search, which is why `padm_marked` stops at  *)
(*     one;                                                            *)
(*   - `PBoundaryF` hands the value to the marker's responder, or      *)
(*     YIELDS if there is none.  It is matched only against another    *)
(*     `PBoundaryF`, and only when both sides reach THE SAME marker;   *)
(*   - `PModeF m resp` CARRIES A RESPONDER.  It is deleted only in     *)
(*     the regime where nothing above it can reach the responder --    *)
(*     the relation earns that by structure (`sh = false` forbids      *)
(*     `PBoundaryF` outright, and a `PSiteF` reads the MODE and never  *)
(*     the responder), not by fiat.                                    *)
(* ================================================================== *)

(** **A frame a value passes without consulting anything else on the stack**,
    and which `pfind_mode` walks straight through. `PScopeF` is absent because it
    allocates and blocks the search; `PBoundaryF`, `PSiteF` and `PModeF` are
    absent because each of them is exactly what the protocol is made of. *)
let padm_inert (#v #cl: Type) (f: pframe v cl) : bool
  = match f with
    | PBindF _ -> true
    | PParamF _ _ -> true
    | PPromptF _ _ _ -> true
    | _ -> false

(**
 * **The stack reaches a live marker for `m`.** This is `pfind_mode`'s walk,
 * written as a boolean over the mode alone, and it is the SIDE CONDITION that
 * makes erasing a `PSiteF` sound: a site frame is `PBindF`-or-nothing only when
 * the search beneath it actually answers, and answers with `m`.
 *)
let rec padm_marked (#v #cl: Type) (m: weave_mode) (k: pstack v cl)
  : Tot bool (decreases k)
  = match k with
    | [] -> false
    | PModeF m1 _ :: _ -> m1 = m
    | PScopeF :: _ -> false
    | PBoundaryF :: t -> padm_marked m t
    | PSiteF _ :: t -> padm_marked m t
    | f :: t -> padm_inert f && padm_marked m t

(** **`padm_marked` is `pfind_mode`, answered.** PROVED, by induction; the two
    walks have the same clauses in the same order. *)
let rec lemma_padm_marked_finds (#v #cl: Type) (m: weave_mode) (k: pstack v cl)
  : Lemma (requires padm_marked m k)
          (ensures pmode_of (pfind_mode k) == Some m)
          (decreases k)
  = match k with
    | PModeF _ _ :: _ -> ()
    | PBoundaryF :: t -> lemma_padm_marked_finds m t
    | PSiteF _ :: t -> lemma_padm_marked_finds m t
    | PScopeF :: _ -> ()
    | [] -> ()
    | _ :: t -> lemma_padm_marked_finds m t

(* ------------------------------------------------------------------ *)
(*  CONDITION 1: THE RELATION                                          *)
(* ------------------------------------------------------------------ *)

(**
 * **THE MODE-INDEXED ADMINISTRATIVE STACK RELATION.**
 *
 * `m` is the mode in scope. `sh` says which marker regime the two sides are in:
 *
 *   - `sh = false` -- the LEFT carries the consumer's marker and the RIGHT has
 *     none. This is the regime the two projections differ in: a residual driven
 *     by a consumer against an independent description that never had a consumer.
 *     `PBoundaryF` is REFUSED here, because a boundary on the left would reach
 *     the marker and a boundary on the right would reach whatever is beneath the
 *     ambient stack, and those are not the same responder.
 *
 *   - `sh = true` -- BOTH sides carry the same marker, which is what
 *     `ctx_drive` produces when the same consumer drives two residuals. Here a
 *     `PBoundaryF` is matched against a `PBoundaryF` and the two responders are
 *     related because the two markers are.
 *
 * The clauses, in order:
 *
 *   - `[]` against `[]`. Nothing left to say.
 *   - a marker on the left. Either deleted (`sh = false`, and the rest of the
 *     left must be `pframes_rel` to the whole of the right) or shared
 *     (`sh = true`, and the two markers must be related frames).
 *   - a `PSiteF` on the left, WITH the mode search beneath it answering `m`.
 *     Under `MExtend` it matches nothing; under `MResume` it matches a `PBindF`
 *     carrying a related function.
 *   - a `PBoundaryF`, only in the shared regime and only against a `PBoundaryF`.
 *   - a `PBindF`, either frame for frame OR -- and this is the clause the
 *     algebraic half needs -- TWO of them against ONE carrying their
 *     composition. `PBindF f :: PBindF g` and `PBindF (fun x -> f x >>= g)` take
 *     a value to the same configuration, the second one transition later.
 *   - any other inert frame, frame for frame.
 *
 * Everything else -- a `PScopeF` anywhere, a `PBoundaryF` in the deleted
 * regime, a `PSiteF` with no marker beneath it -- is `False`, and `False` is the
 * right answer for each: those are the frames the machine does REAL work at.
 *)
let rec padm_stack (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode) (sh: bool)
                   (n: nat) (w: pworld) (k1 k2: pstack v cl)
  : GTot prop (decreases k1)
  = match k1 with
    | [] -> (match k2 with | [] -> True | _ -> False)
    | PModeF m1 resp1 :: t1 ->
      m1 == m /\
      (if sh
       then (match k2 with
             | PModeF m2 resp2 :: t2 ->
               m2 == m /\
               pframe_rel r n w (PModeF m1 resp1) (PModeF m2 resp2) /\
               pframes_rel r n w t1 t2
             | _ -> False)
       else pframes_rel r n w t1 k2)
    | PSiteF g1 :: t1 ->
      b2t (padm_marked m t1) /\
      (match m with
       | MExtend -> padm_stack r m sh n w t1 k2
       | MResume ->
         (match k2 with
          | PBindF g2 :: t2 ->
            pframe_rel r n w (PSiteF g1) (PSiteF g2) /\ padm_stack r m sh n w t1 t2
          | _ -> False))
    | PBoundaryF :: t1 ->
      b2t sh /\ b2t (padm_marked m t1) /\
      (match k2 with
       | PBoundaryF :: t2 -> padm_stack r m sh n w t1 t2
       | _ -> False)
    | PBindF f1 :: t1 ->
      (match k2 with
       | f2 :: t2 -> pframe_rel r n w (PBindF f1) f2 /\ padm_stack r m sh n w t1 t2
       | [] -> False)
      \/
      (match t1 with
       | PBindF g1 :: t1' ->
         (match k2 with
          | PBindF h2 :: t2 ->
            pframe_rel r n w (PBindF (fun x -> pbind (f1 x) g1)) (PBindF h2) /\
            padm_stack r m sh n w t1' t2
          | _ -> False)
       | _ -> False)
    | f1 :: t1 ->
      b2t (padm_inert f1) /\
      (match k2 with
       | f2 :: t2 -> pframe_rel r n w f1 f2 /\ padm_stack r m sh n w t1 t2
       | [] -> False)

(** The intersection of the approximants, exactly as `pkrel` is taken from
    `pframes_rel`. This is the relation the five conditions are about. *)
let padm (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode) (sh: bool) (w: pworld)
         (k1 k2: pstack v cl) : GTot prop
  = forall (n: nat). padm_stack r m sh n w k1 k2

(** **The administrative relation on COMPUTATIONS.** It is `pcrel` everywhere
    except at the three nodes that carry a stack or a body a residual can be
    reached through -- `PSplice`, which is what a captured continuation IS, and
    `PEnterCtx` and `PEmit`, which a clause interpreter wraps one around. *)
let rec padm_comp (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode) (sh: bool)
                  (w: pworld) (c1 c2: pcomp v cl)
  : GTot prop (decreases c1)
  = match c1 with
    | PSplice fs1 b1 ->
      (match c2 with
       | PSplice fs2 b2 -> padm r m sh w fs1 fs2 /\ padm_comp r m sh w b1 b2
       | _ -> False)
    | PEnterCtx pl1 b1 ->
      (match c2 with
       | PEnterCtx pl2 b2 -> pplrel r w pl1 pl2 /\ padm_comp r m sh w b1 b2
       | _ -> False)
    | PEmit e1 b1 ->
      (match c2 with
       | PEmit e2 b2 -> e1 == e2 /\ padm_comp r m sh w b1 b2
       | _ -> False)
    | _ -> pcrel r w c1 c2

let padm_fn_at (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode) (sh: bool)
               (w0: pworld) (f1 f2: pval v -> pcomp v cl) : GTot prop
  = forall (w: pworld) (y1 y2: pval v).
      pwf_world w /\ pwext w w0 /\ pval_rel w y1 y2 ==> padm_comp r m sh w (f1 y1) (f2 y2)

(** **The condition 4 asks about**: `papply_equivariant` with `pcrel` replaced by
    the administrative relation on both sides. An interpreter satisfies it when
    it cannot tell two administratively equal continuations apart. *)
let padm_apply_pres (#v #cl: Type) (r: pcl_rel_t cl) (apply: papply_t v cl)
  : GTot prop
  = forall (m: weave_mode) (sh: bool) (w: pworld) (c1 c2: cl)
           (p1 p2: list (pval v)) (kk1 kk2: pval v -> pcomp v cl).
      pwf_world w /\ pclrel r w c1 c2 /\ pvals_rel w p1 p2 /\
      padm_fn_at r m sh w kk1 kk2 ==>
      padm_comp r m sh w (apply c1 p1 kk1) (apply c2 p2 kk2)

let padm_apply_pres_inst (#v #cl: Type) (r: pcl_rel_t cl) (apply: papply_t v cl)
    (m: weave_mode) (sh: bool) (w: pworld) (c1 c2: cl) (p1 p2: list (pval v))
    (kk1 kk2: pval v -> pcomp v cl)
  : Lemma (requires padm_apply_pres r apply /\ pwf_world w /\ pclrel r w c1 c2 /\
                    pvals_rel w p1 p2 /\ padm_fn_at r m sh w kk1 kk2)
          (ensures padm_comp r m sh w (apply c1 p1 kk1) (apply c2 p2 kk2))
  = ()

(* ---- CONDITION 1: the two modes are genuinely different ----------- *)

(**
 * **`MExtend` AND `MResume` DO NOT COLLAPSE.** PROVED, at one two-frame stack
 * and its two candidate right-hand sides.
 *
 * The same left stack is related to the EMPTY stack at `MExtend` and to
 * `[PBindF PVar]` at `MResume`, and to neither at the other mode. So the mode
 * index is doing work: it is not a parameter the relation could be quantified
 * over and forgotten.
 *)
let guard_adm_modes_differ (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (resp: pval v -> pcomp v cl)
  : Lemma (padm r MExtend false w
             ([PSiteF (PVar #v #cl); PModeF MExtend resp] <: pstack v cl)
             ([] <: pstack v cl)
           /\
           ~(padm r MResume false w
               ([PSiteF (PVar #v #cl); PModeF MResume resp] <: pstack v cl)
               ([] <: pstack v cl))
           /\
           ~(padm r MExtend false w
               ([PSiteF (PVar #v #cl); PModeF MExtend resp] <: pstack v cl)
               ([PBindF (PVar #v #cl)] <: pstack v cl)))
  = introduce forall (n: nat).
        padm_stack r MExtend false n w
          ([PSiteF (PVar #v #cl); PModeF MExtend resp] <: pstack v cl)
          ([] <: pstack v cl)
    with begin
      assert (padm_marked MExtend ([PModeF MExtend resp] <: pstack v cl));
      assert (pframes_rel r n w ([] <: pstack v cl) ([] <: pstack v cl));
      assert (padm_stack r MExtend false n w
                ([PModeF MExtend resp] <: pstack v cl) ([] <: pstack v cl))
    end;
    introduce padm r MResume false w
                ([PSiteF (PVar #v #cl); PModeF MResume resp] <: pstack v cl)
                ([] <: pstack v cl) ==> False
    with assert (padm_stack r MResume false 1 w
                   ([PSiteF (PVar #v #cl); PModeF MResume resp] <: pstack v cl)
                   ([] <: pstack v cl));
    introduce padm r MExtend false w
                ([PSiteF (PVar #v #cl); PModeF MExtend resp] <: pstack v cl)
                ([PBindF (PVar #v #cl)] <: pstack v cl) ==> False
    with assert (padm_stack r MExtend false 1 w
                   ([PSiteF (PVar #v #cl); PModeF MExtend resp] <: pstack v cl)
                   ([PBindF (PVar #v #cl)] <: pstack v cl))

(** The `MResume` side of the same fact: there the site frame IS the bind frame,
    and the empty stack is refused. PROVED. *)
let guard_adm_resume_is_bind (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (resp: pval v -> pcomp v cl)
  : Lemma (padm r MResume false w
             ([PSiteF (PVar #v #cl); PModeF MResume resp] <: pstack v cl)
             ([PBindF (PVar #v #cl)] <: pstack v cl))
  = lemma_pfn_rel_at_pvar #v #cl r w;
    lemma_pfrel_site r w (PVar #v #cl) (PVar #v #cl);
    introduce forall (n: nat).
        padm_stack r MResume false n w
          ([PSiteF (PVar #v #cl); PModeF MResume resp] <: pstack v cl)
          ([PBindF (PVar #v #cl)] <: pstack v cl)
    with begin
      assert (padm_marked MResume ([PModeF MResume resp] <: pstack v cl));
      assert (pframe_rel r n w (PSiteF (PVar #v #cl)) (PSiteF (PVar #v #cl)));
      assert (pframes_rel r n w ([] <: pstack v cl) ([] <: pstack v cl));
      assert (padm_stack r MResume false n w
                ([PModeF MResume resp] <: pstack v cl) ([] <: pstack v cl))
    end

(* ------------------------------------------------------------------ *)
(*  CONDITION 2: THE FOUR MISMATCHES OF THE REDUX                      *)
(* ------------------------------------------------------------------ *)

(** The protocol projection is inert-or-site all the way down, so it never
    stops a mode search. PROVED, by induction on the plan's items. *)
let rec lemma_padm_marked_protocol (#v #cl: Type) (m: weave_mode)
    (ls: list (plan_item v cl)) (t: pstack v cl)
  : Lemma (requires padm_marked m t)
          (ensures padm_marked m (protocol_layer_frames ls @ t))
          (decreases ls)
  = match ls with
    | [] -> ()
    | _ :: rest -> lemma_padm_marked_protocol m rest t

(** And it never REACHES a marker either, if what is beneath it does not.
    PROVED, and this is what refuses the two production mismatches. *)
let rec lemma_padm_unmarked_protocol (#v #cl: Type) (m: weave_mode)
    (ls: list (plan_item v cl)) (t: pstack v cl)
  : Lemma (requires ~(b2t (padm_marked m t)))
          (ensures ~(b2t (padm_marked m (protocol_layer_frames ls @ t))))
          (decreases ls)
  = match ls with
    | [] -> ()
    | _ :: rest -> lemma_padm_unmarked_protocol m rest t

(**
 * **PROTOCOL AGAINST ENTER, UNDER `MExtend`: RELATED.** PROVED, by induction on
 * the plan's items.
 *
 * This is the length obstruction `lemma_plan_frames_lengths` measures, absorbed:
 * every `PIBind` the protocol projection keeps as a dormant `PSiteF` is matched
 * against NO frame at all on the enter side, because that is what the machine
 * does with it when the marker beneath says `MExtend`.
 *)
let rec lemma_padm_layers_extend (#v #cl: Type) (r: pcl_rel_t cl) (sh: bool)
    (n: nat) (w: pworld) (ls: list (plan_item v cl)) (t1 t2: pstack v cl)
  : Lemma (requires pitems_rel r n w ls ls /\ padm_marked MExtend t1 /\
                    padm_stack r MExtend sh n w t1 t2)
          (ensures padm_stack r MExtend sh n w
                     (protocol_layer_frames ls @ t1) (enter_layer_frames ls @ t2))
          (decreases ls)
  = match ls with
    | [] -> ()
    | i :: rest ->
      lemma_padm_layers_extend r sh n w rest t1 t2;
      lemma_padm_marked_protocol MExtend rest t1;
      (match i with
       | PIBind _ -> ()
       | PICell _ _ -> ()
       | PITransparent _ -> ()
       | PIReenter _ _ -> ())

(**
 * **PROTOCOL AGAINST RESUME, UNDER `MResume`: RELATED.** PROVED, by the same
 * induction. Here the two projections have the SAME LENGTH and the `PSiteF`
 * matches the `PBindF` it was recorded from, which is the other half of what
 * makes one projection stand for both.
 *)
let rec lemma_padm_layers_resume (#v #cl: Type) (r: pcl_rel_t cl) (sh: bool)
    (n: nat) (w: pworld) (ls: list (plan_item v cl)) (t1 t2: pstack v cl)
  : Lemma (requires pitems_rel r n w ls ls /\ padm_marked MResume t1 /\
                    padm_stack r MResume sh n w t1 t2)
          (ensures padm_stack r MResume sh n w
                     (protocol_layer_frames ls @ t1) (resume_layer_frames ls @ t2))
          (decreases ls)
  = match ls with
    | [] -> ()
    | i :: rest ->
      lemma_padm_layers_resume r sh n w rest t1 t2;
      lemma_padm_marked_protocol MResume rest t1;
      (match i with
       | PIBind _ -> ()
       | PICell _ _ -> ()
       | PITransparent _ -> ()
       | PIReenter _ _ -> ())

(**
 * **`guard_align_marker_vs_enter`'S TWO STACKS ARE ADMINISTRATIVELY RELATED.**
 * PROVED, at every plan self-related at every index, every responder and every
 * self-related ambient stack.
 *
 * This is the third of the redux's four mismatches, and it is the one the
 * middle layer exists for: the consumer's marker is deleted, the dormant site
 * frames vanish with it, and what is left on both sides is the enter projection
 * over the same ambient stack.
 *)
let lemma_padm_marker_vs_enter (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (resp: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (requires pplrel r w pl pl /\ pkrel r w amb amb)
          (ensures padm r MExtend false w
                     (plan_protocol_frames pl @ (PModeF MExtend resp :: amb))
                     (plan_enter_frames pl @ amb))
  = let ls = Plan?.layers pl in
    let ow = Plan?.owner pl in
    append_assoc (protocol_layer_frames ls) ([owner_frame ow] <: pstack v cl)
                 ((PModeF MExtend resp :: amb) <: pstack v cl);
    append_assoc (enter_layer_frames ls) ([owner_frame ow] <: pstack v cl) amb;
    introduce forall (n: nat).
        padm_stack r MExtend false n w
          (plan_protocol_frames pl @ (PModeF MExtend resp :: amb))
          (plan_enter_frames pl @ amb)
    with begin
      assert (pplan_rel r n w pl pl);
      lemma_padm_layers_extend r false n w ls
        ((owner_frame ow :: PModeF MExtend resp :: amb) <: pstack v cl)
        ((owner_frame ow :: amb) <: pstack v cl)
    end

(**
 * **`guard_align_marker_vs_resume`'S TWO STACKS ARE ADMINISTRATIVELY RELATED.**
 * PROVED, and this is the fourth mismatch. The two segments had equal length
 * already; what separated them was the marker, and the marker is what the
 * deleted regime deletes.
 *)
let lemma_padm_marker_vs_resume (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (resp: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (requires pplrel r w pl pl /\ pkrel r w amb amb)
          (ensures padm r MResume false w
                     (plan_protocol_frames pl @ (PModeF MResume resp :: amb))
                     (plan_resume_frames pl @ amb))
  = let ls = Plan?.layers pl in
    let ow = Plan?.owner pl in
    append_assoc (protocol_layer_frames ls) ([owner_frame ow] <: pstack v cl)
                 ((PModeF MResume resp :: amb) <: pstack v cl);
    append_assoc (resume_layer_frames ls) ([owner_frame ow] <: pstack v cl) amb;
    introduce forall (n: nat).
        padm_stack r MResume false n w
          (plan_protocol_frames pl @ (PModeF MResume resp :: amb))
          (plan_resume_frames pl @ amb)
    with begin
      assert (pplan_rel r n w pl pl);
      lemma_padm_layers_resume r false n w ls
        ((owner_frame ow :: PModeF MResume resp :: amb) <: pstack v cl)
        ((owner_frame ow :: amb) <: pstack v cl)
    end

(**
 * **AND THE OTHER TWO ARE REFUSED, AT EVERY MODE AND IN BOTH REGIMES.**
 * PROVED, and the refusal is a FINDING and not a gap.
 *
 * `guard_align_produce_vs_enter` and `..._bind2` put the PRODUCTION stack on the
 * left: a `PBoundaryF` on top, the protocol projection, and then a `PScopeF`.
 * The floor stops the mode search, so those `PSiteF`s have NO marker to ask, and
 * a `PSiteF` with no marker in scope does not vanish and does not fire -- IT
 * YIELDS, storing a context the other side has no counterpart for.
 *
 * That is not a shortcoming of this relation. It is exactly the mechanism
 * `xapply` exploits (`guard_nom_b2b3_verdict` above), and a middle layer that
 * related these two stacks would be UNSOUND for `pnobs`. The produce/enter
 * mismatch is not administrative; it is real.
 *)
let guard_adm_refuses_produce_vs_enter (#v #cl: Type) (r: pcl_rel_t cl)
    (m: weave_mode) (sh: bool) (w: pworld) (pl: plan v cl)
    (f: pval v -> pcomp v cl) (amb: pstack v cl) (rhs: pstack v cl)
  : Lemma (~(padm r m sh w
               (PBoundaryF :: (plan_protocol_frames pl
                               @ (PScopeF :: PBindF f :: amb)))
               rhs))
  = let ls = Plan?.layers pl in
    let ow = Plan?.owner pl in
    append_assoc (protocol_layer_frames ls) ([owner_frame ow] <: pstack v cl)
                 ((PScopeF :: PBindF f :: amb) <: pstack v cl);
    lemma_padm_unmarked_protocol m ls
      ((owner_frame ow :: PScopeF :: PBindF f :: amb) <: pstack v cl);
    introduce padm r m sh w
                (PBoundaryF :: (plan_protocol_frames pl
                                @ (PScopeF :: PBindF f :: amb)))
                rhs ==> False
    with assert (padm_stack r m sh 1 w
                   (PBoundaryF :: (plan_protocol_frames pl
                                   @ (PScopeF :: PBindF f :: amb)))
                   rhs)

(**
 * **AND THE MIDDLE LAYER IS STRICTLY BETWEEN THE TWO.** PROVED, at every plan,
 * responder and ambient stack, and in BOTH directions of the enter/resume
 * distinction.
 *
 * The very same two stacks that `guard_align_marker_vs_enter` and
 * `guard_align_marker_vs_resume` proved `pkrel` REFUSES are related by `padm`.
 * That is what "middle layer" has to mean, and it is why nothing above needed
 * weakening: `pcrel` is left exactly as it was and still refuses, and the new
 * relation is the one that does not.
 *)
let guard_adm_strictly_coarser (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (pl: plan v cl) (resp: pval v -> pcomp v cl) (amb: pstack v cl)
  : Lemma (requires pplrel r w pl pl /\ pkrel r w amb amb)
          (ensures
            padm r MExtend false w
              (plan_protocol_frames pl @ (PModeF MExtend resp :: amb))
              (plan_enter_frames pl @ amb) /\
            ~(pkrel r w
                (plan_protocol_frames pl @ (PModeF MExtend resp :: amb))
                (plan_enter_frames pl @ amb)) /\
            padm r MResume false w
              (plan_protocol_frames pl @ (PModeF MResume resp :: amb))
              (plan_resume_frames pl @ amb) /\
            ~(pkrel r w
                (plan_protocol_frames pl @ (PModeF MResume resp :: amb))
                (plan_resume_frames pl @ amb)))
  = lemma_padm_marker_vs_enter r w pl resp amb;
    guard_align_marker_vs_enter r w pl MExtend resp amb;
    lemma_padm_marker_vs_resume r w pl resp amb;
    guard_align_marker_vs_resume r w pl MResume resp amb

(* ------------------------------------------------------------------ *)
(*  CONDITION 3: CONSUMING TWO RELATED RESIDUALS IN THE SAME MODE      *)
(* ------------------------------------------------------------------ *)

(**
 * **THE SHARED MARKER IS FOUND ON BOTH SIDES, AND THE TWO RESPONDERS ARE
 * RELATED.** PROVED, by induction on the left stack, at every index from 1 up.
 *
 * This is what makes a `PBoundaryF` inside a residual behave the same way on
 * both sides: the boundary hands the value to whatever `pfind_mode` answers, and
 * `pfind_mode` answers with related responders at the same mode.
 *)
let rec lemma_padm_shared_marker (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode)
    (n: nat) (w: pworld) (k1 k2: pstack v cl)
  : Lemma (requires n >= 1 /\ padm_marked m k1 /\ padm_stack r m true n w k1 k2)
          (ensures (match pfind_mode k1, pfind_mode k2 with
                    | Some (m1, resp1), Some (m2, resp2) ->
                      m1 == m /\ m2 == m /\
                      pframe_rel r n w (PModeF m resp1) (PModeF m resp2)
                    | _, _ -> False))
          (decreases k1)
  = match k1 with
    | [] -> ()
    | PModeF _ _ :: _ -> ()
    | PSiteF _ :: t1 ->
      (match m with
       | MExtend -> lemma_padm_shared_marker r m n w t1 k2
       | MResume ->
         (match k2 with
          | PBindF _ :: t2 -> lemma_padm_shared_marker r m n w t1 t2
          | _ -> ()))
    | PBoundaryF :: t1 ->
      (match k2 with
       | PBoundaryF :: t2 -> lemma_padm_shared_marker r m n w t1 t2
       | _ -> ())
    | PBindF f1 :: t1 ->
      (match k2 with
       | f2 :: t2 ->
         FStar.Classical.move_requires (lemma_padm_shared_marker r m n w t1) t2;
         (match t1 with
          | PBindF _ :: t1' ->
            FStar.Classical.move_requires (lemma_padm_shared_marker r m n w t1') t2
          | _ -> ())
       | [] -> ())
    | PParamF _ _ :: t1 ->
      (match k2 with
       | _ :: t2 -> lemma_padm_shared_marker r m n w t1 t2
       | [] -> ())
    | PPromptF _ _ _ :: t1 ->
      (match k2 with
       | _ :: t2 -> lemma_padm_shared_marker r m n w t1 t2
       | [] -> ())
    | PScopeF :: _ -> ()

(**
 * **THE `MExtend` ADMINISTRATIVE STEP IS SILENT, AND THE RELATION SURVIVES IT.**
 * PROVED, at every stack, store and counter, and for any lookup and interpreter.
 *
 * The left takes ONE transition, EMITS NOTHING, and arrives at the same value
 * under the tail; the right stands still; and the two are still related. This is
 * the step `pframes_rel` cannot take, and it is the only thing the length
 * mismatch of the two projections is made of.
 *)
let lemma_padm_step_site_extend (#v #cl: Type) (r: pcl_rel_t cl) (sh: bool)
    (w: pworld) (lk: plookup_t cl) (apply: papply_t v cl)
    (g1: pval v -> pcomp v cl) (t1 k2: pstack v cl) (x: pval v)
    (sto: pstore v cl) (n0: nat)
  : Lemma (requires padm r MExtend sh w (PSiteF g1 :: t1) k2)
          (ensures
            (let cf : pconf v cl =
               { st = PStep (PVar x) (PSiteF g1 :: t1); store = sto; next = n0 } in
             pstep_tr lk apply cf
             == (({ st = PStep (PVar x) t1; store = sto; next = n0 } <: pconf v cl),
                 ([] <: list string)) /\
             padm r MExtend sh w t1 k2))
  = assert (padm_stack r MExtend sh 1 w (PSiteF g1 :: t1) k2);
    lemma_padm_marked_finds MExtend t1;
    introduce forall (n: nat). padm_stack r MExtend sh n w t1 k2
    with assert (padm_stack r MExtend sh n w (PSiteF g1 :: t1) k2);
    assert (padm r MExtend sh w t1 k2)

(**
 * **THE `MResume` ADMINISTRATIVE STEP IS SILENT ON BOTH SIDES, AND LANDS ON
 * RELATED COMPUTATIONS.** PROVED.
 *
 * Here BOTH sides move, each by one transition and each emitting nothing: the
 * site frame fires as the bind frame it was recorded from, and the two functions
 * are related because the relation asked for it when it matched them.
 *)
let lemma_padm_step_site_resume (#v #cl: Type) (r: pcl_rel_t cl) (sh: bool)
    (w: pworld) (lk: plookup_t cl) (apply: papply_t v cl)
    (g1 g2: pval v -> pcomp v cl) (t1 t2: pstack v cl) (x1 x2: pval v)
    (sto1 sto2: pstore v cl) (n1 n2: nat)
  : Lemma (requires padm r MResume sh w (PSiteF g1 :: t1) (PBindF g2 :: t2) /\
                    pwf_world w /\ pval_rel w x1 x2)
          (ensures
            (let cf1 : pconf v cl =
               { st = PStep (PVar x1) (PSiteF g1 :: t1); store = sto1; next = n1 } in
             let cf2 : pconf v cl =
               { st = PStep (PVar x2) (PBindF g2 :: t2); store = sto2; next = n2 } in
             pstep_tr lk apply cf1
             == (({ st = PStep (g1 x1) t1; store = sto1; next = n1 } <: pconf v cl),
                 ([] <: list string)) /\
             pstep_tr lk apply cf2
             == (({ st = PStep (g2 x2) t2; store = sto2; next = n2 } <: pconf v cl),
                 ([] <: list string)) /\
             padm r MResume sh w t1 t2 /\
             pcrel r w (g1 x1) (g2 x2)))
  = assert (padm_stack r MResume sh 1 w (PSiteF g1 :: t1) (PBindF g2 :: t2));
    lemma_padm_marked_finds MResume t1;
    lemma_pwext_refl w;
    introduce forall (n: nat). padm_stack r MResume sh n w t1 t2
    with assert (padm_stack r MResume sh n w (PSiteF g1 :: t1) (PBindF g2 :: t2));
    introduce forall (n: nat). pcomp_rel r n w (g1 x1) (g2 x2)
    with (if n = 0 then ()
          else assert (padm_stack r MResume sh n w (PSiteF g1 :: t1) (PBindF g2 :: t2)));
    assert (padm r MResume sh w t1 t2);
    assert (pcrel r w (g1 x1) (g2 x2))

(* ---- and a positive OBSERVATIONAL instance, run ------------------- *)

(** Two residuals that differ by exactly one dormant site frame. Both are
    `presid_wf`-shaped -- a boundary on top -- and they are driven by ONE
    consumer, in ONE mode, with the same `post` and the same extension. *)
let aresid1 : pstack fv fcl = [PBoundaryF; PSiteF (PVar #fv #fcl)]
let aresid2 : pstack fv fcl = [PBoundaryF]
let apost : pval fv -> pcomp fv fcl = PVar #fv #fcl
let af : pval fv -> pcomp fv fcl = PVar #fv #fcl
let aR : pval fv -> pcomp fv fcl = fun z -> pbind (apost z) af

let acf1 : pconf fv fcl =
  { st = PStep (ctx_drive MExtend (PCtxRequests fone aresid1 apost) af)
               ([] <: pstack fv fcl);
    store = []; next = 0 }
let acf2 : pconf fv fcl =
  { st = PStep (ctx_drive MExtend (PCtxRequests fone aresid2 apost) af)
               ([] <: pstack fv fcl);
    store = []; next = 0 }

(** The marker `ctx_drive` appends is self-related, which is all the relation
    asks of the shared regime. PROVED. *)
let lemma_aR_selfrel (w: pworld) (n: nat)
  : Lemma (pframe_rel fcl_rel n w (PModeF MExtend aR) (PModeF MExtend aR))
  = if n = 0 then ()
    else begin
      introduce forall (w': pworld) (y1 y2: pval fv).
          (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
           pcomp_rel fcl_rel n w' (aR y1) (aR y2))
      with (introduce _ ==> _
            with begin
              lemma_pcrel_var fcl_rel w' y1 y2;
              lemma_pfn_rel_at_pvar #fv #fcl fcl_rel w';
              lemma_pcrel_pbind fcl_rel w' (PVar y1) (PVar y2)
                                (PVar #fv #fcl) (PVar #fv #fcl);
              assert (pcrel fcl_rel w' (aR y1) (aR y2))
            end);
      assert (pframe_rel fcl_rel n w (PModeF MExtend aR) (PModeF MExtend aR))
    end

(** **THE TWO DRIVEN RESIDUALS ARE ADMINISTRATIVELY RELATED, IN THE SHARED
    REGIME.** PROVED. `ctx_drive` puts the SAME marker under both. *)
let guard_adm_residuals_related (w: pworld)
  : Lemma (padm fcl_rel MExtend true w
             (aresid1 @ [PModeF MExtend aR]) (aresid2 @ [PModeF MExtend aR]))
  = introduce forall (n: nat).
        padm_stack fcl_rel MExtend true n w
          (aresid1 @ [PModeF MExtend aR]) (aresid2 @ [PModeF MExtend aR])
    with lemma_aR_selfrel w n

(**
 * **CONSUMED IN THE SAME MODE, THEY GIVE THE SAME TRACE, EQUAL VALUES AND EQUAL
 * STORES.** PROVED, by running the machine.
 *
 * Both traces are empty, both answers are `fone`, and neither run allocates --
 * the extra site frame on the left costs exactly one silent transition. This is
 * ONE instance and is labelled as one: the general statement is the NEXT gate's,
 * and nothing here stands in for it.
 *)
let guard_adm_consume_same_mode ()
  : Lemma ((fst (prun flook xapply 20 acf1)).st == PDone fone /\
           snd (prun flook xapply 20 acf1) == ([] <: list string) /\
           (fst (prun flook xapply 20 acf1)).store == ([] <: pstore fv fcl) /\
           (fst (prun flook xapply 20 acf2)).st == PDone fone /\
           snd (prun flook xapply 20 acf2) == ([] <: list string) /\
           (fst (prun flook xapply 20 acf2)).store == ([] <: pstore fv fcl))
  = assert_norm ((fst (prun flook xapply 20 acf1)).st == PDone fone);
    assert_norm (snd (prun flook xapply 20 acf1) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 20 acf1)).store == ([] <: pstore fv fcl));
    assert_norm ((fst (prun flook xapply 20 acf2)).st == PDone fone);
    assert_norm (snd (prun flook xapply 20 acf2) == ([] <: list string));
    assert_norm ((fst (prun flook xapply 20 acf2)).store == ([] <: pstore fv fcl))

(* ------------------------------------------------------------------ *)
(*  CONDITION 4: THE DECISION POINT                                    *)
(* ------------------------------------------------------------------ *)

(**
 * **`xapply` PRESERVES THE ADMINISTRATIVE RELATION.** PROVED.
 *
 * `xapply` is the interpreter the four counterexamples are taken at: it opens a
 * scope of its own and APPLIES the continuation it was handed, which is what an
 * ordinary handler does. It cannot tell two administratively equal continuations
 * apart, because it never looks at one -- it calls it.
 *
 * This is the half of condition 4 that says the relation is not too fine. An
 * administrative relation that `xapply` broke would be excluding general
 * higher-order handlers for the laws' convenience.
 *)
let guard_adm_xapply_preserved ()
  : Lemma (padm_apply_pres fcl_rel xapply)
  = introduce forall (m: weave_mode) (sh: bool) (w: pworld) (c1 c2: fcl)
                     (p1 p2: list (pval fv)) (kk1 kk2: pval fv -> pcomp fv fcl).
      (pwf_world w /\ pclrel fcl_rel w c1 c2 /\ pvals_rel w p1 p2 /\
       padm_fn_at fcl_rel m sh w kk1 kk2 ==>
       padm_comp fcl_rel m sh w (xapply c1 p1 kk1) (xapply c2 p2 kk2))
    with (introduce _ ==> _
          with begin
            lemma_pwext_refl w;
            assert (pval_rel #fv w (fpv FU) (fpv FU));
            assert (padm_comp fcl_rel m sh w (kk1 (fpv FU)) (kk2 (fpv FU)));
            introduce forall (n: nat). pplan_rel fcl_rel n w xplan xplan
            with lemma_xplan_selfrel n w;
            assert (pplrel fcl_rel w xplan xplan)
          end)

(** Two continuations that differ by exactly one dormant site frame and the
    marker that answers it -- administratively equal, and of different LENGTH. *)
let akk1 : pval fv -> pcomp fv fcl
  = fun x -> PSplice [PSiteF (PVar #fv #fcl); PModeF MExtend (PVar #fv #fcl)] (PVar x)
let akk2 : pval fv -> pcomp fv fcl
  = fun x -> PSplice ([] <: pstack fv fcl) (PVar x)

let lemma_akk_padm (w: pworld)
  : Lemma (padm_fn_at fcl_rel MExtend false w akk1 akk2)
  = introduce forall (w': pworld) (y1 y2: pval fv).
        (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
         padm_comp fcl_rel MExtend false w' (akk1 y1) (akk2 y2))
    with (introduce _ ==> _
          with begin
            lemma_pcrel_var fcl_rel w' y1 y2;
            introduce forall (n: nat).
                padm_stack fcl_rel MExtend false n w'
                  ([PSiteF (PVar #fv #fcl); PModeF MExtend (PVar #fv #fcl)]
                   <: pstack fv fcl)
                  ([] <: pstack fv fcl)
            with ();
            assert (padm fcl_rel MExtend false w'
                     ([PSiteF (PVar #fv #fcl); PModeF MExtend (PVar #fv #fcl)]
                      <: pstack fv fcl)
                     ([] <: pstack fv fcl))
          end)

(**
 * **`xapply2` IS REFUSED.** PROVED, at every well-formed world and every clause.
 *
 * `xapply2` READS THE LENGTH of the segment its continuation would splice back.
 * Handed two administratively equal continuations it answers `FI 2` and `FI 0`,
 * and those are not related values at any world.
 *
 * This is the half of condition 4 that says the relation is not too coarse. An
 * administrative relation `xapply2` preserved would be one that had thrown the
 * frame count away, and the frame count is what the four counterexamples above
 * are made of.
 *)
let guard_adm_xapply2_refused (w: pworld) (c: fcl)
  : Lemma (requires pwf_world w)
          (ensures ~(padm_apply_pres fcl_rel xapply2))
  = lemma_akk_padm w;
    introduce padm_apply_pres fcl_rel xapply2 ==> False
    with begin
      padm_apply_pres_inst fcl_rel xapply2 MExtend false w c c
        ([] <: list (pval fv)) ([] <: list (pval fv)) akk1 akk2;
      assert_norm (xapply2 c ([] <: list (pval fv)) akk1 == PVar (PV (FI 2)));
      assert_norm (xapply2 c ([] <: list (pval fv)) akk2 == PVar (PV (FI 0)));
      assert (pcrel fcl_rel w (PVar #fv #fcl (PV (FI 2))) (PVar #fv #fcl (PV (FI 0))));
      assert (pcomp_rel fcl_rel 1 w (PVar #fv #fcl (PV (FI 2)))
                                    (PVar #fv #fcl (PV (FI 0))))
    end

(**
 * **THE DECISION, AS ONE STATEMENT.** PROVED, and stated against
 * `papply_equivariant` so that the separation is visible.
 *
 * BOTH interpreters satisfy the boundary's condition -- `papply_equivariant` is
 * proved of each above, and neither is weakened. The administrative demand
 * separates them: `xapply`, which only APPLIES its continuation, meets it;
 * `xapply2`, which READS THE LENGTH of the segment it was handed, does not.
 *
 * So `padm_apply_pres` is STRICTLY STRONGER than `papply_equivariant`, and the
 * line it draws is exactly the line between calling a continuation and
 * inspecting one. The granularity is right in both directions: an
 * administrative relation `xapply` broke would be too fine (it would exclude
 * ordinary higher-order handlers), and one `xapply2` preserved would be too
 * coarse (it would have thrown away the frame count the four counterexamples
 * are made of).
 *)
let guard_adm_condition_4 (w: pworld) (c: fcl)
  : Lemma (requires pwf_world w)
          (ensures papply_equivariant fcl_rel xapply /\
                   padm_apply_pres fcl_rel xapply /\
                   papply_equivariant fcl_rel xapply2 /\
                   ~(padm_apply_pres fcl_rel xapply2))
  = lemma_xapply_equivariant ();
    lemma_xapply2_equivariant ();
    guard_adm_xapply_preserved ();
    guard_adm_xapply2_refused w c

(* ------------------------------------------------------------------ *)
(*  CONDITION 5: A SMALL POSITIVE INSTANCE OF `pbind` ASSOCIATIVITY    *)
(* ------------------------------------------------------------------ *)

(**
 * **THE TWO BRACKETINGS PUT ADMINISTRATIVELY EQUAL STACKS UP.** PROVED, at
 * `f = g = PVar` over the empty ambient stack.
 *
 * `pbind (pbind c f) g` takes TWO transitions to reach `c` under
 * `PBindF f :: PBindF g`; `pbind c (fun x -> pbind (f x) g)` takes ONE to reach
 * `c` under a single bind frame carrying the composition. `pframes_rel` refuses
 * the two stacks on LENGTH -- which is `guard_align_bracketing`'s obstruction
 * seen from the stack rather than from the responder -- and the administrative
 * relation matches them, because a value takes both to the same configuration.
 *)
let guard_adm_pbind_assoc_small (#v #cl: Type) (r: pcl_rel_t cl) (m: weave_mode)
    (sh: bool) (w: pworld)
  : Lemma (padm r m sh w
             ([PBindF (PVar #v #cl); PBindF (PVar #v #cl)] <: pstack v cl)
             ([PBindF (fun (x: pval v) -> pbind (PVar #v #cl x) (PVar #v #cl))]
              <: pstack v cl))
  = introduce forall (n: nat).
        padm_stack r m sh n w
          ([PBindF (PVar #v #cl); PBindF (PVar #v #cl)] <: pstack v cl)
          ([PBindF (fun (x: pval v) -> pbind (PVar #v #cl x) (PVar #v #cl))]
           <: pstack v cl)
    with (if n = 0 then ()
          else begin
            introduce forall (w': pworld) (y1 y2: pval v).
                (pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==>
                 pcomp_rel r n w' (pbind (PVar #v #cl y1) (PVar #v #cl))
                                  (pbind (PVar #v #cl y2) (PVar #v #cl)))
            with (introduce _ ==> _
                  with begin
                    lemma_pcrel_var r w' y1 y2;
                    lemma_pfn_rel_at_pvar #v #cl r w';
                    lemma_pcrel_pbind r w' (PVar y1) (PVar y2)
                                      (PVar #v #cl) (PVar #v #cl);
                    assert (pcrel r w' (pbind (PVar #v #cl y1) (PVar #v #cl))
                                       (pbind (PVar #v #cl y2) (PVar #v #cl)))
                  end);
            assert (pframe_rel r n w
                      (PBindF (fun (x: pval v) -> pbind (PVar #v #cl x) (PVar #v #cl)))
                      (PBindF (fun (x: pval v) -> pbind (PVar #v #cl x) (PVar #v #cl))));
            assert (padm_stack r m sh n w ([] <: pstack v cl) ([] <: pstack v cl))
          end)

(** And the two stacks the two bracketings actually put up are NOT `pkrel`
    related, at any world -- so the clause above is doing work and is not a
    restatement of something `pframes_rel` already had. PROVED, on length. *)
let guard_adm_assoc_not_pkrel (#v #cl: Type) (r: pcl_rel_t cl) (w: pworld)
    (f g h: pval v -> pcomp v cl)
  : Lemma (~(pkrel r w ([PBindF f; PBindF g] <: pstack v cl)
                       ([PBindF h] <: pstack v cl)))
  = introduce pkrel r w ([PBindF f; PBindF g] <: pstack v cl)
                        ([PBindF h] <: pstack v cl) ==> False
    with lemma_pkrel_length r w ([PBindF f; PBindF g] <: pstack v cl)
                                ([PBindF h] <: pstack v cl)

(* ================================================================== *)
(*  B2b.4 LEDGER                                                       *)
(*                                                                     *)
(*  CONDITION 4 FIRST, BECAUSE IT IS THE DECISION POINT.                *)
(*                                                                     *)
(*   - `xapply` IS PRESERVED (`guard_adm_xapply_preserved`) and        *)
(*     `xapply2` IS REFUSED (`guard_adm_xapply2_refused`), both        *)
(*     PROVED, and the pair is `guard_adm_condition_4`, which states   *)
(*     it against `papply_equivariant`: BOTH interpreters satisfy the  *)
(*     boundary's condition, and only one satisfies the               *)
(*     administrative one.  So `padm_apply_pres` is STRICTLY STRONGER  *)
(*     than `papply_equivariant` and the line it draws is exactly the  *)
(*     line between CALLING a continuation and INSPECTING one.         *)
(*                                                                     *)
(*     The granularity is therefore the one the question asked for:    *)
(*     coarse enough that an interpreter which only APPLIES its        *)
(*     continuation cannot see the difference, fine enough that one    *)
(*     which READS THE LENGTH of the segment it was handed can.        *)
(*     Neither outcome was engineered: `xapply` is preserved because   *)
(*     it never inspects the continuation, and `xapply2` is refused    *)
(*     because the erased site frame and its marker are two frames     *)
(*     and `xklen` counts them.                                        *)
(*                                                                     *)
(*  CONDITION 1: MET.  `padm_stack` is a total `GTot prop`, indexed    *)
(*  by the mode and by the marker regime.  The two modes do NOT        *)
(*  collapse (`guard_adm_modes_differ`, `guard_adm_resume_is_bind`):   *)
(*  one left stack is related to the EMPTY stack at `MExtend` and to   *)
(*  `[PBindF PVar]` at `MResume`, and to neither at the other mode.    *)
(*                                                                     *)
(*  CONDITION 2: MET FOR TWO OF THE FOUR, AND THE OTHER TWO ARE        *)
(*  REFUSED FOR A REASON.                                              *)
(*                                                                     *)
(*   - `guard_align_marker_vs_enter`'s two stacks: RELATED, at every   *)
(*     plan, responder and ambient stack (`lemma_padm_marker_vs_       *)
(*     enter`);                                                         *)
(*   - `guard_align_marker_vs_resume`'s: RELATED, likewise             *)
(*     (`lemma_padm_marker_vs_resume`); and `guard_adm_strictly_`      *)
(*     `coarser` puts the two facts beside the two REFUSALS the redux  *)
(*     proved of the very same pairs, which is what makes this a       *)
(*     middle layer rather than a second name for `pkrel`;             *)
(*   - `guard_align_produce_vs_enter`'s and `..._bind2`'s: REFUSED,    *)
(*     at EVERY mode, in BOTH regimes, and against ANY right-hand      *)
(*     side (`guard_adm_refuses_produce_vs_enter`).  The reason is     *)
(*     `PScopeF`: production installs a floor, the floor stops the     *)
(*     mode search, and a `PSiteF` with no marker in scope neither     *)
(*     vanishes nor fires -- IT YIELDS.  Relating those two stacks     *)
(*     would be unsound for `pnobs`, and `xapply` is the witness       *)
(*     (`guard_nom_b2b3_verdict`).  So the produce/enter mismatch is   *)
(*     NOT administrative.  That is a finding about the laws' shape,   *)
(*     not a gap in the relation: right identity and transparency      *)
(*     will not be recovered by a middle layer at the stack level.     *)
(*                                                                     *)
(*  CONDITION 3: MET IN THREE PIECES, AND THE GENERAL OBSERVATIONAL    *)
(*  STATEMENT IS NOT ATTEMPTED -- it is the next gate's.                *)
(*                                                                     *)
(*   - the `MExtend` administrative step is SILENT and the relation    *)
(*     survives it, at every stack, store and counter                  *)
(*     (`lemma_padm_step_site_extend`);                                *)
(*   - the `MResume` step is silent on BOTH sides and lands on         *)
(*     `pcrel`-related computations (`lemma_padm_step_site_resume`);   *)
(*   - a shared marker is found on both sides with related responders  *)
(*     (`lemma_padm_shared_marker`), which is what makes a             *)
(*     `PBoundaryF` inside a residual behave alike on the two sides;   *)
(*   - and ONE observational instance is RUN: two residuals differing  *)
(*     by exactly one dormant site frame, driven by one consumer in    *)
(*     one mode, give the SAME TRACE (empty), EQUAL VALUES (`fone`)    *)
(*     and EQUAL STORES (empty) (`guard_adm_residuals_related`,        *)
(*     `guard_adm_consume_same_mode`).                                 *)
(*                                                                     *)
(*  Nothing in condition 3 relates two residuals consumed in           *)
(*  DIFFERENT modes, and the relation could not state it: the mode is  *)
(*  an index on the relation and both sides read the same one.        *)
(*                                                                     *)
(*  CONDITION 5: MET, AT ONE INSTANCE.  `guard_adm_pbind_assoc_small`  *)
(*  relates `[PBindF PVar; PBindF PVar]` to the single bind frame      *)
(*  carrying their composition, and `guard_adm_assoc_not_pkrel`        *)
(*  checks that `pkrel` refuses the same pair on LENGTH -- so the      *)
(*  two-bind clause is not a restatement of something already there.   *)
(*  What is NOT established is that the clause suffices for the        *)
(*  algebraic half: `guard_align_bracketing` refutes at the level of   *)
(*  the marker's RESPONDER, and absorbing that would need the same     *)
(*  re-bracketing inside `pframe_rel`, which is not done here.         *)
(*                                                                     *)
(*  WHAT WAS NOT DONE, AND IS NAMED                                    *)
(*                                                                     *)
(*   - NO law is attempted, wholly or partly;                          *)
(*   - `padm` is NOT proved sound for `pnobs_tr_eq`.  Three of its     *)
(*     ingredients are proved -- the two silent-step lemmas and the    *)
(*     shared-marker lemma -- and one instance is run, and that is     *)
(*     all;                                                            *)
(*   - and the ingredient NOT even stated is the one a soundness       *)
(*     proof will have to face first: `PPerform` dispatches by         *)
(*     `pfind_prompt`, which CAPTURES THE SEGMENT above the matching   *)
(*     prompt, and two `padm`-related stacks hand DIFFERENT segments   *)
(*     to the clause -- related administratively, but not equal, and   *)
(*     not of equal length.  Whether `padm` is preserved across a      *)
(*     dispatch is exactly what `padm_apply_pres` was written to ask,  *)
(*     and condition 4 answers it only for the two interpreters this   *)
(*     file has.  Nothing here shows `pfind_prompt` itself respects    *)
(*     the relation, and `pfind_param`, `pcut_scope` and               *)
(*     `pset_param`, which also walk the stack, are equally untouched; *)
(*   - `pcrel`, `pframes_rel`, `pnobs_tr_le` and every definition of   *)
(*     B2b.3 and earlier are UNTOUCHED.  `padm_stack` is built out of  *)
(*     `pframe_rel` and `pframes_rel`, so it inherits rather than      *)
(*     replaces;                                                       *)
(*   - NO `rlimit`, NO `#push-options`, NO `admit`, NO `assume`.       *)
(* ================================================================== *)
