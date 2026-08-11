(**
 * **The trust boundary, made into types.**
 *
 * `runtime/ml/melange/hoop_ffi.ml` is the layer where F* stops verifying and
 * starts assuming: it receives values PureScript built and turns them into
 * nodes the machine runs. This module is the *only* vocabulary it has for doing
 * so. The intended shape of the dependency is
 *
 * ```text
 *   hoop_ffi.ml  -->  Hoop.Runtime.Api  -->  Hoop.Runtime.Syntax
 * ```
 *
 * with the middle arrow the one that can be read off a type, and the boundary
 * naming no `Hoop_Runtime_Syntax` identifier at all.
 *
 * ### What it admits
 *
 * Exactly the eight nodes the PureScript surface is entitled to build:
 *
 * ```text
 *   var   op   perform   performS   handle   newP   readP   writeP
 * ```
 *
 * These are the AST of a *source program*: a value, a monadic bind, an ordinary
 * and a scoped operation, a handler installation, and the three prompt-local
 * cell operations. Every one of them is something a user wrote, and every one
 * of them is a node whose well-scopedness PureScript's row types are supposed
 * to establish.
 *
 * ### What it refuses
 *
 * `Splice`, `Weave`, and the three frame constructors `BindF` / `ParamF` /
 * `PromptF`. There is no function here that builds one and no function here
 * that takes one apart, so a boundary written against this interface cannot
 * mention them however it is written.
 *
 * `Splice` and `Weave` are machine-internal. `Splice` carries a captured stack
 * segment and is what the machine inserts when a handler clause resumes;
 * `Weave` carries a *normalized* segment and is what applying a scoped clause's
 * weave capability produces. The frame constructors are the segments' elements,
 * and they carry handler tables and cell values. A `comp_tree` built out of
 * frames is a continuation forged by hand, and destructuring one is the same
 * leak read backwards -- which is why this interface offers no eliminator
 * either, only introduction.
 *
 * ### Why refusing matters
 *
 * Not for the correspondence theorem. `Hoop.Runtime.execute` has no
 * precondition, so a forged `Splice` arriving from the boundary would satisfy
 * it perfectly well: the machine would stop where the reference machine stops
 * on that same program. Nothing here is load-bearing for the answer being
 * *right*.
 *
 * What it protects is the **trusted** side of the boundary -- the claim that
 * PureScript's type system only produces well-scoped programs, which is what
 * `Hoop.Runtime.WellScopedness.ws` is assumed of and what makes `execute`'s
 * `never_stuck` hypothesis believable rather than merely stated. *Row types say
 * nothing whatever about frame lists.* A surface that could fabricate a
 * computation carrying an arbitrary captured segment would be making a claim
 * its type system does not support, and the hypothesis would stop being
 * credible at exactly the point it is relied on.
 *
 * The predecessor of this module was a grep in `scripts/build-runtime.sh`
 * (guard (e)): a whitelist of constructor names allowed to appear in the
 * boundary after comments were stripped. That was a real check and it fired on
 * real violations, but it was a check *about* the boundary rather than a
 * property *of* it, and every widening was a whitelist edit. Here the widening
 * is a `val`, reviewed as a `val`, and the check reduces to the far simpler and
 * strictly stronger statement that the boundary may not name
 * `Hoop_Runtime_Syntax` at all.
 *
 * ### What is deliberately NOT here
 *
 * Three groups, and the reason is the same for all three: this module is about
 * what the boundary may **build**, and none of them is that.
 *
 *   - **`Hoop.Runtime.{ct, clause, Full, Fast, Scoped, mk_runtime_handlers}`.**
 *     A tagged clause has three constructors and the boundary is entitled to
 *     build all three -- there is no internal one to hide, so a wrapper would be
 *     indirection with nothing behind it. `mk_runtime_handlers` is *already* the
 *     narrowed entry point (it fixes the classifier the boundary must not
 *     supply, Decision 7), and it is narrowed in the layer that owns the tags,
 *     which is where that argument lives. Moving it here would not even retire
 *     its build guard: what that guard forbids is a call to
 *     `Hoop_Runtime_Handlers.mk_handlers`, which no interface elsewhere can make
 *     unreachable.
 *
 *   - **`Hoop.Runtime.{execute, mstate}` and `Hoop.Runtime.Semantics.rejection`.**
 *     These are *outputs*. `execute` is the machine, and `MDone` / `MStuck` /
 *     `MRejected` / `MStep` and the `rejection` constructors are destructured to
 *     produce an error message. Reading a result the machine produced forges
 *     nothing.
 *
 *   - **`Hoop.Runtime.Semantics.var_eff`.** A constant, read so that the
 *     boundary's specialised "cell used outside its scope" message and the
 *     reference machine's reserved effect label cannot drift apart. Re-exporting
 *     it would add a second name that could drift, which is the opposite of the
 *     point.
 *
 * Keeping those out is what leaves this interface with a single reading: these
 * eight, and nothing else, are the nodes a program can arrive as.
 *
 * ### Definitional, deliberately
 *
 * Every constructor below is pinned to its `Hoop.Runtime.Syntax` counterpart by
 * a refinement on its result, so `Api.var x == Var x` is available to any proof
 * that wants it and the extracted code is unchanged in substance. Nothing
 * downstream is restated: no theorem is phrased about these names, because
 * there is nothing new to say about them. This module adds a *vocabulary
 * restriction*, not a semantics.
 *
 * See docs/study-notes/2026-08-11-scoped-effects-detailed-design.md, Decision 1
 * (acceptance condition 6, and "What condition 6 protects, and what it does
 * not") and Decision 7.
 *)
module Hoop.Runtime.Api

(* The AST, and the runtime's clause tagging. Everything below is stated at
   `Hoop.Runtime.ct`, i.e. `comp_tree v (clause cl)`, which is the type the
   machine runs and the type the boundary's `comp` abbreviates -- so the
   boundary never has to name `comp_tree` even in a type annotation. *)
open Hoop.Runtime.Syntax
open Hoop.Runtime

(** **A value.** The `pure` of the `Hoop` monad: the computation that is already
    finished and whose result is `value`. *)
val var (#v #cl: Type) (value: v)
  : Tot (c: ct v cl { c == Var value })

(** **A monadic bind.** `c` runs first and its result is handed to `fn`. The
    continuation is an ordinary function, which is what keeps it *the user's*
    continuation: the machine's own defunctionalized continuations are frame
    lists, and those are not reachable from here. *)
val op (#v #cl: Type) (c: ct v cl) (fn: v -> ct v cl)
  : Tot (r: ct v cl { r == Op c fn })

(** **An ordinary (algebraic) operation.** The payload is the operation's
    arguments, in the order the signature declares them; the boundary treats
    each element as an opaque `v` and so does the machine.

    The label `eff` must not be `Hoop.Runtime.Semantics.var_eff`, which is
    reserved for prompt-local cells -- but that is a condition on *programs*,
    stated by `Hoop.Runtime.WellScopedness.ws`, not a refinement here: making it
    one would put a proof obligation on a boundary that receives its strings
    from JavaScript and could not discharge it. *)
val perform (#v #cl: Type) (eff: string) (op: string) (payload: list v)
  : Tot (r: ct v cl { r == Perform eff op payload })

(**
 * **A scoped (higher-order) operation.** The same three fields as `perform`,
 * and the constructor is the whole of the difference: what it marks is the KIND
 * OF THE OPERATION, which the handler table's stored `clause_kind` is checked
 * against at dispatch.
 *
 * **The inner computations are inside the payload, and nothing on this side
 * knows it.** A scoped operation's payload carries the user's higher-order
 * signature value -- `h (Hoop inner) b` -- as one more opaque element. The
 * boundary neither knows nor checks that, and that is Decision 3's whole point:
 * the runtime never traverses those computations, so it never owes the
 * `HFunctor` obligation traversing them would require. The clause destructures
 * the payload itself and applies the `weave` capability the machine hands it to
 * whichever computation it selects.
 *
 * What is trusted, and where it is paid for: that a clause applies `weave` only
 * to computations from its own rigid inner family is the rank-2 quantifier's
 * job on the PureScript side, and it is assumed here as
 * `Hoop.Runtime.WellScopedness.apply_scoped_ok`.
 *)
val performS (#v #cl: Type) (eff: string) (op: string) (payload: list v)
  : Tot (r: ct v cl { r == PerformS eff op payload })

(**
 * **A handler installation.** `hs` is the table -- which the boundary must have
 * built through `Hoop.Runtime.mk_runtime_handlers`, so that the *kind* of each
 * clause is a reading of the tag the boundary attached rather than an assertion
 * the boundary made -- `pure` is the optional return clause, and `body` is the
 * computation run under the prompt.
 *
 * Note what does NOT appear: `PromptF`, the frame this node becomes when the
 * machine steps into it. Installing a prompt is a source-level act and is
 * offered; putting a prompt frame onto a stack by hand is not.
 *)
val handle (#v #cl: Type)
           (hs: handlers (clause cl))
           (pure: option (v -> ct v cl))
           (body: ct v cl)
  : Tot (r: ct v cl { r == Handle hs pure body })

(** **A prompt-local cell, for the duration of `body`.** The label names a
    *binder*, not a location: the cell lives in a `ParamF` frame by value, so a
    captured continuation carries its own copy. That frame, again, is not
    reachable from here -- only the source-level `new` that creates it. *)
val newP (#v #cl: Type) (label: string) (init: v) (body: ct v cl)
  : Tot (r: ct v cl { r == NewP label init body })

(** **Read the nearest enclosing cell of this label.** *)
val readP (#v #cl: Type) (label: string)
  : Tot (r: ct v cl { r == ReadP label })

(** **Write the nearest enclosing cell of this label.** *)
val writeP (#v #cl: Type) (label: string) (value: v)
  : Tot (r: ct v cl { r == WriteP label value })
