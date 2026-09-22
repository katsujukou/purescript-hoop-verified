# Scoped Effects: detailed design

Date: 2026-08-11
Status: Living document. Decisions are recorded here as they are taken; the
agenda at the end lists what is still open.

Predecessors: `2026-08-06-general-higher-order-effects.md` (direction),
`2026-08-10-toward-scoped-effects.md` (what prompt-local state established, and
the deadlines it set). This note is the specification level: each section is a
decision that has been argued to a conclusion, with its acceptance conditions.

---

## Decision 1 — `Resumed` becomes `Splice`

**Taken. Semantics-preserving; may land before the rest of the scoped design is
settled, and is not wasted if that design changes.**

### The change

`Hoop.Runtime.Syntax.Resumed` carries a captured segment and a *value*. The
scoped work needs the same node carrying a segment and a *computation* — a
woven inner computation is exactly "run this program with these frames spliced
on". Rather than adding a second splicing node, generalise the one that exists:

```fstar
| Splice: frames:list (frame v cl) -> body:comp_tree v cl -> comp_tree v cl
// step: Step (Splice fs c) k  ->  Step c (fs @ k)
```

and keep the old node as an abbreviation, so that its meaning survives as a
name rather than as a parallel datatype:

```fstar
unfold
let resumed (#v #cl: Type) (fs: list (frame v cl)) (x: v) : comp_tree v cl
  = Splice fs (Var x)
```

`Resumed fs x` and `Splice fs (Var x)` cannot be stated as *equivalent*, because
after the change only one of them exists. Maintaining both — an old AST, an
injection, and a step-commutation proof — is the parallel-module approach that
`2026-08-10` §6 records as a wrong turn (2000 lines before the blocker
surfaced). The abbreviation buys the same assurance at no cost: the old claims
stay writable, and the day one of them stops being writable is the alarm.

### Acceptance conditions

1. **`resumed` is kept as an abbreviation** for `Splice fs (Var x)`.

2. **The old transition and the meaning of `kont_of` are pinned by definitional
   equalities:**

   ```fstar
   let step_resumed apply fs x k
     : Lemma (step apply (Step (resumed fs x) k) == Step (Var x) (fs @ k))
     = ()
   ```

   plus `kont_of cap x == resumed cap x`. These are tautologies as written; they
   are regression tests, and they fail the moment `Splice`'s rule is defined as
   anything other than `fs @ k`.

3. **Every theorem that named `Resumed` survives under its own name, as a
   statement of the same meaning about `resumed`, derived as a corollary of the
   general form.** This is the corrected form of "the old statements survive
   verbatim", which is not achievable: `step_resumed` currently uses the
   constructor recognizers `Resumed?`, `Resumed?.frames`, `Resumed?.value`, and
   those disappear with the constructor. The names in scope are
   `ws_resumed`, `ws_resumed_fwd`, `pres_resumed`, `step_resumed`.

4. **The general form is the new principal theorem:**

   ```fstar
   val ws_splice  : ws cok can (Splice fs body)
                    <==> wf_stack cok can fs /\ ws cok (can_in_with fs can) body
   val pres_splice : ...
   ```

   with the structure

   ```text
   ws_splice   ──specialise──>  ws_resumed
   pres_splice ──specialise──>  pres_resumed
   step Splice ──specialise──>  step_resumed
   ```

5. **progress, the laws and the simulation hold with the existing public
   hypotheses.** *Stop rule:* if any existing public theorem or the FFI boundary
   needs a **new independent hypothesis**, stop and return to the design — that
   is evidence that `Splice` has changed the range over which the laws hold, not
   that the proof is merely awkward. Specifically excluded from counting as a
   new hypothesis:

   - `ws_splice` demanding well-scopedness of the body;
   - `pres_splice` using `wf_stack_append` and friends internally;
   - local premises derivable from the existing `wf_state` / `ws`;
   - auxiliary lemmas added to discharge the new `sim` constructor case.

6. **The FFI cannot name internal continuation or frame constructors.** Enforced
   as guard (e) of `scripts/build-runtime.sh`: after stripping comments, every
   occurrence of `Hoop_Runtime_Syntax.` in `runtime/ml/melange/hoop_ffi.ml` must
   be one of a whitelist — currently `Var`, `Op`, `Perform`, `Handle`, `NewP`,
   `ReadP`, `WriteP`. `Splice`, `resumed`, `BindF`, `ParamF`, `PromptF`
   therefore fail.
   The check is on identifiers, so it forbids *pattern matching* on frames as
   well as constructing them. References to other extracted modules
   (`Hoop_Runtime.{ct, clause, Full, Fast, MDone, MStuck, MStep, execute}`,
   `Hoop_Runtime_Handlers.mk_handlers`, `Hoop_Runtime_Semantics.var_eff`) are
   out of scope for this guard.

   The whitelist reads *qualified* names, so an `open` of an extracted module
   would make exactly what it is looking for invisible to it. The guard
   therefore rejects one outright, as a separate error. It was checked to FIRE
   and not merely to pass, on four violations — constructing `Splice`, matching
   on `BindF`, constructing `PromptF`, and adding the `open` — and to stay
   silent when the same names appear only in a comment.

### What condition 6 protects, and what it does not

Not the correspondence theorem. `Hoop.Runtime.execute` has no precondition, so a
malformed `Splice` arriving from the FFI would still satisfy it: the machine
would stop where the reference machine stops on that same program.

What it protects is the *trusted* side of the boundary — the claim that
PureScript's type system only produces well-scoped programs. Row types say
nothing whatever about frame lists, so if the surface could fabricate an
internal computation carrying an arbitrary segment, that claim would stop being
believable. The guard is syntactic and lives inside the handwritten TCB, so it
is not a proof; it is a CI-enforced invariant that makes an unintended widening
of the exposed surface show up as a diff.

`Api.fsti` — a thin module exposing only the smart constructors the FFI may
use, so that

```text
hoop_ffi.ml  →  Hoop.Runtime.Api  →  Hoop.Runtime.Syntax
```

promotes this syntactic guard to a typed boundary — is deferred to **the first
scoped-runtime FFI change, once the scoped operation's AST representation has
been settled**. It is deliberately not tied to a `PerformS` node, whose fate is
open (see below): scoped support adds a `Scoped` clause tag, a
`scoped_apply_t`, a third interpreter and `mkScopedClauseImpl` to the FFI
whether or not the AST gains a constructor, and that is the natural moment to
pin the exposed surface with types. Until then the whitelist stands, and any
widening of it is a one-line diff — which is the review artifact.

### Grounding (checked against the source, 2026-08-11)

Recorded because each of these is a way the stop rule of condition 5 could have
fired, and none of them does:

- **The machine case generalises literally.** `Hoop.Runtime.fst:999` is
  `MStep (Var value) (mreinstall_fast w kont) (inj_append kont kk)`; the new
  case is that with `Var value` replaced by `body`. `erase_st` passes the
  control component through unchanged, so `msim` keeps its shape — one machine
  transition, one reference transition.
- **`ws_resumed` really is a corollary.** Specialising `ws_splice` at
  `body := Var x` leaves `ws cok (can_in_with fs can) (Var x)`, which collapses
  to `True` by the existing `ws_var`. Nothing is assumed.
- **`apply_ok` does not move.** It constrains the continuation by
  `forall x. ws cok can (kf x)`; at `kf = kont_of captured` this unfolds to
  `wf_stack cok can captured`, the same proposition as before the change. The
  FFI-boundary hypothesis is unchanged character for character.
- **The termination measures are unchanged.** `ws_n` decreases at `%[n; 1; 0]`
  and `wf_stack_n` at `%[n; 0; length k]`. The `Splice` arm needs
  `wf_stack_n n cok can fs` (same `n`, second component 1 → 0) and
  `ws_n (n-1) cok (can_in_with fs can) body` (`n` decreases). Both fit the
  existing order.

### Where the risk actually is

Condition 5, and within it the laws. `Hoop.Runtime.Laws` quantifies over
`comp_tree`, so adding a general form **strengthens** every law statement: they
now claim more programs. The places to look first are the `sim` family, together
with `no_prompt` / `fp_append_in` / `fp_append_out`, which prove the laws by
replacing prompt-free blocks of the stack. Arbitrary *frames* inside a spliced
node were already possible with `Resumed`; an arbitrary *body* is new.

---

## Decision 2 — what the woven segment is made of

**Taken.**

A scoped operation dispatches like any other: `find_prompt` returns
`(captured, clause, below)`, and `find_prompt_partitions` / `find_prompt_last`
give `captured == intermediates @ [owner]` with `PromptF? owner`. The segment
the scope runs under is built from those two parts, which play **different
roles**:

```text
prepare_scope intermediates owner =
  guard (all_prompts_borrowable intermediates);
  borrow intermediates @ [owner]        // owner keeps hs AND ret

borrow k = match k with
  | []                -> []
  | BindF _    :: r   -> borrow r                    // drop
  | ParamF l x :: r   -> ParamF l x :: borrow r      // keep, by value
  | PromptF hs _ :: r -> PromptF hs None :: borrow r // dispatch only
```

### The intermediates: borrowed

Dropping `BindF` and setting `ret := None` is the whole content of "available
for dispatch, but not an answer boundary". Keeping `ParamF` **by value** is what
makes the borrowing coherent:

- operation capabilities are restored;
- cell capabilities are restored;
- the perform site's continuation is *not* carried in;
- cell contents branch as a snapshot.

**This closes the label-collision hazard of `2026-08-10` §1 structurally.** The
relative position of a borrowed `PromptF` and the `ParamF` frames belonging to
it is preserved, so a borrowed clause still meets its own cell first. No runtime
label minting, hence no runtime content in `Region`, hence the rank-2 escape
argument of `2026-08-10` §4 stands unexamined.

It also fixes the interaction with prompt-local state: **the cell is a snapshot
if its handler is borrowed (inside the scope), and live if its handler sits
outside the scoped handler.** Which of the two applies is decided by handler
composition order — the same mechanism that produces the two Koka figures in
`2026-08-10` §2, with no new machinery. The TypeScript runtime reaches the
global-update reading in both cases, because its borrowed frame shares the
original cell *object*; frames-by-value cannot express that, and giving it up
would mean giving up the var-semantics theorem of `2026-08-10` §5.

*The proof requires the cells to travel.* The machine's obligation below
(`prepare_scope_can`) is false if `ParamF` is dropped: `param_in` would not be
preserved. Keeping the cells is not a convenience, it is what makes the
statement true.

### The owner: not borrowed

**The handler interpreting the scoped operation keeps its own return clause.**
This was got wrong once (a proposal to set every `ret` to `None` and restrict
scoped handlers to answer-preserving ones); it is wrong because the owner's
return clause is exactly the answer former `f` that lets `ndAll` report a
scope's result as `Array a`. Setting it to `None` makes `once` inexpressible and
so contradicts the milestone of `2026-08-06`. `machine.ts:469` confirms the
distinction: the owning prompt is pushed first, carrying both `handlers` and
`pure`, and the borrowed ones go on top in their original nesting.

The ordering works out. With head = innermost, a value leaving the scope passes
the borrowed intermediates (transparent, `ret = None`) and meets the owner
**last**, so the handler's answer transformation is applied exactly once, and
what the clause receives is `f x`.

Keeping `ret` is also cheaper than dropping it: the owner's tail in the woven
segment is the same as its tail in the original segment, so its `ret_ws`
obligation transports identically, with no congruence step. The intermediates'
dropped return clauses make their own obligations trivially true.

**`prepare_scope` introduces no new semantic premise.** The existing
`handler_ok` obligations of borrowed prompts are transported through
`prepare_scope_can` and `handler_ok_congr`; the owner's `ret_ws` obligation is
reused unchanged. That is a statement about *premises*, not about *work*:
removing the `BindF` frames changes each intermediate's tail, so the transport
is a real induction over the segment (see Decision 3 on why
`prepare_scope_can` has to hold at every suffix).

### Hazard: the segment must be the erased one, never the raw machine frames

The prompts to borrow are those the perform site could *see*, which is not the
same as those physically on the machine stack. They differ exactly while a
tail-resumptive clause body is in flight: the body runs with its own handler
masked out of the environment, and a scope opened from inside it must not see
that handler either.

In the reference semantics this is automatic — the desugaring
`Fast c ↦ fun args k -> Op (afast c args) k` really does cut the stack, so a
masked prompt is inside a `BindF (kont_of captured)` closure and simply is not
in `captured`. On the machine it is not automatic: the frames are still there,
under an `MEnvF`. The borrowed segment must therefore be derived from the
*erased* view (what `msplit` / `erase_k` already produce) or, equivalently, from
the evidence environment — never by walking `mstack` directly.

### Which input is authoritative

```text
raw mstack        ✗  wrong, and wrong by returning an answer
environment       ✓  correct, but redundant here
msplit captured   ✓  correct, and already required
```

**The initial implementation should take the `msplit` result.** A scoped clause
receives a `Cont`, so dispatch captures the continuation exactly as a full
clause does, so `msplit_fast` runs whatever else happens; and what it returns is
already the view this hazard demands —

```fstar
let captured, below      = msplit_fast eff op kk       // captured : rstack, erased
let intermediates, owner = split_last_prompt captured
let prepared             = prepare_scope intermediates owner
```

Masked prompts are absent from `captured` because `erase_k` has already absorbed
them into a `BindF (kont_of ...)`, and `prepare_scope` drops `BindF`, so they
cannot re-enter the borrowed context. `progFastInFlight`'s requirement is met
with nothing written for it.

The agreement between the two machines is free: `msplit_agrees` already gives
propositional equality of the machine's `captured` and the reference's, and
`prepare_scope` is a pure function, so equal inputs give equal outputs by
congruence. There is no new lemma of the `msplit_agrees` family to prove.

`Hoop.Runtime.Env.prompts_between` is an **alternative** machine-side source of
the same visible context, and is in the interface for this purpose (see its
comment there). It becomes worth taking only if scoped dispatch later stops
building a captured segment — a fast path that acquires the borrowed context
without capturing a continuation, or an evidence-derived scope context. The two
consequences below are conditions *on that choice*, not work for the initial
implementation:

- the environment view is outermost-first and includes the owner, while the
  reference stack is innermost-first with the owner last, so the order has to be
  converted and the two constructions proved to agree;
- `prompts_between` is currently `noextract` "for as long as no transition calls
  it", and is written with `firstn` at `int`. A live transition extracts it, and
  no negative value can arise at run time, but the type is signed — so **build
  guard (a) fires unless `firstn`, `view_firstn_payloads` and friends are
  re-typed at `nat`**, with the depth inequality discharged from `outer_of`.

### Where the fixture has to run

`progFastInFlight` is not a reference-machine fixture. The reference machine
uses the right `captured` by construction and cannot reproduce the fault, so a
reference-only test would pass while the shipped runtime returned 8. It is
needed in at least two places:

- an F\* fixture that runs the **optimized** machine directly (`msteps`), beside
  the existing `Hoop.Runtime.Test` fixtures;
- a smoke test through the **shipped JavaScript**, in `test/js/`.

Both checked non-vacuous by perturbing the expected `Right 101` to `Right 8` —
the value the raw-frame construction produces — and confirming the fixture
fails.

No new frame constructor is introduced. The two roles are made visible in the
*signature* of the function instead:

```fstar
val prepare_scope
  : (intermediates: rstack v cl)
 -> (owner: rframe v cl { PromptF? owner })
 -> rstack v cl
```

---

## Decision 3 — `weave` stays a rank-2 capability; pre-weaving is retracted

**Taken. This section records a retracted proposal, because it is one that will
be proposed again.**

### The retracted proposal

That the machine weave every inner computation *before* dispatch and hand the
clause ordinary values, removing `weave` from the clause signature entirely.
Its attraction: no rank-2 capability, no skolem row, the clause signature keeps
the continuation last with no extra argument, and — the reason it was proposed —
the inner computations would be visible to `ws`, so `progress` would survive
without a new boundary assumption.

### Why it is wrong

**The runtime cannot find the inner computations.** A scoped payload is
`h (Hoop inner) b` — a *user-defined* higher-order signature (`OnceScope p` and
the like). The machine sees one opaque value and has no idea where inside it the
computations are. Locating them needs a structural traversal, i.e. `hmap`, i.e.
precisely the `HFunctor` obligation that `2026-08-06` identifies as the thing
this design removes. Pre-weaving would buy a proof convenience at the cost of
the research claim.

So the clause destructures `h` itself and applies `weave` to whichever
computation it selects — and the rigid `inner` row keeps its job, which is to
make "you may only run an inner computation through `weave`" a type error rather
than a convention.

### What this costs, and where it is paid

Because `weave` is applied by the clause to a value F\* cannot see, `ws` cannot
constrain the inner computation, and the well-scopedness of a scoped clause's
result becomes a boundary assumption — of exactly the same character as the
existing `apply_ok`, which already assumes rather than proves that a clause uses
`kf` properly. The two environments are quantified as ghost indices rather than
computed inside the predicate:

```fstar
let weave_ok cok (can_site can_clause: can_perform) (weave: comp_tree v cl -> comp_tree v cl) : prop =
  forall (d: comp_tree v cl). ws cok can_site d ==> ws cok can_clause (weave d)

let apply_scoped_ok (apply_s: scoped_apply_t v cl) (cok: clause_ok_t cl) : prop =
  forall (can_site can_clause: can_perform) (c: cl) (payload: list v)
         (weave: comp_tree v cl -> comp_tree v cl) (kf: v -> comp_tree v cl).
    cok can_clause c /\
    (forall (x: v). ws cok can_clause (kf x)) /\
    weave_ok cok can_site can_clause weave
    ==> ws cok can_clause (apply_s c payload weave kf)
```

At the transition these are instantiated with

```fstar
let can_clause = can_in_with below base in          // base = can_nothing () in a machine state
let can_site   = can_in_with captured can_clause in // captured == intermediates @ [owner]
```

(`base` is worth quantifying in the general lemmas even though it is
`can_nothing ()` in any reachable state.)

**The split of responsibility is the point:**

| | |
|---|---|
| the machine **proves** | `weave` maps a computation well scoped at the perform site to one well scoped in the clause's context |
| the FFI/PureScript boundary **assumes** | a scoped clause applies `weave` only to computations drawn from its rigid inner family |

The machine's half rests on two lemmas:

```fstar
val prepare_scope_can : equiv_can (can_in_with prepared can) (can_in_with (intermediates @ [owner]) can)
val prepare_scope_wf  : wf_stack cok can (intermediates @ [owner]) ==> wf_stack cok can prepared
```

from which `weave_ok` follows via `ws_splice`. Note that `prepare_scope_can` has
to be proved **for every suffix** of the segment, not only at the top:
`prepare_scope_wf` transports each borrowed prompt's `handler_ok` obligation
from its original tail to its borrowed tail through `handler_ok_congr`, and that
congruence needs the environments to agree at that position.

The assumption's justification is the rigid `inner` row, and it must not be
turned into an F\* ghost predicate over the shape of `h` — doing so would lose
payload-shape genericity again, by the back door. The README's trusted list
gains one line:

> A scoped clause applies the supplied rank-2 `weave` capability only to
> computations drawn from its rigid inner computation family.

This is a boundary assumption belonging to a new feature, so it does not
conflict with the stop rule of Decision 1, which concerns existing hypotheses
under a semantics-preserving refactor.

---

## Decision 4 — the answer former `f`, and what to call it

**Taken, in part.**

`weave : forall x. Hoop inner x -> Hoop r (f x)` is polymorphic in `x`, so `f`
is a genuine answer type *constructor* and the handler's answer decomposes as
`o ~ f b`. The owner's return clause is therefore a **polymorphic point** —
`forall x. x -> f x` — rather than the monomorphic `a -> o` the verified surface
currently builds.

*Called a polymorphic point, or a polymorphic family, and deliberately not a
natural transformation.* Naturality would need `f`'s functor structure and a
parametricity argument to be pinned down, and with `unsafeCoerce` available on
the PureScript side it is not a theorem obtainable from the types inside F\*.

The runtime is unaffected — the machine never inspects a type — so this is
entirely a surface obligation. `Hoop.Engine.BuildHandler` as it stands cannot
express it; the shape to port is the TypeScript-backed project's

```purescript
newtype HandlerF effh r f = HandlerF (forall effa b. Hoop effa b -> Hoop r (f b))

handlerScoped :: (forall b. Handler effh r b (f b)) -> HandlerF effh r f
```

(`purescript-hoop/src/Hoop/Engine.purs:186`).

Note that no rank-2 *record field* is needed: the polymorphism sits on the
handler, so under the family's `forall b` the `pure` field is the ordinary
monomorphic `b -> f b` at each instantiation. A handler carrying a scoped clause
does need a `pure` clause, though — without one `o ~ a` collapses `f` to the
identity and neither `catch` nor `ndAll` can be written.

*Keeping `HandlerF` and `withF` separate from the ordinary `Handler` / `with` is
a decision of the borrowable milestone only.* Whether the separation survives
generalisation is open — see "the general level" below.

---

## Decision 5 — when borrowability is checked

**Taken in outline; the failure representation is still open.**

**The check belongs at the point `weave` is used, not at dispatch of the scoped
operation.** A scoped clause is entitled to discard an inner computation —
`once` prunes candidates, `catch` does not take the branch it did not choose, a
clause may drop the scope and the continuation both — and a non-borrowable
prompt in a context that is never woven is no reason to reject anything. The
TypeScript runtime checks inside the `WEAVE` transition for this reason.

### The consequence that has to be recorded

**Borrowability is not discharged by PureScript's row types.** It is a property
of the handlers actually crossed at run time, and no static discipline in this
design decides it. The condition separating the guaranteed case from the rest is
not "does the program contain scoped operations" — a clause that discards a
scope never runs the check at all — but "was every weave that was actually
evaluated borrowable".

Decision 7 settles where that lands: in a **dedicated `Rejected` outcome**, not
in `Stuck`. The split is therefore

```text
well-scopedness                 -> never Stuck
typed-boundary compatibility    -> never Rejected
termination + both              -> Done
```

and the well-scopedness development is untouched. In particular
`prepare_scope_can`, `prepare_scope_wf` and `ws_weave` all hold **without any
borrowability hypothesis**: a `Weave` node that is going to be rejected is still
well scoped — it fires no action it lacks the capability for — so `weave_ok`,
and with it the third premise of `apply_scoped_ok`, is discharged
unconditionally. Borrowability is only the condition under which `Weave` takes
its success branch.

### What the check protects

Not `ws`, not progress, not the simulation. Over F\*'s single value type `v`, a
borrowed full clause has perfectly well-defined operational behaviour — it
captures a continuation that ends at its borrowed prompt — and
`prepare_scope_wf` transports its obligations whatever kind of clause it is.
None of the verified theorems needs borrowability.

What it protects is on the PureScript side: a borrowed full clause would deliver
a value at the scope's type where the clause's own answer type is expected. So
the check is a **dynamic boundary check for the type soundness of the
PureScript representation** — one of the trusted items, and one F\* does not
currently formalise. Calling it "just a legible error" understates it; calling
it a soundness condition of the machine overstates it.

Should a typed source semantics ever be introduced, this condition stops being a
courtesy and becomes either an assumption or a theorem of the source–runtime
correspondence.

The representation is Decision 7.

---

## Decision 6 — scoped dispatch is a dedicated `PerformS`

**Taken.**

> Scoped dispatch is represented by a dedicated `PerformS` constructor. A
> handler entry carries a `Scoped` tag, and a mismatch between the AST kind and
> the tag is an explicit boundary error. Borrowability is cached on the handler
> table, but its value is **derived inside F\* from the clause tags**, not
> supplied by the FFI. The ordinary `apply_ok` and the algebraicity of ordinary
> operations stay independent; the scoped side adds `apply_scoped_ok` and the
> minimal `apply_scoped_obs_congr` the monad laws need.

### Why, and why not the alternative

The alternative was to leave the AST alone and decide dispatch on the clause tag
after lookup. It is cheaper in two places — a mismatch is structurally
impossible, and `mstep` already branches on `Full` / `Fast` so `Scoped` is one
more arm rather than a new top-level one. It was rejected on two others:

- **It weakens an existing boundary hypothesis.** `apply` would only ever be
  called on non-scoped clauses, so `apply_ok` could no longer be assumed of
  every `c : cl`; it would have to be conditioned on `kind c != KScoped` (both
  `Full` and `Fast` travel the ordinary path). A new feature would be editing
  the hypothesis that covers programs which do not use it.
- **It entangles the laws.** `perform_algebraic` would silently range over
  performs whose clause happens to be scoped. That is probably still *true* —
  see the blindness lemma below — but proving it would pull `prepare_scope` into
  the algebraicity proof. With `PerformS` the statement does not mention the
  scoped case at all.

Two arguments advanced earlier for the node do **not** survive and are recorded
as withdrawn:

- *"`PerformS` keeps `cl` abstract in the reference."* False: the classifier the
  tag design needs is definable rather than trusted (the reference is
  instantiated at `clause cl` by the machine, exactly as `desugar` is), and the
  borrowability question does not need a classifier at all under the cache
  below.
- *"Inner computations must be in the AST for `ws` to see them."* Retracted in
  Decision 3. `PerformS` carries the same fields as `Perform`; the inner
  computations stay in the opaque payload. What the constructor marks is the
  *kind of the operation*, not the location of its arguments.

A field on `Perform` was not considered a serious alternative: `2026-08-10` §6
records the measurement (22 sites for a constructor against 94 for a field).

### The shape

```fstar
| Perform  : eff:string -> op:string -> payload:list v -> comp_tree v cl
| PerformS : eff:string -> op:string -> payload:list v -> comp_tree v cl
```

```fstar
apply_t        = cl -> list v -> (v -> comp_tree v cl) -> comp_tree v cl
scoped_apply_t = cl -> list v
              -> (comp_tree v cl -> comp_tree v cl)   // weave
              -> (v -> comp_tree v cl)                // continuation
              -> comp_tree v cl
```

`Hoop.Runtime.Semantics.step` takes both interpreters and gains one arm, which
splits `captured` into `intermediates @ [owner]` and builds
`weave = fun d -> Splice (prepare_scope intermediates owner) d`. The
borrowability check sits **inside `weave`**, not in the transition, which is
Decision 5.

`apply_t` is unchanged, and so is `apply_ok`.

### The laws are *not* unchanged — and that is the point

The comparison table earlier in the argument said "laws unchanged". That is
wrong as stated, and the correction belongs here because it is the honest form
of the advantage:

> The statement of ordinary algebraicity and the existing `apply_obs_congr` stay
> isolated. But the monad laws quantify over an arbitrary `m : comp_tree`, so
> they acquire a `PerformS` case, and with it a new obligation on the scoped
> interpreter.

`right_identity` and `associativity` are proved through `sim`
(`Hoop.Runtime.Laws.fst:539`), which must handle every operation `m` performs
while running. A scoped perform among them needs the counterpart of
`apply_obs_congr` (`Hoop.Runtime.Laws.fst:194`):

```text
resume1 and resume2 observationally equal to depth n
─────────────────────────────────────────────────────
applyS c payload weave resume1  and  applyS c payload weave resume2
                       equal to depth n
```

— that is, congruence **in the resume argument only, at a fixed `weave`**.

That this suffices rests on a blindness lemma, and the ground for it is already
there: `no_prompt d` (`Hoop.Runtime.Laws.fst:348`) says *every* frame of a
replaced block is a `BindF`, not merely that it holds no prompt. Since `borrow`
drops `BindF` and keeps everything else,

```fstar
val borrow_append     : borrow (a @ b) == borrow a @ borrow b
val borrow_no_prompt  : no_prompt d ==> borrow d == []
```

give `borrow (a @ d @ b) == borrow (a @ b)`: the two sides of a law produce
**literally the same** prepared segment, because prompts live only in `pre` and
`post` and the block between them contributes nothing. Two short inductions.

Acceptance criteria for this part:

1. prove the blindness lemma above;
2. conclude that both sides of a law build the same `weave`;
3. keep `apply_scoped_obs_congr` to resume-congruence at a fixed `weave`;
4. **stop and return to the design if observational congruence in `weave`
   itself is required as a new boundary assumption.**

### The `Scoped` tag is mandatory, not defence in depth

The AST alone selects the interpreter, so the tag is not needed for dispatch.
It is needed to keep the shipped runtime *total* in the presence of two
mismatches:

- a `PerformS` reaching a `Full` or `Fast` entry;
- a `Perform` reaching a `Scoped` entry.

The PureScript surface rules both out — the operation signature is the single
source of truth from which both the perform site and the clause's canonical type
are derived — but the runtime cannot assume it. The tag's three roles:

- unwrap to the right interpreter safely;
- turn a broken type boundary into an explicit rejection rather than a wrong
  answer;
- keep the F\* entry point total.

This failure is a different thing from an unhandled operation's `Stuck`, and
belongs on whatever dedicated rejected outcome Decision 5 settles on.

### Borrowability: cached, but derived in F\*

The cache must not arrive from the FFI. A `mk_handlers` taking a boolean would
let the handwritten TCB build

```text
clauses    = [Full ...; Fast ...]
borrowable = true
```

— a new trusted input, and one whose failure mode is silent. Derive it instead:

```fstar
borrowable_clause (Fast _)   = true
borrowable_clause (Full _)   = false
borrowable_clause (Scoped _) = false

borrowable hs = forall e. e `memP` table hs ==> borrowable_clause e.clause
```

folded once at `mk_handlers` time and cached, with the interface pinning the
cache to the view exactly as `keys` is pinned. The reference machine asks
`borrowable hs` and never inspects a `cl`.

So the finding that opened this section is recorded as: *no classifier is needed
to decide borrowability — but the correctness of the cache is derived on the
verified side from the clause tags, never asserted at the boundary.*

### Postscript: what "scoped operations are not algebraic" can and cannot mean here

Two different axes, and only one of them is expressible in the generic core:

| axis | statement | expressible? |
|---|---|---|
| the **inner** computation | `catch (m >>= k)` vs `catch m >>= k` | **no** — the inner computation sits inside an opaque payload (Decision 3), so `m >>= k` cannot be built inside F\* |
| the **outer** continuation | `(op(..) >>= cont) >>= k` vs `op(..) >>= (fun x -> cont x >>= k)` | yes, and it may well *hold* for scoped operations too, by the blindness lemma above |

`PerformS` lets these be stated separately — `perform_algebraic` and, if it is
proved, `performS_outer_algebraic`. What must **not** be claimed is that the
non-algebraicity of scoped operations has been proved: the axis on which they
fail to be algebraic is the one payload-shape genericity puts out of reach. That
is a cost of Decision 3, and it is the price of not requiring an `HFunctor`.

---

## Decision 7 — a dedicated `Rejected` outcome, and an internal `Weave` node

**Taken.**

> Boundary failures are represented by a dedicated terminal `Rejected` state,
> distinct from `Stuck`. Scoped weaving is represented by an internal `Weave`
> node carrying a normalized scope plan. Kind/tag mismatches reject directly
> during perform dispatch; borrowability violations reject when the `Weave` node
> is evaluated. Well-scopedness rules out `Stuck`, while a separate
> boundary-compatibility condition rules out `Rejected`.

### The shape

```fstar
type operation_kind = KOrdinaryOperation | KScopedOperation   // read off the AST node
type clause_kind    = KFull | KFast | KScoped                 // read off the table entry

type rejection =
  | ClauseKindMismatch : eff:string -> op:string
                      -> expected:operation_kind -> actual:clause_kind -> rejection
  | UnborrowableScope  : eff:string -> op:string
                      -> blocking_effects:list string -> rejection

type state v cl =
  | Done     : v -> state v cl
  | Step     : comp_tree v cl -> stack v cl -> state v cl
  | Stuck    : string -> string -> state v cl
  | Rejected : rejection -> state v cl

| Weave : origin_eff:string -> origin_op:string
       -> prepared:stack v cl -> body:comp_tree v cl -> comp_tree v cl
```

```text
Perform / PerformS disagreeing with the entry's clause kind
  -> Rejected (ClauseKindMismatch ...)

Weave prepared body
  -> if borrowable_prefix prepared then Step body (prepared @ k)
                                   else Rejected (UnborrowableScope ...)
```

Well-scopedness of the node carries no borrowability condition at all:

```fstar
ws cok can (Weave prepared body)
  = wf_stack cok can prepared /\ ws cok (can_in_with prepared can) body
```

so the success branch is `ws_splice` and the reject branch is
`wf_state (Rejected _) = True`. **Preservation is unconditional on both.**

### Why not a reserved effect name on `Stuck`

`Stuck` means one thing throughout the development: **a required dynamic
capability is absent** — an unhandled operation, or a `read`/`write` with no
`ParamF` to reach. `wf_state` (`Hoop.Runtime.WellScopedness.fsti:316`) sets
`Stuck` to `False`, and its unreachability is *proved* from well-scopedness.

The failures here are not of that kind. The operation is handled; `prepare_scope`
is perfectly well defined over F\*'s single value type; what cannot be
guaranteed is the answer-type agreement PureScript assumes. Folding them into
`Stuck` under a reserved name would inject borrowability and kind/tag agreement
into a theorem that currently says something else, undoing the split Decision 5
was written to establish. With a separate state the two axes stay orthogonal,
and `wf_state` gains the honest arm

```fstar
| Rejected _ -> True
```

`wf_state` guarantees that a machine does not halt for want of a capability;
type agreement of the PureScript representation is a different predicate and a
different trusted item.

The visible consequence is that `execute`'s guarded conjunct becomes

```text
never_stuck /\ never_rejected  ==>  MDone
```

This is not a retreat. The failure axis it names did not exist before scoped
operations, and stating it separately is what keeps the old guarantee exactly as
strong as it was.

### Why the node

If `weave` returned a `Splice` directly, expressing a borrowability failure
would still need either an internal reject node or a reserved-name `Perform`.
Making `Weave` explicit puts Decision 5's meaning straight into the transition
rules:

- the check runs when the woven computation is *evaluated*;
- a clause that never calls `weave` is never checked;
- a clause that builds a woven computation and does not run it is not rejected;
- `prepare_scope`'s result is installed on the stack only on success.

And the two rejections stay unmixed: kind/tag mismatch arises at the perform
transition, borrowability at the `Weave` transition.

### The *execution-relevant* component must be normalized, not raw

`Weave` must **not** carry the raw captured segment. The two sides of a monad
law differ by the extra `BindF` frames of the law's redex block; `prepare_scope`
erases that difference, but a raw segment stored in the node would not, and the
two sides would build syntactically different `weave` functions — for which the
minimal `apply_scoped_obs_congr` of Decision 6 would no longer suffice.

Carrying the prepared stack gives, with the blindness lemma of Decision 6,

```text
prepared (pre @ d1 @ rest) owner  ==  prepared (pre @ d2 @ rest) owner
```

for `no_prompt d1`, `no_prompt d2` — hence the same prepared stack, the same
borrowability verdict, the same rejection payload, and therefore *the same weave
function*. The congruence obligation stays confined to the resume continuation.

**But "normalized" is a condition on the stack, and it was wrongly read as a
reason to carry nothing else.** That cost the diagnostic: `UnborrowableScope`'s
`eff` / `op` came out as `""`, because by the time a `Weave` is evaluated there
is no operation left to name — and a node that may be evaluated far from the
dispatch that built it is exactly the node that has to remember its origin.

```fstar
| Weave : origin_eff:string -> origin_op:string
       -> prepared:stack v cl -> body:comp_tree v cl -> comp_tree v cl
```

The provenance is inert: `ws` ignores it, `prepare_blind` is about the segment,
and on both sides of a law the origin is the same pair of strings — the redex
block a law replaces is `no_prompt` and contributes to none of the three fields.
So the weave function depends on the origin *and* the prepared segment, and both
are identical across a law. No new hypothesis.

The lesson generalises: **normalize what execution depends on; keep what
diagnosis depends on.** Conflating the two is what produced an error message
that could not name its own operation.

`borrowed` was considered as a second field and left out: `prepared` is
`borrow intermediates @ [owner]`, so the borrowed prompts are exactly
`init prepared`, and a stored copy would only add a consistency invariant. A
record `scope_plan` becomes worth having if a second genuinely normalized
component appears.

### The classifier gap this exposes, and how it is closed

Decision 6 wrote `borrowable_clause (Fast _) = true | ...`. That typechecks only
where `cl` is `clause cl0` — i.e. in `Hoop.Runtime`, not in the `cl`-polymorphic
`Handlers`, which cannot see a tag. The same objection hits
`ClauseKindMismatch`'s `actual` field, which `Hoop.Runtime.Semantics` could not
name either.

Closed by taking the classifier **once, at table construction**:

```fstar
val mk_handlers (#cl: Type) (classify: cl -> clause_kind) (entries: list (entry cl))
  : Tot (handlers cl)
```

and fixing it on the shipping path in the layer that owns the tags:

```fstar
let classify_runtime_clause #cl (c: clause cl) : clause_kind =
  match c with Full _ -> KFull | Fast _ -> KFast | Scoped _ -> KScoped

let mk_runtime_handlers entries = mk_handlers classify_runtime_clause entries
```

**`classify` must not come from the FFI**, or the trusted input returns in
functional form (`fun _ -> KFast`). Only `mk_runtime_handlers` is exposed, and
guard (e)'s whitelist is **extended beyond `Hoop_Runtime_Syntax` to
`Hoop_Runtime_Handlers.mk_handlers`**, which `hoop_ffi.ml` currently calls
directly. That extension is on its own a sufficient reason for the `Api.fsti`
promotion.

With `clause_kind` a flat enumeration, `rejection` lives in
`Hoop.Runtime.Semantics` beside `state`, and both machines share it —
`erase_st (MRejected e) == Some (Rejected e)`.

#### Lookup returns the clause and its kind together

Asking `lookup_clause` and then `clause_kind_of` searches the same table twice on
the dispatch path. One projection instead:

```fstar
type found_clause cl = { body : cl; kind : clause_kind }

val lookup_handler (#cl: Type) (hs: handlers cl) (eff op: string)
  : Tot (option (found_clause cl))
// pinned by:
//   lookup_handler (mk_handlers classify entries) eff op
//     == map_opt (fun c -> { body = c; kind = classify c }) (assoc_clause entries eff op)
```

`lookup_clause` stays as `map_opt (fun f -> f.body) (lookup_handler hs eff op)`,
so nothing downstream is restated. `find_prompt` carries a `found_clause`, which
makes the agreement between a clause and its actual kind structural rather than
a second lookup that could disagree.

*Cost:* `find_prompt`'s result type changes in one component, so its three
correctness lemmas (`find_prompt_partitions` / `_last` / `_innermost`),
`msplit` / `msplit_ok` / `msplit_agrees`, and the `fp_*` family in
`Hoop.Runtime` are all touched. The arguments are unchanged; the types are not.

#### Cache the blockers, not a boolean

An error names the effect labels that blocked the borrow, so caching a `bool`
beside a label list would create a consistency obligation between them. Cache
only the list:

```fstar
val blocking_effects (#cl: Type) (hs: handlers cl)
  : Tot (l: list string {
      forall eff. eff `mem` l <==>
        (exists op found. lookup_handler hs eff op == Some found /\ found.kind =!= KFast)
    })

let borrowable hs = Nil? (blocking_effects hs)
```

Stated through `lookup_handler` rather than through `classify` applied to the
table, for three reasons: no `classify_of : handlers cl -> cl -> clause_kind`
has to be added to and kept in the abstract interface; the correspondence
between a clause and its kind is already structural inside `found_clause`; and
for an entry list with duplicate keys it judges **only the entry that would
actually be dispatched**, since `lookup_handler` is first-match. A shadowed
`Full` clause is invisible to `lookup_clause`, to `clause_memP` and hence to
`handler_ok`, so it is right that it should not block a borrow either.

`classify` is then confined to the construction refinement

```fstar
lookup_handler (mk_handlers classify entries) eff op
  == map_opt (fun c -> { body = c; kind = classify c }) (assoc_clause entries eff op)
```

and everything else is defined from the public specification. From the two,

```fstar
borrowable hs <==> (forall eff op found. lookup_handler hs eff op == Some found ==> found.kind == KFast)
```

Pinned **as a set**, exactly as `keys` is, so a realisation building it per
effect group may dedup and reorder. Success reads one emptiness test; failure
hands the list straight to the message; and there is no boolean that can
disagree with the offenders.

*Cached or not — the initial realisation is on demand.* This section originally
said "cache". What shipped computes `blocking_effects` when asked. **Initial
realisation: computed on demand, until `Weave` provides a real access pattern
and a benchmark.** Caching at `mk_handlers` time would put a walk on every
`Handle` — the operation `benchmarks/src/Benchmarks/CatchInstall.purs` measures,
and one that a closure-capturing `catch` pays on every call — to precompute an
answer nothing asks for yet. If `Weave` turns out to be frequent, the same
table's answer gets recomputed repeatedly and the trade reverses. The refinement
is identical either way, so it can become a field with nothing downstream to
revisit; this is a realisation choice, not a decision.

#### The borrow check is one pass over `prepared`

`borrowable_prefix` / `blocking_prefix` inspect every `PromptF` **but the last**
— the owner is not borrowed. `BindF` cannot occur (the stack is normalized) and
`ParamF` does not bear on borrowability. Both are kept **total on an arbitrary
`prepared`**; that a real `prepared` is `borrow intermediates @ [owner]`, and
hence that `init prepared` is the borrowed part and `last prepared` the owner,
is a lemma about the `weave_of` generation path rather than a refinement on the
constructor. The FFI cannot build a `Weave` (guard (e)), so no other path
exists.

### What the laws observe, and what they do not

`converges` is `exists n. steps apply n s == Done x` (`Hoop.Runtime.Laws.fst:63`):
the only observation is convergence to a value. `Stuck` and divergence are
already indistinguishable at that granularity, and `Rejected` joins them. So no
law statement changes, and treating a rejection as simply "does not converge" is
the consistent reading for the initial implementation.

The existing `obs_eq` is therefore a **success-only (value-convergence)
observational equivalence**, and it is worth calling it that in the source. The
consequence, recorded so that it is not later mistaken for a new hole: a law can
be satisfied by **both sides rejecting**. That is a deliberate coarseness of
this observation, pre-existing — mutual `Stuck` already does it — and `Rejected`
adds an inhabitant to it rather than a failure mode.

If the errors ever need observing, **add a separate `outcome_obs_eq` rather than
strengthening `obs_eq`**: the current relation is what every law and every
transported result is stated in, and strengthening it in place would reopen all
of them at once.

### Cost

A state constructor, reached by everything that case-analyses a state: `steps`
and `steps_terminal`, `no_more_steps`, the `never_*` predicates, `erase_st` and
`msim`, `mrun` / `execute`, and one more arm in `hoop_ffi.ml`'s `run_impl` —
where it becomes the message naming the blocking handlers. Plus the
`found_clause` retyping listed above.

**+1,299 bytes of provisional rejection diagnostics** in the shipped bundle
(13,023 → 14,322), for an outcome nothing produces yet. The FFI *arm* is
unavoidable — under `-w -a` an incomplete match compiles and raises
`Match_failure` at run time — but the length of the two messages is not.
**Revisit at the slice that makes rejection reachable**, together with the
diagnostic fixtures: that is when it is known which parts of the explanation a
user actually needs at the point of failure, and which belong here and in the
surface docs instead. The 60 KB budget is comfortable, which is a reason not to
hurry and not a reason to keep prose in the runtime.

One wording correction was made straight away, because it was wrong rather than
merely long. The message said borrowing is *"only sound when every clause is
tail-resumptive"*, which reads as a general impossibility; re-instantiating a
full prompt across a scope is precisely the research goal. It now says the
**current implementation** can reinstall a prompt only when its clauses are
independent of the answer type, and that a full one would need re-instantiation
at the scope's result type, which is not supported yet.

### Confirmed form

- `Rejected rejection` is a fourth terminal state, distinct from `Stuck`.
- `wf_state (Rejected _) = True`.
- `Weave prepared body` is well scoped unconditionally.
- Borrowability is the condition on `Weave`'s success transition, and appears in
  neither `ws` nor `apply_scoped_ok`.
- `Handlers.mk_handlers` takes a classifier; the shipping path fixes it through
  `Hoop.Runtime`'s verified wrapper, and guard (e) forbids the direct call.
- Runtime lookup returns the clause and its kind together.
- `Weave` holds only the normalized `prepared`; the borrowed part is its prefix
  up to the owner.
- Offender information comes from a `blocking_effects` cache, from which
  `borrowable` is derived — no independent boolean.
- `never_stuck` and `never_rejected` are stated separately, and
  `execute` guarantees `MDone` under both.

---

## Decision 8 — the jsoo backend is retired

**Taken.** A project decision rather than a semantic one, recorded here because
it gates the implementation and because PR #1 asked for it explicitly:

> every change to the machine — scoped effects will add nodes — means editing
> two boundaries. Worth deciding whether jsoo stays maintained or becomes frozen
> before that work starts.

That work is this work. Counting what the decisions above put through a
boundary: three AST constructors (`Splice` replacing `Resumed`, `PerformS`,
`Weave`), a state constructor (`Rejected` / `MRejected`, hence an arm in
`run_impl`), three builders (`performScopedImpl`, `mkScopedClauseImpl`,
`mk_runtime_handlers`), one interpreter (`apply_scoped`) and two error messages.
Twice.

And the guards do not tolerate a half-done second boundary: Decision 7's
`mk_runtime_handlers` exists so the FFI cannot call `mk_handlers` with its own
classifier, which is worth nothing if one of the two boundaries still can.

The reasoning is PR #1's own — Melange wins on all three of its metrics — plus
one about the audience: the users of this library are PureScript engineers who
may well care that the runtime is verified in F\*, and are unlikely to care how
the OCaml reaches JavaScript. Backend independence is not a claim worth paying a
recurring tax for.

**Retired, not frozen** — the word matters, because "frozen" suggests a build
path that keeps working and merely stops gaining features, and that is not what
would happen.

> The jsoo boundary directly constructs selected AST nodes and destructs machine
> outcomes. Future datatype changes therefore require it to be audited and
> updated; otherwise the backend may fail to compile or, more dangerously,
> continue compiling with an incomplete runtime interpretation.

The second half is the real hazard, and it is not hypothetical: both backends
compiled with `-w -a` (the `compile_flags` of the generated dune stanza in
`scripts/build-runtime.sh`, and the same flag on the retired jsoo `ocamlc`
line), so a non-exhaustive match compiles silently and
fails at run time with `Match_failure`. Adding `MRejected` to `mstate` is
exactly that case. Conversely, `Resumed → Splice` would very likely compile
untouched, since the jsoo boundary never names that constructor — so "the first
constructor change breaks the build" is false in both directions, and an
unaudited second boundary is a silent-failure risk rather than a loud one.

**A separate commit, immediately before Decision 1.** Not the same commit. The
retirement is a build change with no semantic content, which unlocks an
unusually strong acceptance condition: **the generated `src/Hoop/Engine.js` must
be byte-identical to PR #1's Melange output.** Doing it together with a
semantics change would forfeit that check exactly when it is most useful.

Acceptance conditions for the retirement commit:

- `src/Hoop/Engine.js` byte-identical to the current Melange output;
- every F\* module verifies;
- JS smoke suite 63/63;
- PureScript suite 22/22;
- Melange build succeeds in a clean Nix environment;
- `ocaml`, `findlib`, `zarith` and the js_of_ocaml packages tried against the
  devShell **one at a time, each measured**, rather than dropped as a block on
  the assumption that they were only there for jsoo;
- `BACKEND=jsoo` fails with an explicit "backend retired" message for at least a
  transition period, rather than an unknown-option error.

### The dependency measurement, as it came out

Two of the four expected removals did not survive contact. Recorded because the
expectation was wrong in a way that would otherwise be re-proposed:

| package | result |
|---|---|
| `js_of_ocaml-compiler`, `js_of_ocaml-ppx` | **removed** |
| `zarith` | **removed** |
| `ocaml` | **retained** — dune loads the OCaml compiler for its default context: `Error: Program ocamlc not found in the tree or in PATH` |
| `findlib` | **retained** — dune resolves `melange.ppx` through it: `Error: Library "melange.ppx" not found.` |

Both reasons are now comments in `flake.nix` beside the packages they justify.
`ppxlib` stays listed for the reason it was always listed: it used to arrive
only as a transitive dependency of `js_of_ocaml-ppx`.

**The measurement has to be run with the environment cut.** The first pass was
made by invoking `nix develop` from *inside* the devShell, which inherits the
parent `PATH`; `ocamlc`, `js_of_ocaml` and `ocamlfind` remained visible and all
four removals appeared to pass. `nix develop --ignore-environment` reverses two
of the four answers. A build that succeeds is not evidence that a package was
removable unless the tool it provides is provably absent from the shell.

What it buys immediately:

- guard (e)'s whitelist has one target instead of two, and the `Api.fsti`
  promotion pins one boundary rather than two — or, worse, one by type and one
  by grep;
- guard (c) loses its second backend-specific reading;
- two OCaml packages leave the devShell, though not the four expected.

**One hazard carried into the scoped work, and one non-hazard.** PR #1's first
hazard is that Melange flattens `let f a = fun b c -> ...` into a
three-argument JS function, so a boundary function that *returns* a function
must be written in JS.

- `mkScopedClauseImpl` **is** that case — it returns a function — and belongs in
  `hoop_prim.js` from the start, beside `mkFullClause` and `mkFastClause`.
- `apply_scoped` is **not**, merely because `weave` is a function *argument*:
  `apply_full` already takes the continuation `k` that way and works. Being
  flattened to four arguments may well be what is wanted. What needs measuring
  is only the implementation that hands `weave` across as a JS callback.

The hazard is about partially applied shapes reaching PureScript, and about
OCaml functions that return functions — not about function-typed arguments.

## A standing constraint: the shim fixes the vocabulary of extracted code

Found while implementing the lookup substrate, and recorded here because it will
be hit again in Decisions 6 and 7 — building a `Rejected`, walking
`borrowable_prefix` — and because the failure mode is a confusing build error
rather than anything that names the cause.

> **Every computational definition in an extracted module may use only
> operations the handwritten shim realises, even where JavaScript tree-shaking
> would later remove it.**

The "even where" is the part that surprises. The constraint bites at OCaml /
Melange typecheck and link time, which happens *before* esbuild decides what
survives; a definition nothing calls still has to compile. So "it gets tree-
shaken anyway" is not an argument.

What this cost in practice, in one small module:

| written naturally | why it fails | written instead |
|---|---|---|
| `Nil? xs` | extracts to `Prims.uu___is_Nil`, which `runtime/ml/shim/Prims.ml` does not realise | `match xs with [] -> true \| _ -> false` |
| `not b`, `a && b` | `op_Negation` and friends, likewise absent | explicit matches |
| `k <> KFast` | extracts to `caml_notequal`, a *generic* comparison — build guard (c) fires | a tag match |

The last one is the interesting one: it would not have failed to compile, it
would have failed the guard that exists to keep `caml_compare_val` out of the
bundle. The three constraints are of two different kinds — the shim's coverage
and the guards' — and both are the price of a small trusted base, which is the
right price to pay. It is worth knowing before writing rather than after.

## Prior art, checked against primary sources

Checked because an earlier round of this argument leaned on half-remembered
readings and got two of them wrong. Recorded with the sources so the next round
does not repeat it.

| system | what it actually does | bearing here |
|---|---|---|
| **Koka** | *Does* have scoped effects, using rank-2 polymorphism to prevent scope extrusion. Their purpose is the safe scoping of first-class named handlers / resources. ([OOPSLA'22](https://xnning.github.io/papers/oopsla22namedh.pdf)) | Not the same thing as a general higher-order operation whose inner computation is virtualized by a dynamically selected handler semantics. The rank-2 escape discipline is shared; the goal is not. |
| **Effekt** | Blocks are second-class computations whose effects bind to the *lexical* capabilities at the definition site; higher-order blocks pass region/subregion evidence. ([computation](https://effekt-lang.org/tour/computation), [lift inference](https://effekt-lang.org/docs/implementation/lift-inference), [captures](https://effekt-lang.org/tour/captures)) | A structurally different answer: nothing is reinstalled, because the inner computation carries its context lexically. The price is that the handler does not get to decide the inner computation's meaning. |
| **Flix** | Deep, dynamically scoped, multi-shot algebraic handlers with effect polymorphism. ([docs](https://doc.flix.dev/effects-and-handlers.html)) | No positive precedent for general higher-order operations was found. Not usable as support either way. |
| **Hefty Algebras** | Modular *elaboration* of higher-order effect trees into first-order algebraic effects — but it requires higher-order signatures together with elaboration algebras. ([TU Delft](https://research.tudelft.nl/en/publications/hefty-algebras-modular-elaboration-of-higher-order-effects/)) | The structural obligation is not removed, it is relocated into the elaborator. The contrast with `2026-08-06`'s hypothesis is real, but it is *where* the structure lives, not whether it exists. |
| **Heftia** | Does **not** eliminate `HFunctor`: new higher-order effects need `HFunctor`, `OrderOf` and friends, higher-order and first-order effect lists are kept apart, and delimited continuations carry restrictions. ([README](https://github.com/sayo-hs/heftia), [write-up](https://sayo-hs.github.io/jekyll/update/2024/09/04/how-the-heftia-extensible-effects-library-works.html)) | Same correction as above, in a shipping library. |
| **Polysemy `Tactical`** | The closest precedent for a context capability. Crucially the context functor is **not** a type argument the handler chooses — it is hidden under `forall f. Functor f => ...` and reached only through `runT` / `bindT` / `pureT` / `Inspector`. Note also what it is *not*: Polysemy's interpreters are answer-preserving, so there is one hidden functor and no separate owner layer; the hidden one threads the state other effects hold. ([hackage](https://hackage.haskell.org/package/polysemy-1.9.2.0/docs/Polysemy.html)) | This is the shape the general level has to take here, and it is why a `ctx` *type parameter* on `ScopedClause` is the wrong preparation. Hoop needs *two* layers, and conditions 1–3 show why. |

## Open — the general level: weaving an arbitrary prompt

Recorded now because it constrains what may be frozen at the borrowable
milestone, and because one attractive-looking shortcut has already been tried
and withdrawn.

> **A vocabulary note, fixed once.** This project uses `weave` and `ctx` for
> its own concepts — types, code, classification names, and prose about Hoop.
> The machine already has a `Weave` node and a `weave_of`, and the raw `weave` a
> scoped clause receives today is the trivial-`ctx` instance of the general
> capability; a second word for it here would be a synonym with no distinction
> behind it.
>
> **Prior work retains its source terminology.** `fused-effects` calls the
> corresponding algebra operation `thread`; Polysemy speaks of *functorial
> state* carried by `Tactical` / `runT` / `bindT`. These play analogous
> context-propagation roles, and each corresponds to Hoop's weave capability —
> but they are not definitionally the same operation, because their types and
> handler architectures differ:
>
> - `fused-effects`'s `thread` is a method passing an already-composed *outer*
>   context through an `Algebra`;
> - Polysemy's `Tactics` carry a hidden stateful environment moved by `runT` /
>   `bindT`, as an internal effect;
> - Hoop's `weave` is the capability — and the machine transition — that
>   re-establishes the dynamic prompt context between the perform site and the
>   owner around a scoped computation.
>
> The roles correspond; the inputs, outputs and responsibility boundaries do
> not. So the correspondence is stated once, here, and the literature is quoted
> in its own words thereafter.

### Withdrawn: "keep `ret` on the intermediates and it generalises"

Operationally the transition is definable — over F\*'s single value type `v`,
`PromptF hs ret` in a borrowed position steps perfectly well. It does not
generalise the *surface*, because a `PromptF` holds a table built at one
concrete answer type. Running an inner computation at an unknown `x` does not
need the existing table reused; it needs the **handler family re-instantiated at
`x`**, and polymorphising `ret` alone re-instantiates neither the `Cont` in a
full clause nor its answer type. So the general level needs one of

- prompts holding a polymorphic handler *factory* rather than a table;
- borrowed prompts rebuilt from a general WEAVE CAPABILITY -- the ability to
  re-enter an intervening handler at an unknown answer type. The raw `weave` a
  scoped clause is handed today is its trivial-`ctx` instance;
- explicit generalized forwarding, as the scoped calculus requires for passing
  an unknown scoped operation through another handler
  ([LMCS](https://lmcs.episciences.org/14832/pdf)).

That is a change to the typed representation of a prompt, not a line of
`borrow`.

### What borrowability actually is

The existing surface already states the criterion, and it is sharper than
"tail-resumptive":

```purescript
FullSignature (a ->* b) r o (a -> Cont b r o -> Hoop r o)   -- mentions o twice
FastSignature (a ->* b) r o (a -> Hoop r b)                 -- does not mention o
```

(the `FullSignature` / `FastSignature` base instances in this repository's
`src/Hoop/Engine.purs`; the TypeScript-backed project's are identical.)

> **In the current representation, a stored handler component is borrowable
> without re-instantiation exactly when its canonical type is independent of the
> answer type `o`.** Resuming in place is a consequence, not the reason.

The qualifications are load-bearing and the claim should not be shortened past
them. It is a statement about *reuse of the stored representation*, not a
semantic characterisation of which handlers could in principle be woven. A full
clause that discards its continuation behaves, operationally, exactly as a
borrowable one — and is still excluded, because its canonical type mentions `o`
and so cannot be reused at an unknown answer type under the present discipline.

Keeping the distinction is what stops `borrow` and a future factory from being
confused: a full clause under a factory does not become "borrowable unchanged",
it becomes **re-instantiable at an unknown `o`**. Two different properties, and
only the first is what `borrow` tests today.

Two things follow. **Dropping `ret` on the intermediates is forced, not an
approximation** — `pure : a -> o` mentions `o`, a fast clause does not, and a
cell's type does not; so the same single criterion keeps the `ParamF`, keeps the
fast clauses, and drops the return clause. `borrow`'s three lines are one rule.
And in any future factory design, **only the `o`-dependent parts need
re-instantiating** — the full clauses and the return clause — which narrows the
three options above.

### The context, and its direction

With intermediates that do transform the answer, a value leaving the scope
passes the intermediates' return clauses innermost-first and the owner's last:

```text
x  →  f_innermost x  →  …  →  ctx x  →  f_owner (ctx x)
```

so the woven result is `f (ctx x)` and **not** `ctx (f x)`. For
`withF runExc (withF ndAll program)` that is `Either e (Array a)`, which is
exactly what makes `catch` still able to match the outer `Left` / `Right`. But
the success payload is `ctx x`, which cannot be handed to a `Cont x r o`
directly — hence a `bindT`-style weave capability is required, of the Polysemy
shape rather than a type parameter.

### Do not pre-drill the hole

An earlier proposal here was to add a `ctx` slot to `ScopedClause` now, so that
the generalisation would not rewrite every scoped clause. **Withdrawn.** The
intervening context varies per perform, so it is not a type argument a handler
author chooses; it is hidden inside the clause, and what is needed alongside it
is an algebra (`runT` / `bindT` / `pureT` / inspect), not a slot. A hole drilled
in the wrong place and the wrong direction is worse than no hole.

### The gate: a types-only prototype

Before any of the general-level questions are settled, build a **type-checking
only** `GeneralScopedClause` / `ScopeTactics` sketch against the existing
`progCatchAcrossNd`, used as a generalisation fixture rather than as a rejection
test:

```purescript
withF runExc (withF ndAll progCatchAcrossNd)
```

It must satisfy all five:

1. the woven scope has type `Either e (Array x)`;
2. `catch` can discriminate `Left` from `Right`;
3. each value in `Right xs` reaches the continuation in the right
   nondeterministic context;
4. `ndAll`'s table is correctly re-instantiated at the unknown `x`;
5. no `unsafeCoerce` is exposed outside the FFI.

**Condition 4 is the only discriminator** — 1 to 3 are satisfiable by several
shapes — so it should be written first. The natural home is the
TypeScript-backed project, where `runExc`, `ndAll` and the fixture already exist
and no verified runtime is disturbed.

Condition 4 should be a **pair** of fixtures, negative and positive:

- an `ndAll` table already built at a concrete answer type **cannot** be reused
  at an unknown `x` — this must fail to typecheck;
- the same `ndAll` **can** be rebuilt at `x` through a rank-2 factory or through
  the tactics capability — this must typecheck.

Without the negative half, a shape that happens to compile because something was
coerced would read as success. The pair is what identifies *what* supplies the
re-instantiation capability, rather than merely that something did.

### Condition 4: run, and answered

The sketch is `purescript-hoop/test/Test/ScopedGeneral.purs`. It typechecks and
runs nothing.

**Negative half.** `ndAllAtInt : Handler Nd1 r Int (Array Int)` is what a prompt
actually holds: the nondeterminism table built at one answer type. Reusing it at
a rigid `x` is rejected —

```text
[ERROR 1/1 TypesDoNotUnify]
  reinstateFromTable h comp = with h comp
  Could not match type  x2  with type  Int
  where x2 is a rigid type variable
```

**Positive half.** The same handler reached through `HandlerF` answers at that
same rigid `x`, and so does the concrete `ndAll` the suite already builds:

```purescript
reinstateFromFactory :: forall r x. HandlerF Nd1 r Array -> Hoop (ND r) x -> Hoop r (Array x)
reinstateFromFactory hf comp = withF hf comp        -- compiles
```

> **Re-instantiation is supplied by the rank-2 quantifier inside `HandlerF`, and
> by nothing else in the current design.**

It is already there for the *owning* handler of a scoped operation — that is
what `handlerScoped : (forall b. Handler effh r b (f b)) -> HandlerF effh r f`
is for, and its own doc comment says so: the whole clause table, return clause
included, has to be valid at every `b`. The general level needs the same thing
for the *intervening* prompts, which today hold tables.

**What this does not settle.** All three candidates of "Withdrawn: keep `ret`"
— factory, tactics, generalized forwarding — need a re-instantiation capability;
what the gate has shown is that such a capability must exist and that rank-2 is
how this design can express one. Whether the **prompt itself carries it**, or it
is derived from a separate context algebra, depends on conditions 1–3. Reading
this as "a `PromptF` holds a `HandlerF`" would be fixing the representation on
the strength of a question that has not been asked yet.

### An unasked finding: nothing forces a scoped handler through `handlerScoped`

Turned up by the negative half and worth recording separately, because it is
about the surface as it stands rather than about the generalisation.

`ndAllAtInt` carries a `scoped` clause and is a plain `Handler` — that
typechecks, since `ScopedSignature` decomposes `o ~ f b` as
`Array Int ~ Array Int`. It can also be **installed with ordinary `with`**, and
a scope may then run under it at a result type the table was never built for.
Both of these compile:

```purescript
probeInstall          :: forall r. Hoop (ND r) Int    -> Hoop r (Array Int)
probeInstall           = with ndAllAtInt

probeScopeAtOtherType :: forall r. Hoop (ND r) String -> Hoop r (Array Int)
probeScopeAtOtherType p = with ndAllAtInt (once p *> pure 1)
```

In the second, `weave` receives a `Hoop inner String` and its type promises
`Hoop r (Array String)`; the runtime honours that by reinstalling *this* table,
whose return clause is `Int -> Array Int`. Nothing is checked at run time,
because by then there are no types.

So `handlerScoped` is what makes a scoped-clause handler sound, and nothing
*requires* going through it.

> **Closed by the permission slice.** Both halves of the finding are now
> unreachable, by two independent mechanisms rather than one.
>
> *Permission.* A table carrying a scoped clause can only be built at
> `AllowScoped` — `PermitsClauses` refuses `Scoped h` under `AlgOnly`, naming
> the offending operation — and `with` demands `AlgOnly`. `probeInstall` no
> longer compiles; the fixture is `test-compile-fail/ScopedUnderWith.purs`.
>
> *Quantification.* `handlerScoped` takes `forall b. HHandler AllowScoped effh
> r b (f b)`, so a table pinned at one answer type cannot be passed to it —
> the rigid `b` is what refuses it. `test-compile-fail/MonomorphicFamily.purs`.
>
> The two are genuinely independent: permission alone would still admit a
> monomorphic `HHandler AllowScoped` if `handlerScoped` were rank-1, and
> quantification alone would still admit `with ndAllAtInt`. Neither subsumes
> the other, which is why both are pinned.
>
> Note what this does *not* establish. The clause still has to apply `weave`
> only to computations drawn from its own rigid inner family, and that remains
> an assumption of `Hoop.Runtime.WellScopedness.apply_scoped_ok` discharged by
> the rank-2 quantifier on `ScopedClause`, not a checked property of the FFI —
> see the note at `apply_scoped` in `runtime/ml/melange/hoop_ffi.ml`.

### The counterexample, run

Built and executed rather than argued. The table's return clause is made
type-specific and the scope is made to produce a *function*:

```purescript
ndDoubleAtInt :: forall r. Handler Nd1 r Int (Array Int)   -- pure: \n -> [ n * 2 ]

demoBroken :: Unit -> Array Int
demoBroken _ = run $ with ndDoubleAtInt do
  f <- once (pure (\n -> n + 1))     -- f :: Int -> Int, says the type
  pure (f 41)
```

```text
THREW: TypeError: f is not a function
```

`weave` reinstalls `ndDoubleAtInt`'s table, so the scope's value leaves through
`\n -> [n * 2]` applied to a closure; `f` is bound to the result. **No
`unsafeCoerce`, no `Partial`, no FFI anywhere in the program** — every line is
ordinary well-typed user code, and the representation of a typed value is
broken.

What this establishes, and what it does not:

- it **is** a type-soundness defect of the *surface API*;
- it is **not** a defect of the runtime semantics or of anything on the F\* side
  — the machine did exactly what it is specified to do;
- the cause is that `handler` admits a `scoped` clause at all.

**Confirmed requirement: ordinary handler construction must not admit scoped
clauses.** A `scoped` clause may only be reachable through the path that builds
a rank-2 family. The fix itself waits until conditions 1–3 fix the final shape
of `ScopedClause`, since that is what decides what the admitting path looks
like.

The fixture is `purescript-hoop/test/Test/ScopedGeneral.purs`, wired into the
suite. It asserts a **defect**, not a behaviour: when the surface is fixed,
`ndDoubleAtInt` stops compiling and the fixture has to be rewritten as a
should-not-typecheck comment. That is the intended way for it to fail.

### The three type-level roles, named

`h` has been written inline as `(Type -> Type) -> Type -> Type` throughout this
argument, which left the concept present but the *name* unrecorded. The
TypeScript-backed project already names it, and the verified surface should
carry the same two declarations, beside `Computation` / `->*` in
`src/Hoop/Types.purs:54`:

```purescript
type HSig = (Type -> Type) -> Type -> Type

foreign import data Scoped :: HSig -> Type
```

| | |
|---|---|
| `HSig` | the *kind* of a higher-order operation's payload shape |
| `h :: HSig` | a user-defined higher-order signature — `OnceScope`, `CatchScope e` |
| `m :: Type -> Type` | the inner computation constructor; `Hoop inner` at a real perform |
| `b :: Type` | the scoped operation's result type |
| `h m b :: Type` | the whole payload handed to the clause |
| `Scoped h :: Type` | the marker in an operation-signature row, distinguishing it from `a ->* b` |

```purescript
newtype OnceScope :: HSig
newtype OnceScope m a = OnceScope (m a)

newtype CatchScope :: Type -> HSig
newtype CatchScope e m a = CatchScope { try :: m a, recover :: e -> m a }
```

**`HSig` is not the `ctx` that was withdrawn above.** The three are distinct and
easy to conflate:

```text
h    operation payload shape             static; the operation author defines it
f    owning handler's answer former      static; the handler's own
ctx  dynamically intervening context     per-perform; NOT a parameter anyone chooses
```

`h` and `Scoped` are consequently unaffected by the generalisation gate — the
positioning table below already freezes "`Scoped h` in an operation signature" —
and may be fixed as public API now. What remains open is the final
`ScopedClause` type that *consumes* an `h`, and the tactics that handle `ctx`.
What was missing here was a name, not a piece of the design.

### Conditions 1–3: the context capability, derived rather than ported

The sketch is `purescript-hoop/test/Test/ScopedTactics.purs`. Derived by
rewriting the clause bodies that already exist — `catch`'s and `once`'s — against
an opaque context, and taking what they demanded. Nothing was ported from
Polysemy.

```purescript
type ScopeTactics f ctx inner r o =
  { runScope    :: forall x. Hoop inner x -> Hoop r (f (ctx x))
  , resumeScope :: forall x. ctx x -> Cont x r o -> Hoop r o
  }

newtype GeneralScopedClause h f r o = GeneralScopedClause
  ( forall b inner ctx
     . h (Hoop inner) b -> ScopeTactics f ctx inner r o -> Cont b r o -> Hoop r o )
```

`ctx` is bound by the clause's own `forall`: unnameable, uninspectable,
unchooseable — the status the dynamic handler context actually has. `f` stays a
parameter, so the clause can match on it.

Both clauses typecheck against exactly these two operations. `catch` keeps its
shape: `Left`/`Right` are still matched, the recovery is still woven, and
non-recapture is still the clause returning `Left e'`. The one change is the
success branch, `continue k a` becoming `resumeScope cx k`.

**Checked to fail, twice.** A shape that compiles proves nothing alone:

| probe | result |
|---|---|
| replace `resumeScope` with `continue k cx` | `Could not match type ctx2 b0 with type b0` — `ctx` really is opaque and `resumeScope` really is load-bearing |
| identify `f` with the hidden context (one functor, `runScope :: Hoop inner x -> Hoop r (ctx x)`) | `Could not match type Either t2 with type ctx4` — `catch` loses the ability to tell failure from success |

The second is the justification for the asymmetry, and it is worth stating
against Polysemy precisely. **Polysemy does not fold two layers into one; it has
only the hidden context functor.** Its interpreters are answer-preserving, so
there is no owner layer to keep apart, and the hidden functor is there to thread
the state *other* effects hold
([Tactical](https://hackage.haskell.org/package/polysemy/docs/Polysemy.html)).
The claim here is therefore not that Polysemy conflates something, but that
*Hoop must not*: identify the owner's answer former `f` with the hidden context
and `catch` stops being expressible. `f (ctx x)` — outer concrete and matchable,
inner opaque and only passable — is what keeps the operation writable.

**Why two operations and not four.** `pureT` was not demanded: neither clause
injects a value into a context. A general `bindT` was not demanded: the only
sequencing either clause performs on a context is handing it to the
continuation, which is `resumeScope`. An `Inspector` was not demanded and would
be actively wrong — it exists to look inside the hidden functor, and the whole
argument for `f (ctx x)` is that what a clause may look inside is `f`, which it
already can.

**Scope of this conclusion.** "Two operations suffice" is fixed as *the minimal
capability necessary and sufficient for the `catch` / `once` fragment*, and is
not a claim about scoped operations in general. The bind gate below may add a
third; it must not be read as overturning this one.

### The bind gate: run, and it added one operation

Same module. Dependent sequencing was isolated from `bracket` first, so that a
failure would be attributable to a missing operation rather than to resource
semantics.

**Criterion 1 — the two operations fail.** Writing `ThenScope`'s clause with
only `runScope` and `resumeScope` is rejected:

```text
[ERROR InfiniteType] An infinite type was inferred: ctx2 t0
  while trying to match type t1 with type t0
```

— `cxa :: ctx a` being asked to serve as the `a` that `next` consumes.

**Criteria 2–5 — one operation fixes it, and no more.**

```purescript
bindScope :: forall x y. ctx x -> (x -> Hoop inner y) -> Hoop r (f (ctx y))
```

typechecks the clause. Nothing that *observes* `ctx` was required (3); no
`pureScope` was required (4); and the distinction is in the types (5) —
`runScope` starts from the initial context, `bindScope` continues from the one a
preceding computation produced.

`bindScope` does **not** break the abstraction: its function argument is
`x -> Hoop inner y`, over the value rather than over `ctx x`. The clause still
never sees inside; the machine is what re-enters the intervening prompts and
applies the function there.

**Minimality.** The three roles do not overlap — `runScope` introduces a
context, `bindScope` extends one, `resumeScope` eliminates one onto the
continuation — and none is derivable from the others **parametrically, over
this interface**: `bindScope` needs a `ctx x` to start from and only `runScope`
produces one, while `runScope` is unreachable from `bindScope` without a
`pureScope` that nothing has asked for.

The qualification is load-bearing. What typechecking establishes is
underivability *by a clause that may use only what it is handed*. It says
nothing about the language at large, where `unsafeCoerce`, bottom, or simply
adding a `pureScope` would each change the answer. Absolute underivability is
not what was checked and should not be claimed.

So the capability is **three operations**, and the earlier "two suffice" stands
as exactly what it was scoped to: necessary and sufficient for the
`catch` / `once` fragment, which does no dependent sequencing.

### `bracket` demanded nothing further — and why that matters

Run as a pure expressiveness probe, `bracket alloc use release` typechecks with
the same three operations, because `use` and `release` are sequenced **inside
`Hoop inner`**:

```purescript
bindScope cres \res -> use res >>= \v -> release res >>= \_ -> pure v
```

One `bindScope`; the ordering is the inner monad's.

Two things follow, and both are worth recording.

*A trap for the surface documentation.* Sequencing them in the tactics layer
instead — two `bindScope` calls on the same `cres` — **also typechecks, and is
wrong**: it re-enters the intervening context twice, which for a
nondeterministic `ctx` duplicates branches.

*Release guarantees are a different problem, confirmed rather than assumed.*
Inner sequencing buys "release runs after use, if use returns normally". It
cannot buy "release runs even when use fails, or when the continuation is
abandoned" — no arrangement of these three operations expresses that. It needs
finalizer frames in the machine, **not a fourth tactic**.

And it is not an *async* problem, though the implementation milestone currently
sits in `2026-08-11-async-suspend-roadmap.md`. A finalizer is equally required
by a synchronous throw, by a clause that discards its continuation, and by a
multi-shot branch that abandons one of its copies — all of which this runtime
already has, with no suspension anywhere. **Resource-unwind semantics is
conceptually independent of asynchrony**; it is scheduled alongside cancellation
only because that is where the two must agree.

### The gate is closed

Nothing further to probe at the type level. What comes out of it, for the
production API:

| prototype | published as |
|---|---|
| `ScopeTacticsB` (three operations) | `ScopeTactics` |
| `GeneralScopedClauseB` | `ScopedClause` |
| `ScopeTactics` (two operations) | not published — kept as the record of what the `catch` / `once` fragment alone needs |

**And this does not make the borrowable milestone heavier.** There
`ctx ~ Identity`, so the three operations are implementable on prompt borrowing
exactly as it stands:

```purescript
runScope body    = weave body
bindScope cx g   = runScope (g cx)
resumeScope cx k = continue k cx
```

`Identity` vanishes at run time, so no cost is paid for the generality.
Publishing the three-operation shape now is what stops every scoped clause from
being rewritten when arbitrary prompt weaving arrives — at which point `ctx`
becomes a real intervening context, and the *machine-side* implementations of
`bindScope` and `resumeScope` become the research problem rather than the
surface.

### The gate as originally stated

`bracket alloc use release` is the shape that would force a general
`bindScope`, but it carries release guarantees, failure paths and continuation
capture along with it. Isolating the sequencing first keeps a failure
attributable:

```purescript
newtype ThenScope a m b = ThenScope { first :: m a, next :: a -> m b }
```

against the candidate

```purescript
bindScope :: forall x y. ctx x -> (x -> Hoop inner y) -> Hoop r (f (ctx y))
```

Acceptance criteria:

1. `runScope` + `resumeScope` alone **fail** — a `ctx x` cannot be handed to
   `x -> Hoop inner y`;
2. adding `bindScope` makes it typecheck;
3. no operation that *observes* `ctx` is required;
4. no `pureScope` is required;
5. the difference shows in the types: `runScope` starts from the initial
   context, `bindScope` continues from the one a preceding computation produced.

Only then `bracket`, where anything that goes wrong is attributable to release
semantics rather than to a missing bind.

### Positioning

Until that prototype typechecks, the borrowable milestone freezes only what
survives generalisation:

| frozen | still open |
|---|---|
| `Scoped h` in an operation signature | the final `ScopedClause` type |
| `performScoped :: h (Hoop eff) b -> Hoop eff b` | where `ctx` is quantified |
| `try` and `recover` both inside `h` | how `Cont` is used across `ctx` |
| the clause weaving a chosen recovery explicitly | whether `Handler` / `HandlerF` stay separate after generalisation |
| deriving ordinary vs scoped from the one signature | whether a prompt holds a table or a factory |
| keeping `HandlerF` / `withF` apart from the ordinary API | |

The last row is **a decision of the borrowable milestone, not the final
higher-order API**, and should be described that way wherever it appears.

## Implementation order

Fixed by a dependency split that happens to be clean:

1. **Retire the jsoo backend (Decision 8), as a commit of its own**, containing
   no semantic change — so that "`Engine.js` is byte-identical" is available as
   its acceptance condition.
2. **Decision 1 (`Resumed` → `Splice`), as its own commit.**
   `Splice fs body` is a lower-level
   execution primitive that survives *every* candidate for the general level —
   borrowable, factory, general weave capability, generalized forwarding — so
   nothing the gate decides can overturn it. Its stop rule (condition 5) is
   also the earliest available check on whether the existing laws and
   simulation really survive a generalised node, and that check is independent
   of everything else here.
3. **The types-only gate in the TypeScript-backed project**, condition 4 first,
   negative fixture before positive.
4. **Choose between table / factory / tactics** from what the gate shows.
5. **The surface API and the substance of Decisions 2–7.**

Steps 2 and 3 are independent and can run in parallel. Step 5 must not start
before step 4: `HandlerF`, `ScopedClause`, the prompt representation and the FFI
all depend on the answer, while `Splice` depends on none of it. What condition 4
moves is how `prepared` is built, whether a prompt holds a table or a factory,
and how the surface is typed — not the splice primitive underneath.

## Shipped — the borrowable milestone, as built

Step 5 is done. What follows is the record of what landed and, more usefully,
of the four places where the plan above did not survive contact with the
compiler. Each of those is a shape that would be re-invented by anyone
reworking this area, so the *reason* is recorded rather than only the outcome.

### The published surface

```purescript
-- Hoop.Types
kind HCapability ; AlgOnly ; AllowScoped        -- an open kind
Scoped :: HSig -> Type                          -- the operation-signature marker

-- Hoop.Engine
HHandler :: HCapability -> Row EffType -> Row EffType -> Type -> Type -> Type
type Handler effh r a o = HHandler AlgOnly effh r a o     -- unchanged for users
HandlerF effh r f                                          -- the family
handlerScoped :: (forall b. HHandler AllowScoped effh r b (f b)) -> HandlerF effh r f
withF         :: Row.Union effh effb effa => HandlerF effh effb f -> Hoop effa a -> Hoop effb (f a)

ScopeTactics f ctx inner r o    -- runScope / bindScope / resumeScope
ScopedClause h f r o ; scoped
performScoped   -- via PerformScopedList / PerformScopedEffect / PerformScopedOp
```

`ScopeTactics` and `ScopedClause` are published at the **general** shape the
bind gate settled on, not at a borrowable-only one. The milestone specialises
`ctx ~ Identity` in the engine's own `scopeTactics`; the clause is quantified
over `ctx` and cannot tell.

`Handler` remains a five-argument-free synonym, so every existing annotation
compiles unchanged, and the capability is not re-exported from `Hoop` — a user
never spells `AlgOnly` or `AllowScoped`.

### `capability` works because it is in the RESULT type

The first attempt threaded the capability through the classes that BUILD the
table (`BuildHandler` → `MkHandlers` → `MkHandlersList` → `ClauseFor`). It
fails: their methods do not mention it, so nothing at a use site determines it,
and the chain stalls on an unknown and reports a partial overlap instead of the
intended `Fail`.

The working shape is a **method-less predicate**, `PermitsClauses capability
effhL`, discharged from `handler`'s context. But "carrying no method" is *not*
the reason it works — a method-less class stalls just the same when its index is
undetermined. What makes it work is that `capability` occurs in `handler`'s
**result** type, so it is fixed at the point the handler is consumed: `with`
demands `AlgOnly`, `handlerScoped` demands `AllowScoped`. The predicate is then
always discharged against a *known* capability. A handler value with no consumer
and no annotation simply generalises with the constraint attached, which is
correct and was checked.

Walking `effh` costs nothing new: `handler` already demanded `RowToList effh
effhL`, and `MkHandlersList`'s cons instance already did `EffNewtype efftyp
repr, RowToList repr reprL`. The open-row objection — that an open row cannot be
walked — does not bite, because the row walked is the one `Proxy effh` supplies,
which is closed by construction. The computation's row stays open.

`PermitsOps` is a four-arm chain: `AllowScoped` + `Scoped h` permitted,
`AlgOnly` + `Scoped h` refused with the message that names the offending
operation and points at `handlerScoped` / `withF`, **any other capability** +
`Scoped h` refused generically, everything else recursing. The third arm is not
a placeholder for a future extension: `HCapability` is an open kind, so a user
may declare their own inhabitant and pin a handler to it. Deny-by-default is
what keeps a capability nobody vetted from being scoped-permissive.

### Two things the type checker forced

Neither is a matter of taste; both were arrived at by watching the error
messages, and both would be re-broken by an obvious-looking simplification.

**`ClauseFor` for a scoped operation must be keyed on the OPERATION.** The
natural spelling puts the clause in the head —

```purescript
ClauseFor comp (ScopedClause h ff r o) r o
```

— and it does not work. The clause's own type is still being inferred from the
lambda the user wrote, so `r` and `o` arrive as unknowns, and the solver refuses
to commit to an instance head containing them: *"The instance head contains
unknown type variables."* The operation is always known, so keying on it
(`ClauseFor (Scoped h) f r o`, with `TypeEquals f (ScopedClause h ff r o)` in
the context) commits immediately and the equality is what forces the clause into
shape.

**`performScoped` needs a separate class whose head carries the operation's
declared type.** With the payload shape written into `PerformScopedEffect`'s
head — or imposed by an equality in its context — the use site's expected type
is unified against `h (Hoop eff) b -> Hoop eff b` before anything has looked at
what the operation actually is. Performing an ordinary operation scoped then
reports

```text
Could not match type Unit with type t1 (Hoop t2) t3
```

which says nothing. Splitting out `PerformScopedOp efflbl op comp comptyp`, with
`comp` in the **head**, makes an ordinary signature fail to match the first arm;
the chain falls through and the failure says what is wrong. The general lesson:
a `Fail` arm only speaks if the discrimination it depends on happens in a head.

### `Identity` is introduced on the way IN

The tactics record at `ctx ~ Identity` looks like it could be

```purescript
runScope body = unsafeCoerce (weave body)        -- WRONG
```

since `Identity` erases. It is not sound. The coercion is
`Hoop r (f x) -> Hoop r (f (Identity x))`, and the change is **under `f`**,
which is a rigid variable whose argument need not be representational. That
spelling adds a representation assumption to the trusted base that no proof
covers, and `coerce` cannot express it for the same reason. The correct form
introduces `Identity` inside the computation, so the weave's own `forall` is
instantiated at `Identity x`:

```purescript
scopeTactics weave =
  { runScope: \body -> weave (Identity <$> body)
  , bindScope: \cx g -> weave (Identity <$> g (unwrap cx))
  , resumeScope: \cx k -> continue k (unwrap cx)
  }
```

The price is one `map` per scope entry, which the monad laws make the identity.
**The scoped slice added no `unsafeCoerce` to `Hoop.Engine`.**

### `var` had to be generalised — a regression of the slice's own making

`var` was typed `... -> Handler effh r a o`. Before the capability index there
was only one handler type, so that was fully general; after it, a scoped handler
could not keep state in a cell. `var` is now polymorphic in the capability —
installing cells says nothing about which clauses a table may carry.

### Borrowability: what is refused, and where

Same restriction in substance as the TypeScript-backed runtime, but stated,
derived and reported rather than thrown.

- **The criterion is negative.** `blocking_effects` tests `found.kind =!=
  KFast`, so a `KScoped` clause blocks a borrow exactly as a `KFull` one does,
  and for the same reason — its canonical type mentions the answer type.
- **Only the intermediates are checked.** `scope_blockers` returns `[]` for the
  last frame of the prepared segment: the owner is not borrowed, so **the scoped
  handler itself may carry full clauses**. Only prompts *between* the perform
  site and the owner are constrained.
- **Shadowed entries do not block.** The property is stated through
  `lookup_handler`, so a `Full` clause that a later entry shadows is invisible
  to dispatch and has no business blocking a borrow either.
- **At weave use, not at dispatch** (Decision 5). A non-borrowable prompt in a
  context that is never woven rejects nothing.
- **`Rejected`, not `Stuck`** (Decision 7). The message names the innermost
  offending effect labels and says what to do about them — make them
  tail-resumptive, or install them outside the scope rather than between it and
  its handler. Only the innermost offender is named, because accumulating every
  blocker would need `@` on a path that must not call it.
- **`borrowable` is derived, not stored** — `Nil? (blocking_effects hs)` —
  so the FFI cannot supply its own answer.

### Is `Rejected` reachable from a well-typed program?

Asked after the slice landed, and worth recording because the answer differs
between the two rejections and because asking it found a defect.

**`UnborrowableScope`: yes, easily, and by design.** The type system does not
track borrowability — Decision 5 puts the check at weave use, at run time —
so a program that installs an ordinary handler between a scoped handler and its
perform site is well typed and rejects. It is not an exotic case: an unmarked
clause defaults to `full`, so the naive reader handler blocks a scope over it.
Run, from PureScript:

```text
hoop: the scope of 'exc.catch' could not be entered across non-borrowable
handlers: 'rd'. ... Either make the listed handlers tail-resumptive, or install
them outside the scope rather than between it and its handler.
```

This is the milestone's known boundary, and it is why the message is written to
be actionable rather than diagnostic. Lifting it is what "the general level"
below is about.

**`ClauseKindMismatch`: the question found a real defect, now fixed.** The
route was duplicate row labels — PureScript rows admit them, and the machine
dispatches on the label *string* — so two effect types sharing a label and an
operation name could put an ordinary clause where a scoped perform looks. It
ran, and produced the kind-mismatch rejection from a fully type-checked program.

But the reason it ran was that **`performScoped` constrained nothing about the
row it appeared in**. `PerformScopedOp`'s instance head introduced `eff` without
the `Row.Cons efflbl efftyp _ eff` that ordinary `performEffectImpl1` carries,
so `bad :: forall r. Hoop r Int` compiled — a scoped operation could be
performed into a row that does not declare it, including the empty row. That is
a defect of the slice, independent of the duplicate-label question; the
regression is `test-compile-fail/ScopedPerformIgnoresRow.purs`.

With the constraint restored the duplicate-label construction no longer
typechecks in either label order: performing the scoped operation requires the
first `e` to be the scoped effect, installing the ordinary handler innermost
requires it to be the ordinary one, and the two cannot both hold.

**What is not claimed.** That construction closing is not a proof that
`ClauseKindMismatch` is unreachable from well-typed code. `performEffect` and
`performScopedEffect` are exported and take the effect label, effect type and
representation by *type application*, which is a documented way round the
label-derived path; that route has not been examined for this. And
`unsafeCoerce` is always available. What the FFI comment says — that a kind
mismatch means one side "was built by hand or against a stale signature" —
holds for the typed surface as it now stands, and should be read as a claim
about that surface rather than about the language.

### What the tests constitute

- `test/Scoped.purs` — five behaviours through the real machine. The clause is
  a `catch`, chosen because `runScope` is on its **success** path: a clause that
  discarded its scope would exercise the dispatch of `PerformS` and never the
  `Weave` transition.
- `test/Scoped.purs`, the cell fixture — `Right [ 200, 999, 200, 42 ]`. Two
  regions sharing the reserved scalar label, one inside the scoped handler and
  one outside, read and written from both sides of a borrow. The four positions
  separate the three claims: the scope meets the nearer cell, a write inside is
  visible inside, the borrowed cell is a snapshot, the outer cell is live. This
  is the end-to-end half of the placement invariant that F\*'s `borrow_param` /
  `prepare_scope_can` (capability preservation), `prepare_scope_fast_agrees`
  (structure preservation) and fixtures 35-40 (the list itself) leave to the
  surface.
- `test-compile-fail/` + `scripts/compile-fail.sh` — four fixtures that must
  NOT compile, each declaring the substrings its error must contain. **One
  module per fixture, built one at a time**, because the PureScript compiler
  reports one error per module and two fixtures in one module mask each
  other. That trap was hit twice during this work and produced two false
  passes; it is the reason the harness exists in this shape. The harness
  itself is fire-tested three ways: a fixture that compiles, one that fails
  for the wrong reason, and one declaring no expectation are all reported as
  failures.
- `test/js/engine-smoke.mjs` — seven additions below the surface, covering the
  two new boundary exports, the machine's curried scoped-clause convention, both
  kind-mismatch rejections and the unborrowable-scope rejection, each matched
  against the distinguishing text of the real message rather than a loose
  pattern.
- Guard (e) re-fired in both directions — a direct
  `Hoop_Runtime_Syntax.PerformS` and a `Hoop_Runtime_Semantics.weave_of`
  detour — after the two exports were restored.

## The general level — decisions taken, and Gate A

### The reframing: re-instantiation is free, the evidence is not

F\*'s machine has one value type and one clause type, and PureScript erases
types, so **the table built at answer type `o` and the table built at `x` are
the same JS closures**. What a general weave needs is therefore not machinery
to rebuild a table; it is evidence that reusing it is legitimate.

Half of that evidence is already derivable from the shipped runtime data, and
half is not:

- *Derivable.* `ret == None` and "every dispatch-visible clause is `KFast`" are
  facts about the frame and the table, and F\* can state them from the real
  `ret` and the tagged table. The authority is that data, never a boolean the
  FFI supplies. The surface's `HasLabel hsL "pure" False` is a **diagnostic**
  witness of the same fact, not the authority.
- *Not derivable.* Family provenance. `withF (HandlerF installer) = installer`
  calls the ordinary `withImpl`, so the `HandlerF` type is gone by the time a
  `PromptF` exists, and an erased table cannot be asked whether it came from a
  family. This has to be carried from `withF` to the prompt.

That was the first correction to the reframing, and it is the load-bearing one:
re-instantiation is free as computation, not as evidence.

### The three-way classification

| class | condition | behaviour |
|---|---|---|
| `ContextTransparent` | every dispatch-visible clause is `Fast`, **and** `ret = None` | the current borrow, as a fast path |
| `Reinstantiable` | family provenance present | the general `ctx` / re-entry path |
| `Monomorphic` | otherwise | `Rejected` |

Priority is fixed: a prompt with family provenance is `Family` **even if it
happens to be all-fast with `ret = None`**. Dropping it to the fast path is an
optimisation to be justified by an equivalence proof, not a default.

`ContextTransparent` rather than `Borrowable`: the second names an
implementation, the first names the property that makes the implementation
sound.

**This is narrower than today's criterion, deliberately.** Today
`blocking_effects` reads clause kinds only, so an all-fast handler with a
non-identity `pure` is borrowed and its return transformation silently dropped
inside the scope. Under the classification such a handler installed with plain
`with` is `Monomorphic`, i.e. rejected. A `ContextDiscarding` fourth class to
preserve the old answer was considered and rejected: it would formalise exactly
the silent semantic difference this project avoids everywhere else. If that
behaviour is ever wanted it should be an explicit API, not an implicit class.

The baseline that records what changes is `Test.Scoped.baselineSpec`.

**The classification is still three-way, and stays that way until Gate B1.5
reports.** Whether `Reinstantiable` splits — family provenance on one side, a
family *plus* an explicit weave capability on the other — depends on whether
the machine can build the general path from provenance alone. See "What is not
decided" at the end of this section.

### The baseline, measured before anything moves

Run against the shipped runtime, an all-fast intermediate with
`pure: \s -> "<" <> s <> ">"`:

| observation | result |
|---|---|
| no scope | `Right "<a>"` — once |
| scope resumed across it | `Right "<a>"` — once, **not twice** |
| the raw scope value, seen through `bindScope` | **`"a"`**, not `"<a>"` |
| the clause discards its continuation | `Left "y"` — **never** |

The third row is the decisive one and it needed `bindScope`, which nothing had
exercised before. The mechanism: `borrow` clears `ret` on an intermediate, so
the scope's own value is untransformed; `kont_of captured` splices back the
**un-borrowed** frames, so the transformation happens once, on resumption.
`weave_of` uses `prepared` (borrowed) and `kont_of` uses `captured`
(un-borrowed) — two different lists, and that is what makes "not inside,
exactly once outside" come out.

### Gate A: types only

Eight conditions. Seven behaved as intended; the eighth was **vacuous**, and
finding that out was the useful part.

| # | condition | result |
|---|---|---|
| 1 | a monomorphic `Handler` cannot be reused at a rigid `x` | refused |
| 2 | a `HandlerF` is legitimate at every `x`, no `unsafeCoerce` | compiles |
| 3 | the classification is expressible as a kind, `Reinstantiable` carrying `f` | compiles |
| 4 | one intermediate gives `ctx = f`; two give `Compose f₁ f₂` | compiles |
| 5 | owner outermost: `Either String (Array (Maybe x))` | compiles |
| 6 | the tactics are not implementable from the clause alone | **see below** |
| 7a | all-fast, no `pure` → `ContextTransparent` | compiles |
| 7b | all-fast, non-identity `pure` → not `ContextTransparent` | refused |
| 7c | the same clauses via `HandlerF` → `Reinstantiable f` | compiles |
| 7d | a `Full` clause → not `ContextTransparent` | refused, by name |
| 8 | no `unsafeCoerce`, `HFunctor` or FFI in the positive cases | held |

The classification needs **no new type machinery**: `AllFastOps` is the same
shape as `PermitsOps`, and `ret = None` is the `HasLabel hsL "pure" False` that
`handler` already computes. (`7b`'s message is currently
`Could not match True with False`, which is not fit to show a user; the real
implementation must wrap that in a `Fail`.)

#### Condition 6 was vacuous as first written, and why that matters

Stated over `runScope`, it *compiles*:

```purescript
runScopeAtArray weave = \body -> weave (map (\x -> [ x ]) body)
```

which is well typed and semantically wrong — it injects each value into a
singleton instead of re-entering the intermediate prompt. **Types cannot tell
the right `runScope` from a wrong one.**

Restated over `resumeScope` it is not vacuous:

```purescript
resumeScopeAtArray _weave = \cx k -> case Array.head cx of
  Just x -> continue k x
  Nothing -> ?noValueToReturn      -- Hoop r0 o1, with o1 rigid
```

There is no `o` to be had: `o` is rigid, the weave produces `f _`, and `k` needs
an `x` that does not exist. So:

> The need for a machine capability is exposed by **elimination**. Introduction
> (`runScope`) and extension (`bindScope`) are not forced by their types, and a
> wrong implementation of either typechecks.

This decides what Gate B has to be. `runScope` and `bindScope` can only be
checked behaviourally, and the strongest instrument is a `Full` clause that
actually resumes its continuation more than once — that is what exercises the
`Cont ... o`-dependent part of a re-instantiated table, which a non-identity
`ret` alone does not reach. It is a *required* fixture rather than the only one:
performing the intermediate's own operations inside the scope, a combining
intermediate, a two-layer `ctx` whose order is observed, and `bindScope`
applying a continuation to each branch all discriminate too.

### The consequence: non-trivial logic leaves PureScript

Condition 6 says a wrong `runScope` typechecks. The answer is **not** a cleverer
PureScript type that pins the implementation down — types do not determine an
implementation's extensional meaning, and no amount of indexing changes that.
The answer is to move the logic that can be wrong somewhere it can be proved.

This is not hypothetical. The first `scopeTactics` written for the borrowable
milestone had `runScope: \body -> unsafeCoerce (weave body)`. It typechecked,
every test passed, and it was caught in review — the type system never fired.

So the boundary is:

```text
PureScript ScopeTactics     -- passes its arguments through, and nothing else
    ↓
FFI constructor
    ↓
F* reference transition     -- what the tactic MEANS
    ↓
F* optimized transition     -- what runs
    ↓  simulation
```

No `map`, no traversal, no branching, no context composition on the PureScript
side. The present `Identity <$> body` is admissible only because `ctx` is
trivial at this milestone; at a non-trivial `ctx` every tactic delegates.

**Added to Gate B as stop conditions:**

- any of `runScope` / `bindScope` / `resumeScope` needing to be non-trivial
  PureScript logic rather than a thin delegation to a verified transition;
- PureScript traversing, constructing or observing a `ctx`;
- the FFI passing anything but a context plan or an opaque context value;
- a tactic with no corresponding reference transition;
- no simulation between the reference and optimized machines;
- `unsafeCoerce` moving a value into or out of a `ctx`.

The FFI choosing the right transition is checked separately, by perturbing each
JS smoke — the boundary is outside every proof, as it is for the existing
clause-shape discrimination.

#### Where the laws go — one level below `ScopeTactics`

An earlier draft of this section proposed stating unit and associativity over
the record's own functions. They do not typecheck there: `bindScope cx pure` has
type `Hoop r (f (ctx x))`, not `ctx x`, so there is nothing to compare `cx` to;
and `bindScope (bindScope cx g) h` cannot nest, because the inner call already
returns `Hoop r (f (ctx y))`. The record is the *public* form, with the owner's
`f` already laid over the top.

The laws belong to the context plan underneath, over operations of the shape

```text
enter_C   : Comp x -> Comp (C x)
extend_C  : C x -> (x -> Comp y) -> Comp (C y)
resume_C  : C x -> (x -> Comp o) -> Comp o
```

with the obligations: left identity at a point; `extend_C cx pure` a right
identity; associativity of `extend_C`; `resume_C` agreeing with the preserved
continuation; plan composition matching handler nesting; and — the one tying
the classification back to what ships — **a transparent plan being
observationally equal to the existing borrow**. `runScope` and friends are then
that proved algebra with `f` laid over it.

The injection counterexample (`weave (map (\x -> [x]) body)`) fails
associativity, which is why it belongs there rather than in a fixture.

#### Indexed protocols are not the safety mechanism

An indexed `IHoop` can express a usage protocol, and there are places it would
earn its keep — the machine primitives' call protocol, a specific combinator
that must re-enter exactly once, finalizer registration and release. It is not
what makes the tactics correct, for two reasons.

*It does not reach the failure mode.* Restricting `runScope` to one call does
nothing about that one call being the injection rather than a re-entry. The
defect is extensional, and an index counts occurrences.

*It cannot enforce linear use of a value anyway.* PureScript duplicates
variables freely, so `let p1 = bindScope cx g` and `let p2 = bindScope cx h` are
two values whichever indices the monad carries; an Atkey-style pre/post index
([Parameterised Notions of Computation](https://bentnib.org/param-notions.html))
refuses to *compose* them in one chain but does not record that `cx` was named
twice. Tracking that needs usage in the typing context, as in
[Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.pdf) —
and distinguishing several live contexts would need fresh type-level tokens
besides. That is a heavy design for PureScript, and it would be buying the wrong
thing.

And the rule it would enforce is not a general law. "At most one `bindScope` per
context" is right for `bracket`'s sequencing and wrong in general: Hoop admits
multi-shot continuations, and a handler that deliberately re-enters a context
several times is legitimate. The recorded trap has been narrowed accordingly —
it is about using repeated re-entry *as sequencing*, not about repeated re-entry.
Resource safety, which is what motivates the restriction, is not bought by
constraining `bindScope`; it needs finalizer frames, and it has its own
milestone.

### Where the prototype lives

`runtime/proto/`, verified on every build and never extracted. The guard that
keeps it out of the shipped path is checked, not trusted — `--extract` reads a
module name as a namespace prefix, so a prototype named into an extracted
namespace would be offered up silently. Fire-tested with a module named
`Hoop.Runtime.Machine.Sneaky`.

`Hoop.Runtime.*` is not to be edited for a prototype's sake. A prototype that
needs a change there is a prototype that has finished.

### B1: the plan verifies; its context value replays

`runtime/proto/Hoop.Proto.GeneralWeave.fst` (1,098 lines) states the context
algebra as `prop`-valued definitions — not `val`s, not axioms — over an
ordered plan:

```fstar
plan      = Plan (layers: list plan_item) (owner: powner)
plan_item = PIBind fn | PICell l x | PITransparent hs | PIReenter hs ret
```

with two projections of the same plan, which is the point of the
representation:

```fstar
let enter_C  pl c    = PSplice (plan_enter_frames pl) c
let resume_C pl cx k = PSplice (plan_resume_frames pl) (pbind (PCtx?.pending cx) k)
```

Four laws: `law_left_identity`, `law_right_identity`, `law_assoc` — two
conjuncts, one algebraic and one anchored to the plan — and
`law_resume_matches_continuation`. Each is a `prop` parameterised by a
`ctx_ops`, so `law_X apply ops ...` is a *statement about* an implementation.

**What B1 established and what it did not.** F\* checked that the four
propositions are well typed and that the representation can even make them —
`law_assoc`'s anchored conjunct is the one that needed the ordered plan to be
statable at all. It did **not** prove that `ref_ops` satisfies them; that is
B2's obligation, written down as such in the module. Likewise the two wrong
implementations `pointwise_ops` and `flat_ops` are recorded with the laws each
is *intended* to fail — all four for `pointwise_ops`, the two anchored ones for
`flat_ops` — and those refutations are unproved too. They are there so the laws
have something to be tested against, not as results.

**Where it fails.** `pctx` is a *suspension*: it holds the pending computation.
So re-entry **replays** it, and `catch`'s observe-then-resume runs the protected
computation twice. That is decisive on two counts. It makes B3's obligation "a
transparent plan is observationally equal to the existing borrow" *false* —
and the shipped runtime demonstrably runs the body once (`baselineSpec`: `Right
"<a>"` once, not twice). A representation whose stated goal is to subsume the
shipped behaviour cannot begin by contradicting it.

Kept from B1, unchanged: the ordered plan, owner separation, `PIBind`
preservation, the two enter/resume projections, and the anchored half of
`law_assoc`. What is replaced is `pctx` and its production and consumption
rules.

### Gate A2: what an answer former gives, and what it does not

Three results, all measured against types and behaviour rather than argued.

*The distributive law is suppliable and composable.* The law experimented with
is

```purescript
type Dist f r = forall x. f (Hoop r x) -> Hoop r (f x)
```

— computations *inside* the shape, pulled out. It is writable for `Either e` and
for `Array`, and `Compose f g` composes from `Dist f` and `Dist g` needing only
`Functor f`. So there is no supply problem and no composition problem.

*The derivation stops short of elimination.* Applying `Dist` to the context
mapped with the continuation gets only as far as `Hoop r (f o)`. Completing
that attempted derivation would require an additional operation

```text
Hoop r (f o) -> Hoop r o
```

which `Dist` does not provide. It is **not** the inverse of `Dist` — that would
be `Hoop r (f o) -> f (Hoop r o)` — but a separate elimination of the remaining
`f` layer, and with `o` rigid nothing but `unsafeCoerce` inhabits it. The same
shape of hole condition 6 found, now at the general level: **the answer former
says how values come back out of the scope, and it does not say how the layer is
discharged.**

The scope of that finding is worth keeping narrow. It says the `Dist`-based
derivation leaves this hole — not that `resumeScope` must in general perform
such a collapse. A plan-anchored machine transition is a candidate precisely
because it can implement `resumeScope` without ever constructing an
`Hoop r (f o)` to collapse.

*The answer former does not determine the context.* `f = Identity` with a
`Full` clause that resumes twice ran the continuation **2 times**. `f` is
`Identity`; the control is multi-shot. So `f` does not determine `ctx`, and a
type of the form `HandlerF effh r f` says nothing about how many context values
exist or how they are eliminated.

Conclusion recorded: **`Dist f` alone is not sufficient, and handler control is
not recoverable from the answer former.** One clarification that belongs with
it — `Dist` is not `Traversable`. It is a distributive law for one specific
`Hoop r`. `Traversable` supplies it in general, but is not a necessary
condition.

### The counterexample gate: eager leaf collection is dead

A candidate general representation was "the leaves, and the captured
continuations up to them", collected by the machine. Run against a clause whose
second resume is conditional on the first's answer —

```purescript
first <- continue k true
case first of
  Left _  -> continue k false
  Right _ -> pure first
```

— the continuation ran **2 times**, and the second call's existence is decided
by the first call's *real* answer. A static leaf list cannot express that.

**What this rejects is eager leaf collection, not machine-only.** The list is
dead because it is computed in advance; the question of whether the machine can
supply the general path without a new surface capability is untouched by it.

### `f = (->) s`, stated precisely

`Reader s a` and `s -> a` differ by a newtype and nothing else; PureScript's
`newtype Reader r a = Reader (r -> a)` with `runReader` is the same functor.
There is no Hoop-specific obstruction here, and the earlier framing of this as
"Hoop cannot express it" was wrong.

What is true:

- `Dist ((->) s) r = (s -> Hoop r x) -> Hoop r (s -> x)` is not constructible in
  general — `(->) s` does not carry a distributive law in that direction. The
  same hole is there in Haskell.
- The standard Reader handler uses `s -> Hoop r a`, **not** `Hoop r (s -> a)`,
  and so contributes a trivial `ctx`.

What may **not** be said: that `(->) s` cannot be an answer former.
`HandlerF effh r ((->) s)` is writable in special cases — a pure-only handler,
an abortive clause that discards its continuation, a handler that receives the
`s` as an operation argument. The precise statement is:

> `(->) s` has no general `Dist`-based weave capability, and the standard Reader
> effect does not implement it as an answer former.

### Gate B1.5: residual configuration, before any explicit capability

Two representations of the context value are now excluded:

| candidate | why it fails |
|---|---|
| the original inner computation | replay — B1 |
| the list of leaves | no result-dependent resume — the gate above |

The remaining machine-only candidate is a **residual configuration**: the
machine stops at the first resume point and keeps a configuration that can be
continued once a real answer arrives. As a protocol:

```text
ContextDone     result
ContextRequests value residual
```

`ContextRequests x residual` means: the handler asked for `continue k x` and has
not yet been given the answer; hand it one and `residual` continues.
`resume_C pl cx k` interprets that — take `ContextRequests x rest`, run `k x`
under `plan_resume_frames pl`, hand the real answer to `rest`, repeat if the
handler asks again, and return the handler's own result when it finishes.

Under this reading the result-dependent case works: the first resume returns the
*real* `Left`, the second resume comes into existence only because of it, the
protected prefix is not re-run, and effects performed between resumes stay in
the residual configuration. This is a coroutine — an interaction tree whose
next shape is decided by the answer received — not a precomputed tree.

Why it is worth trying before any surface capability: **`continue` is an
explicit boundary the machine already knows**, and the rest of the clause's
closure is already preserved as `BindF`. The clause can stay entirely opaque.
So "reifying the handler algebra requires a new trusted DSL" is *not*
established.

Conditions:

| # | condition |
|---|---|
| 1 | `runScope → resumeScope` runs the protected prefix exactly once |
| 2 | `firstOfTwo` produces two resume requests, in order |
| 3 | `retryOnFailure`'s second resume depends on the first's real answer |
| 4 | effects performed between two resumes keep their order |
| 5 | a `Full` clause that never calls its continuation terminates correctly |
| 6 | a transparent plan is observationally equal to the existing borrow |
| 7 | a mixed plan preserves prompt / cell / bind order |
| 8 | a deliberately multi-resumed context is multi-shot **from the saved point**, not from the prefix |
| 9 | no new FFI that inspects a clause closure, and no semantic callback assumption |

Stop condition, stated so it can fire:

> If the residual configuration cannot be built at the first resume point from
> the existing machine state and `BindF` alone — if it requires inspecting or
> transforming the inside of an opaque clause — machine-only is rejected and
> the work moves to an explicit weave capability on the surface.

#### B1.5, run: the stop condition did not fire

The module verifies, at 1,098 lines grown to 2,229, with no `admit`, no
`assume`, no weakening pragma and no `val` standing in for a proof. **What it
establishes is the residual protocol for a closed computation satisfying
`settles`** — see the finding below — and not the general semantics.

*The projection tension resolved by deferring the choice to consumption.* The
open problem going in was that a residual has already been run under one
projection, while `resume_C` wants the perform-site binds back and `extend_C`
must not have them. Both were avoided:

- a **third** projection, `plan_protocol_frames`, is what a residual is produced
  under — `plan_resume_frames` with each recorded `PIBind` rendered as a new
  frame `PSiteF`: present, in the original interleaving with the prompts, and
  **dormant**;
- a consumer installs `PModeF mode` directly beneath the residual it drives, and
  a `PSiteF` consults the nearest one — under `MResume` it is the `PBindF` it
  was recorded from, under `MExtend` it is nothing.

Because the marker is **dynamically scoped**, the bind frames a layer has
carried into its own captured continuations — the ones at second and later
boundary hits, where the residual is no longer literally `plan_enter_frames pl`
— get the same treatment with nobody having to locate them. That is exactly
where the two obvious repairs break.

*Conditions.* 2, 3, 4, 5, 7, 8 passed as posed, each as something F\* checks
(`assert_norm` at concrete values, not a comment claiming a result). 6 passed
**at an instance**: the transparent projection is pinned frame-for-frame against
what `borrow` produces, and the quantified statement `law_transparent_agrees` is
stated and unproved, B3's. 9 is a property of the design, respected and located
in comments. 1 is the interesting one.

Two guards were fired independently of the work that wrote them: mutating the
cost fixture's expected slope, and collapsing `resume_C` into `extend_C` — the
latter breaks `fixture_5b`, which is the check that the two operations stayed
observably different.

#### The finding that reshapes the next gate: purity hides replay

**This machine is pure, so consuming a residual twice is indistinguishable, by
any observation the module can make, from re-running a suspension twice.**
`fixture_1_same_answer` checks that the two representations return the *same
value*. Replay becomes observable only where an effect escapes the plan, which
in the shipped JS runtime is every effect and in this machine is none.

So condition 1 was recorded about **work** instead:

| | n=1 | n=5 | slope |
|---|---|---|---|
| residual | 43 | 51 | **+8** — one copy of the prefix |
| suspension | 41 | 57 | **+16** — two |

The intercepts are not equal and the residual is two transitions dearer at
`n = 1`; the fixture says so rather than rounding it away.

**This is a good non-vacuous check and it is not a semantic acceptance
criterion.** Three reasons, and they are why B1.6 exists: transition counts move
when bookkeeping frames are added; the measurement shows that one representation
did *less work* than another, not that anything ran *once*; and while `pobs_eq`
observes only values, a replaying implementation can still satisfy the laws B2
is meant to prove. The cost fixture stays, demoted from semantic evidence to a
**regression test that prefix work is shared**.

#### Three judgements taken

*B1's criterion "a `resume_C` that could be written without touching the plan is
wrong" is retracted.* Under the residual representation `pl` really is unused in
both consumers; the plan is read exactly once, by `enter_ctx_C`. Accepted —
the discriminating power moved rather than vanished (`flat_ops` is now wrong at
`o_enter_ctx`, and that is checked). Recorded, though, as a property of **this
representation** and not as a general licence: *the plan is interpreted once, at
production, and the interpretation is sealed into the token.*

*`plookup_t` — dispatch threaded as a parameter* — is accepted for a
prototype, and is arguably a gain: it separates the machine semantics from the
table implementation. It was forced, not chosen: `handlers` is abstract in its
`.fsti`, `lookup_handler` does not reduce, this module has no interface and may
not gain one, so the fixtures would have been claims rather than checks. The
cost is that they exercise the dispatch *discipline* against their own table.
Closing it needs two layers, not more `assert_norm`: B2's laws quantified over
any coherent `lk` / `apply`, and a production bridge tying `pref_lookup` to
`lookup_handler` and the shipped table's classification — which step 1's
fixtures already largely pin.

*`pfind_mode`'s nearest-enclosing search carries no label.* Unproved in B1.5 and
that is acceptable there, but it belongs in **B2's completion conditions**: it
is a semantic invariant, not an implementation detail — pick the wrong marker
and a `PSiteF` confuses `MResume` with `MExtend`. The order is to prove
"the nearest marker is the driving consumer's" from a well-bracketed production
discipline first, and to fall back to labelling three frames and one search only
if that fails.

### Gate B1.6: effectful production

A machine-global logger alone would make prefix exact-once observable and leave
`settles` and detached production exactly where they are. Both are one problem,
so they are gated together.

Today production is a **detached evaluation**:

```fstar
enter_ctx_C ... = psteps ... (PStep c (PBoundaryF :: plan_protocol_frames pl))
```

— a meta-level function running the computation to completion on an *empty*
ambient stack. But the surface's `runScope` is a `Hoop` computation, so effects
raised during production must be able to travel outward. Every law in the module
currently carries a `settles` hypothesis, which is precisely this.

> **The central proposition: can context production be expressed as an effectful
> transition on the live machine, rather than as detached evaluation on an empty
> stack?**

An observation trace is the *instrument* for checking that, not the answer.
Adding the trace and keeping `settles` would mean proving the laws with the
hardest part pushed outside the hypothesis.

| # | requirement |
|---|---|
| 1 | the transition sequence carries an observation trace that is **not** preserved into the residual |
| 2 | one observation event sits in the protected prefix |
| 3 | consuming the residual twice yields that prefix event **once** |
| 4 | the suspension version yields the same event **twice** |
| 5 | an ordinary operation the plan does not handle, placed in the prefix, is handled by a prompt **outside the owner** |
| 6 | that outer handler's pending binds and answer transformation are **not lost** |
| 7 | on success, the `settles` hypothesis — in the sense "performs no operation outside the plan" — is removed from the laws |
| 8 | production is initiated by an **object-language transition on the live stack**; neither the production primitive nor the tactics invoke `psteps`, accept `fuel`, or call the clause interpreter directly |

5 and 6 are the substance; 1–4 are how exact-once stops being a claim about
transition counts; 8 is the stop condition, below.

#### The stop condition, and why it is about a type

> Production must become an object-language machine transition. It must **not**
> remain a meta-level call to `psteps`, even if that call is handed an ambient
> stack or an observation trace.

The reason is visible in the signature as it stands, before any behaviour is
considered:

```fstar
o_enter_ctx : plookup_t cl -> papply_t v cl -> nat -> plan v cl -> pcomp v cl
            -> pctx v cl
```

Taking `lk`, `apply` and a `fuel` and returning a pure `pctx` **is** detached
evaluation, written down. It is not a semantic operation so much as a
test-harness partial evaluator exposed through the interface. If B1.6 succeeds
the shape must instead be a node — conceptually

```fstar
PEnterCtx : plan v cl -> pcomp v cl -> pcomp v cl
```

— that steps on the live stack and yields an opaque context token as a *value*
when it reaches the boundary. The constructor's real name and the token's
representation are outcomes of the gate; "an implementation that calls `psteps`
from the inside does not count" can be fixed in advance.

This connects back to the standing stop condition that the three tactics must be
thin delegations to a verified machine transition. A tactic that runs the
machine itself is not delegating to a transition; it *is* one, written at the
wrong level.

The four laws may well change type as a consequence. That is not a regression —
it is the same correction reaching the laws. "B2b: the four laws, over the new
production" is already phrased to allow it.

#### The exact-once fixture must be written in the object language

Requirements 2–4 are vacuous if the fixture produces its token at the meta
level. `let cx = enter_ctx_C ...` invites normalisation, sharing and
substitution to decide the answer, which is not a test of what the *machine*
did. The shape required is

```text
enter once
  >>= \cx ->
        consume cx
          *> consume cx
```

— the token produced once by an object-language bind, the same produced token
consumed twice, the prefix event appearing **once** in the whole trace, and each
consumer's own events appearing twice.

#### B1.6, run: production is a transition, and the context went dynamic

The stop condition did not fire. Production is now the node

```fstar
| PEnterCtx: pl:plan v cl -> body:pcomp v cl -> kbody:pcomp v cl -> pcomp v cl
```

whose rule is one line of frame-pushing on the live stack, with a new frame
`PScopeF` — the **scope floor** — separating the scope's frames from the
ambient stack. The token is formed by a *value* rule cutting the stack at the
floor.

The evidence for requirement 8 is structural rather than a grep: **`ctx_ops` no
longer mentions `pctx` at all.** Every field returns a `pcomp`, and every field
of `ref_ops` is a single constructor application. An implementation cannot run
anything, because it is not handed anything to run with.

`settles` is **deleted, not weakened** — no law mentions it, and `PCtxLost`
went with it. What is checked is that the program `settles` used to exclude now
runs correctly, with the ambient handler's pending bind and answer
transformation both intact around the scope's own answer, and that B1.5's
production gets `PStuck` on the same body. That the laws *hold* without the
hypothesis is B2b's.
`law_assoc` also lost its `cx` parameter.

Requirements 1–8 all passed. Requirement 1 holds **by type**: the trace is the
driver's second result, and no `pstate`, `pframe` or `pctx` has a place to keep
it.

Guards: 23 fixtures and 10 machine rules fired. Two were re-fired independently
— collapsing `resume_here_C` into `PExtendC` breaks `fixture_5b`, and making
the scope floor block the outward search in `pfind_prompt` breaks `fixture_10`,
which locates the one line that makes requirement 5 come out. A first firing
round found a real weakness: fixtures calling raw constructors accepted the
collapse, and were rewritten through the named operations.

**Two mutations were accepted and are recorded in the module.** `pcut_scope`
cutting at the *farthest* floor instead of the nearest is not separated by
anything the file checks — the nearest-floor discipline is *chosen*, and joins
`pfind_mode` as an obligation. And `PCtxRequests y [] PVar` for `PCtxDone y` is
genuinely operationally equal, the constructors being kept apart for the reader.

#### The price, and why it is not payable

To get the token into the value position at all it was **defunctionalised**:
production installs it in a `PTokenF` frame and the consuming nodes read the
nearest one, exactly as `PReadP` reads a cell. A context is therefore
**dynamically scoped** — it cannot be stored, returned as a scope's own
result, or put in a list, and a scope opened inside a consumer shadows the
token being consumed.

The module claimed that nothing the design needs today is lost, on the grounds
that the tactics are written against "the context this clause is handling".
**That is retracted.** The published `ScopeTactics` takes an explicit context
argument:

```purescript
bindScope   :: ctx x -> ...
resumeScope :: ctx x -> ...
```

so this typechecks today —

```purescript
r1 <- t.runScope p
r2 <- t.runScope q
case r1, r2 of
  Right cx1, Right cx2 -> t.bindScope cx1 g
```

— and under a dynamic token the last call would use `cx2`, the nearest,
because `cx1`'s value was never kept. That is not a limit on expressiveness;
**it runs a well-typed program with a different meaning.** `ctx` being
unobservable does not make it unselectable: which of several `ctx x` is passed
is the caller's choice.

The same correction reaches `law_assoc`. Quantifying over stacks recovers a law
about the *nearest* token, but not about a program that selects an outer token
while an inner one is live, consumes two tokens in the reverse order, or holds
tokens in a pair. The law's subject matter narrowed.

#### Strict positivity: what is actually ruled out

Two shapes were tried and rejected by F\*: a `kf : pctx v cl -> pcomp v cl`
field on the production node, and the sum value type
`pvalue v cl = PV of v | PCtxV of pctx v cl`. Both are genuine negative
occurrences, not a conservative check being unhelpful: **`pctx` contains a
negative occurrence of the value type, which closes a negative recursive cycle
when it is embedded directly into the value language.** (It contains positive
occurrences too — "contravariant in `v`", said earlier, was too strong; one
negative occurrence is all the check needs and all that is true.)
`[@@strictly_positive]` annotations are for
telling F\* that an abstract parameter is used positively; they do not make a
real negative occurrence acceptable, and there is nothing here for them to
declare.

**What is ruled out is the direct recursive embedding, and nothing wider.**
Checked in a scratch module, at universe-annotated types so the positivity check
is what answers:

| shape | result |
|---|---|
| `pval` holds `pctx`, all three mutual | **rejected** — `pctx` not strictly positive |
| key indirection, `pctx` lifted out, `pval` still mutual with `pcomp` | **rejected** — `pcomp` not strictly positive |
| key indirection, `pval` defined **before** `pcomp` and not mutual with it, `pctx` outside | **verifies** |

The third row is the point: once only a non-recursive key enters the value
language, `pval` no longer needs to mention `pctx`, so it stratifies out of the
recursive block, and `pctx` — which holds `pval v -> pcomp v` — sits outside
it. A store `nat -> option (pctx v)` beside the machine state typechecks.

So the handle-and-store design is available. It brings its own obligations:
freshness, lookup, preserving the store across capture and resumption, and an
opaque representation for the handle after extraction.

### Gate B1.7: a first-class context handle

B1.6's main result stands. What is rejected is neither the residual
configuration nor machine-only, but **the step that reads an explicit context
argument as the nearest dynamic token**.

> B1.6 established live, effectful, exact-once production for a dynamically
> scoped residual protocol. It did not establish adequacy for the first-class
> `ctx x` the published `ScopeTactics` exposes.

| # | condition |
|---|---|
| 1 | production returns an opaque handle as an object-language value, once |
| 2 | two contexts can be alive at the same time |
| 3 | an outer context can be selected explicitly while an inner one is live |
| 4 | what is consumed is decided by the handle passed, **not** by nearness |
| 5 | B1.6's exact-once, ambient-handler and multi-shot fixtures still hold |
| 6 | strict positivity is satisfied **without** a direct recursive embedding |
| 7 | **store integrity** — every consumable handle was allocated by the machine and resolves to exactly its associated residual; a missing or forged handle must **not** fall back to the nearest context |
| 8 | **persistence and aliasing** — extending a context produces a *fresh* handle without modifying the original; two extensions of the same handle stay independent and may be consumed in either order |

7 and 8 are not implied by 2 and 3. An implementation that overwrites a store
entry in place can still keep two contexts alive and still let an outer one be
named — and would silently break

```purescript
cy1 <- bindScope cx g
cy2 <- bindScope cx h
```

where `cx`, `cy1` and `cy2` must be three independent contexts, because the
published API admits multi-shot use of the same `ctx x`. An append-only
persistent store, or semantics equivalent to one, is what condition 8 asks for.
Condition 7 is its companion at the other end: identity must be *resolved*, and
a handle that resolves to nothing must fail rather than degrade into B1.6's
nearest-token reading, which is the very behaviour this gate exists to remove.

#### B1.7, run: passed, and the first proofs in the prototype

All eight conditions passed; the stop condition did not fire. 3,277 → 3,899
lines.

A handle is `PCtxKey of nat`, one of two constructors of the stratified value
language `pval v`. Because `pval` mentions only a `nat` it needs no `pctx`, so
it leaves the mutual block, so `pctx` — which holds `pval v -> pcomp v cl` —
sits outside it, so `pstore = list (nat & pctx v cl)` can be given a type. The
negative occurrence is still there and still fatal to a direct embedding; the
key is what stops the cycle closing.

Conditions 4 and 7 hold **by type before they hold by behaviour**:

```fstar
presolve : pstore v cl -> pval v -> option (pctx v cl)
```

is not given a stack, so there is nothing for a nearness fallback to consult.
`PTokenF` and `pfind_token` are deleted. The store and counter live in a
`pconf` beside the machine state; `palloc` conses and increments and is the only
writer — no free, no clear, no update.

Several B1.6 fixtures became *stronger* rather than merely surviving: 1, 5b, 7
and 8 now name **one handle twice**, where B1.6 could only consume "the context
in scope" twice and argue that both found the same token. Independent re-firing:
rewriting `presolve` to ignore its key and return the most recent entry — the
same behaviour under another name — is rejected by
`fixture_18_handle_not_nearness`, which is two programs differing in one
variable at one point in one stack.

**The first proved obligations in this prototype.** `lemma_alloc_wf`,
`lemma_alloc_monotone`, `lemma_alloc_fresh` and `lemma_alloc_preserves` are
lemmas with proofs, not `prop` definitions. The last is condition 8's core:
allocation disturbs nothing already allocated.

`fixture_1_prefix_runs_once`'s intercepts moved 47→48 and 55→56, one extra
value step for carrying the handle. **The slopes are unchanged** — 8 and 16,
still exactly 2×.

#### What B1.7 did not establish

*The observation relation still has no trace.* `pobs_eq` / `pobs_le` were
strengthened to quantify over an arbitrary store and counter, but what they
observe is still the final value only — the `PEmit` trace B1.6 introduced is
not in them. **An implementation that replays the prefix can therefore still
satisfy the laws**, because on a pure machine replay changes no value. B1.6's
exact-once
observation is not yet connected to any proof obligation, and connecting it —
a trace-aware observational equivalence, or a trace congruence alongside — has
to happen *before* B2b, not after.

*`pconf_wf` is not connected to reachability.* It appears in the definition and
in the local lemmas, and there is no theorem that the initial configuration is
well formed and that every `pstep` preserves it. That belongs in B2a.

*Fixture 17 does not store handles in a list.* It renders each handle to an
ordinary value with `fseen` before putting it in one, so what it shows is that
two contexts are alive and separately nameable — not that a real handle can be
put in a pair or a list and taken out again. That is a boundary of the shallow
`pval = PV v | PCtxKey nat` model. A stronger claim needs a different model.

*Stale names, corrected.* Three doc comments referred to `lemma_step_fresh` and
one to `fixture_19_multi_shot_alloc`; neither exists. They now name
`lemma_alloc_fresh`, `lemma_alloc_monotone` and `fixture_21_multi_shot_alloc`.
The prose had been written ahead of the code — the same thing that made this
gate's remaining-work estimate wrong, since F\* halts at the first fatal error
and nothing below the failure point had been checked in the new shape at all.

#### Four limits on how the representation should be read

- **The global monotone store is a reference semantics**, adopted so that
  handles created in sibling resumptions can be resolved together afterwards.
- **Multi-shot does not rule out every snapshot scheme.** What it rules out is
  the naive one, which solves neither collision between independent allocators
  nor lost updates. A scheme that solved those is not excluded by anything here.
- **The non-reclaiming association list is prototype-only.** It is *what makes*
  condition 8 hold. A shipping form needs a reclamation scheme that cannot lose
  an escaped handle, a lookup cost, and a bounded representation for ids —
  and, established later by the nesting/sibling gate, it must also preserve
  **cross-branch freshness and the stability of live identities**: an id must
  not be reused while a handle carrying it may still be observable, and two
  jointly observable branches must not be handed the same id. Reclamation is not
  forbidden, but it now carries that proof obligation.
- **`fseen` is fixture instrumentation.** No transition applies it. It does not
  mean handle identity is observable to a user; without it "these two handles
  differ" could not be written as a value and conditions 1, 2 and 8 would be
  unstatable.

#### `pcut_scope`: a negative result, not a missing fixture

Both mutations B1.6 recorded as accepted survive B1.7 unchanged. The interesting
one is `pcut_scope` cutting at the farthest scope floor rather than the nearest.
The handle representation was the obvious candidate to separate them — a
wrongly cut residual is now a wrongly *stored* one, with an identity that can
be named — and it does not. The mutant is not a no-op (the two disagree on
`[PScopeF; PBoundaryF; PScopeF]`), and all 21 fixtures still pass.

The conclusion to draw is **not** "the fixtures are insufficient". If B2a
cannot state a theorem that requires the nearest decomposition, then
nearest-floor is an implementation normal form rather than a semantic
requirement — and this
surviving mutation is the evidence that makes the distinction visible. The other
survivor, `PCtxRequests y [] PVar` for `PCtxDone y`, remains genuinely
operationally equal.

### Gate B2a, strand 1: proximity adjudicated

**Verdict: proximity is a semantic requirement of this protocol, not an
implementation normal form.** The question was decided by a theorem, as it had
to be — no fixture separates the two, and B1.7 had already shown that giving
the context an identity does not separate them either.

The invariant, stated over a *segment* so that it mentions no configuration:

```fstar
let presid_wf r = match r with
  | PBoundaryF :: tl -> pno_floor tl && pno_mode tl
  | PSiteF _ :: tl   -> pno_floor tl && pno_mode tl
  | _ -> false
```

A residual begins with the frame whose meaning the consumer decides, and between
that frame and the residual's end there is neither a scope floor nor a nearer
mode marker. Since `ctx_drive` appends the consumer's own marker at exactly the
residual's end, this *is* "between a boundary or site frame and the marker that
answers it there is no scope floor".

Seven lemmas, all **proved**. Two carry the argument:

- `lemma_pyield_residual_wf` — production: every residual this machine puts in
  the store satisfies `presid_wf`;
- `lemma_ctx_drive_answers_head` — consumption: driving a well-formed residual
  reaches, at its head frame, **the driving consumer's own** marker, runs that
  responder, and **allocates nothing** (`cf2.next == cf.next`).

Under the farthest cut the second conclusion is not merely unprovable but
**false**, and `guard_far_drive_reyields` runs both residuals on the same
machine to show it:

| | answer | `next` |
|---|---|---|
| nearest | `PV 7` | 0 |
| farthest | **`PCtxKey 0`** | **1** |

So under the farthest choice `resumeScope cx k` does not resume: it yields
again, allocates a *second* context, and the answer is that handle. B1.7's
reading — "cutting too far appears merely to defer the inner cut by one
round" — is withdrawn.

**No hypothesis assumes any part of the conclusion.** The two hypotheses used
are branch conditions of `pstep` itself (`pfind_mode rest == None`; the head is
a boundary or a site), and `lemma_pstep_yield_guard` checks that those are the
only routes to `pyield`. The surrounding stack stays universally quantified;
there is no shape assumption and no reachability assumption.

*Why B1.7's fixtures could not see it*, now checked as `fixture_22`: two floors
are not enough — a **live mode marker must sit between them**. A value passing
a `PModeF` pops it, so consuming a context inside a scope's *body* never builds
the configuration; entering a scope from **inside a resumption's continuation**
does. Fixtures 14 and 15 are confirmed not to reach it.

Two F\* traps were recorded in passing, and the second is reusable:
`pfind_mode (a @ (PModeF m r :: t)) == Some (m, r)` is true but resists
induction, because the goal names a pair whose second component is a function
— the base and step cases each go through and the whole fails on incomplete
quantifiers. Stating transparency instead (`pfind_mode (a @ t) == pfind_mode t`)
stays first-order and goes through, without weakening what is proved.

### Gate B2a, strand 2: what it must not assume

Strand 2 is the configuration-wide statement: extend `pconf_wf` — today only
the store's freshness invariant — with a stack condition, and prove that the
machine preserves it. It cannot be done as an unconditional `pload`/`pstep`
theorem.

> **"Every reachable stack is well-bracketed" is false for an arbitrary initial
> `pcomp` and an arbitrary `papply_t`.** A raw `PSplice` can push any frame
> list, and `apply` can return one.

So the layers are: a well-scopedness condition on the initial term; a
preservation condition on the clause interpreter; conditions on the stack and on
the `pctx` values in the store; a configuration invariant composing them; that
`pload` establishes it from the initial condition; and that `pstep` preserves
it. The shipped machine already names the counterparts — `ws`, `apply_ok`,
`clause_ok_congr`, `wf_state` in `Hoop.Runtime.Metatheory.fsti` — so this is a
precedent to follow rather than a design to invent.

One thing to settle **before** building those layers: the store holds
`PCtxRequests`, which carries a `post : pval v -> pcomp v cl` beside its
residual. If `post` may return an ill-formed `PSplice`, keeping every residual
`presid_wf` does not close reachability, and the function component needs a
condition of its own.

Until strand 2 closes, strand 1's result is local: it is about what a step does
given its own guard, not about which configurations the machine can be in.

#### Strand 2, run: the layers came apart, and that is the result

The stop condition did not fire, and nothing added in this gate is
stated-but-unproved. But the six layers the gate was posed with did not stay
six: settling the `post` question first split the work into **two layers needing
different hypotheses**, and that separation is the finding.

**Layer A — the store, UNCONDITIONAL.** `lemma_pstep_store_resid_wf` requires
only that the store already satisfies the invariant; nothing about `lk`, about
`apply`, about the stack, or about the initial term. Three rules write the
store, and each closes on its own: `PScopeF` allocates a `PCtxDone`, which has
no residual; `pyield` allocates the segment above the **nearest** floor, where
strand 1's cut lemmas give `presid_wf` from the branch guard alone; and
`PExtendCtxC` copies an already-stored residual, changing only `post`.

> **Nearest delimitation does the work reachability would otherwise have had to
> do.**

The consequence lemma the gate existed for, `lemma_reachable_residual_wf`, has
**no `requires` at all**: every residual in the store of any configuration
`psteps` can reach satisfies `presid_wf`. And
`lemma_stored_residual_answers_head` restates strand 1's consumption theorem
with its hypothesis *discharged from the store* rather than assumed of a
hand-written residual. The two strands close against each other.

**Layer B — the stack, CONDITIONAL, and it buys something else.** `pwb` is
deliberately *not* the strong bracketing property the strand-2 warning says is
false. It does not claim a boundary is matched by the floor its own `PEnterCtx`
pushed; it claims only that the search a boundary runs lands on something —
which is what a raw `PSplice` can be asked to respect. With an initial-term
condition (`pterm_wb`) and an interpreter condition (`papply_wb`), the payoff is
`lemma_reachable_not_paused`: **`PPaused` is unreachable from `pload`** for any
conforming term, any conforming interpreter, any lookup, any fuel. B1.6's
`fixture_9_paused_is_unreachable` — thirteen programs at one fixed fuel — is
now a theorem.

*The `post` question came out no, and only about shape.* `extend_ctx_C` copies
the residual and composes onto `post` alone, so `presid_wf` survives any number
of extensions; and `ctx_drive` runs `post` only on a stack carrying the driving
consumer's own `PModeF`, where the shape obligation is discharged by the left
disjunct without looking at the term. Both proved. **This is "no shape
obligation", not "no obligation"** — whether `post` needs a condition for
B2b's laws or B3's simulation is untouched, and the module now says so at
the answer.

*Non-vacuity.* `papply_wb` is proved of the fixtures' real interpreter, and
`pterm_wb` of forty programs — `prog1new` / `prog1old` for **every** `n` —
with the check itself fired by inserting an ill-formed `PSplice`. The ledger
naming those programs is **maintained by hand**: nothing detects a fixture
added and not listed, so the claim is about the listed programs, audited by a
reader.

*Following the shipped machine.* `pterm_wb_n` mirrors `ws_n` / `wf_stack_n`, and
the step-indexing was **forced, not stylistic** — the plain structural
definition is rejected at exactly the `option`-wrapped return-clause positions,
because the subterm ordering gives the application step only where the function
is an immediate constructor argument and `Some` interposes. The shipped machine
took the same repair for the same reason. Divergences, each deliberate: no
`cok` / `can` / `clause_ok_congr`, because `pterm_wb` is about frame shapes and
never mentions an effect label; **`PStuck` is `True` where `wf_state` sets it
`False`**, because here `PStuck` is reachable *by design* — a forged handle,
an unhandled operation — so excluding it would make the invariant false; and
the store layer has no counterpart at all.

*The `PWeave` clause, measured at the judgement.* `pints_wb` had no program to
exercise it, since nothing in this prototype produces a `PWeave`. Two type-level
guards now differ **in the return clause alone** and pin that the condition
admits a `Family` prompt carrying a real return clause
(`guard_wb_weave_accepts`, proved, not `assert_norm`) and refuses a malformed
one (`guard_wb_weave_rejects`, stated directly as `~(pterm_wb ...)`). The
refutation goes through the intended route — `pints_wb` → `pret_wb` →
`pterm_wb` → `pwb [PBoundaryF] = false` — checked by making the broken
clause well formed and watching the proof fail at the splice step. A
non-trivial return clause rather than `None` is the point: the `None` arm is
`True` in one step, so a `None`-built guard would pass even against
`pints_wb = True`.

#### Where B2a leaves it

> Nearest delimitation unconditionally preserves the association invariant of
> every stored residual, while a separate, non-vacuous well-bracketedness
> judgement excludes paused configurations for well-formed programs and
> preserving clause interpreters.

### The trace-aware gate: the acceptance conditions

Next, and it is not polish. Comparing two `prun` results at one fixed fuel is
not enough; the observation relation itself has to change.

| # | condition |
|---|---|
| 1 | convergence is to **trace + final value**, in the form "there exists a finite step count" |
| 2 | observational equivalence preserves convergence to the same trace and value, in both directions, from the same initial stack / store / counter |
| 3 | the relation does not depend on any concrete fuel |
| 4 | forgetting the trace, the new relation **implies** the existing value relation — proved |
| 5 | the residual and suspension versions are **not** equivalent under it, though their values agree — fixed as a theorem or a guard |
| 6 | `PEmit`s raised by the ambient stack or the clause interpreter are included, with order and multiplicity preserved |
| 7 | `pstep`/`pstep_tr` and `psteps`/`prun` correspond by trace erasure — proved, so the two semantics cannot drift apart |
| 8 | the five laws remain well typed when retargeted at the new relation; **proving them stays B2b's** |

With these, B1.6's exact-once fixture is connected to the laws and to simulation
for the first time.

One comment in the module is scheduled to go stale here, deliberately. `prun`'s
doc says that threading a trace through the laws "is a different and much
stronger claim than B2 is being asked for". That was true when written and is
now superseded: since B1.7 it is a *requirement*, because a value-only relation
lets a prefix-replaying implementation satisfy every law. Rewrite it in the
trace gate **with the history**, as a claim promoted rather than a sentence
quietly replaced.

#### The trace gate, run

All eight conditions are in place and the module verifies; 6,447 → 7,123
lines.
The definitions:

```fstar
let pconverges_tr lk apply cf tr x : GTot prop =
  exists (n: nat).
    (fst (prun lk apply n cf)).st == PDone x /\ snd (prun lk apply n cf) == tr
```

with `pobs_tr_le` quantifying over stack, store, counter, trace and value, and
`pobs_tr_eq` its two directions. **All five laws are retargeted at
`pobs_tr_eq`**; no law mentions the value-only relation. Proving them is still
B2b's.

`lemma_prun_stable` is the lemma that makes the existential mean anything: its
conclusion is an equality of **pairs**, `prun (n+extra) cf == prun n cf`, fixing
the terminal configuration and the trace at once. Its hypothesis is `~PStep?`,
which covers all four terminals rather than only `PDone`.
`lemma_pconverges_tr_unique` turns it into "at most one trace and one value per
configuration".

`prun`'s comment was rewritten with its history intact — *A JUDGEMENT
PROMOTED, AND THE HISTORY IS THE POINT*, quoting B1.6's sentence and marking it
**superseded, promoted, not corrected**.

#### The gate ran without a report, and what that cost

The authoring session was killed by infrastructure failures five times and never
produced one. The work was on disk and verifying, so a separate audit session
was run against it — which is a worse position than a report from the author,
and the difference showed up as **one overclaim that survived into the file**.

Sixteen mutations were fired in total, four by hand before the audit and twelve
by it, each with its rejection line read. The results worth keeping:

- **Condition 4 (forget) had been entirely unfired** and is the part the audit
  paid for. Redirecting `lemma_pconverges_tr_forget` at the wrong computation,
  weakening the hypothesis to `True`, and removing the appeal to
  `lemma_prun_erase` each fail in an isolated place — so the implication is
  neither vacuous nor independent of condition 7's erasure theorem.
- Removing the store, counter or stack quantifier from `pobs_tr_le` each fails
  in `lemma_pobs_tr_le_forget`; so does collapsing `pobs_tr_eq` to one
  direction. **The separation guard does not detect that last one** — the
  forget lemma is what carries it.
- Bounding the existential (`exists n. n <= 400 /\ ...`) fails, so condition 3
  is measured and not merely observed in the syntax.
- Condition 6 is fire-tested in both respects: multiplicity by deleting one
  duplicate emission, order by transposing two events.
- One mutation is recorded as **worthless**: replacing a trace literal
  file-wide was caught by a B1.6 fixture long before reaching the new guard. F\*
  halting at the first error makes that the standing hazard, and the fix is to
  scope the mutation to the guard's own lines.

**Condition 8 cannot be fire-tested, and that is itself a finding.** Reverting
`law_left_identity` to `pobs_eq` verifies — as it must, since nothing in the
module depends on any law holding. So "the laws are retargeted" is established
by reading, not by an obligation, and a law silently reverting would be caught
by no proof in this file.

#### The overclaim, corrected

The file said `pobs_tr_le` is **strictly** stronger than `pobs_le`, and the
header said the laws are **strictly harder** than they were. What
`lemma_pobs_tr_le_forget` proves is the implication one way. Strictness needs a
witness — a pair the value-only relation joins and the trace-aware one does
not — and the file does not have one: it records elsewhere, correctly, that
`pobs_eq flook fapply prog_traced prog_susp` is *neither claimed nor checked*.
Both sites now say **at least as strong / at least as hard**, with the missing
witness named. The proof was never wrong; the sentence was.

Smaller findings, recorded and not repaired: `lemma_fend_is_frun` is proved and
never used; `guard_amb_scope_prefix_once`'s comment attributes to itself an
ordering fact that its neighbour `fixture_23` actually establishes; the file
proves only **negative** instances of the new relation, so nothing here shows it
is loose enough to relate two different programs — which the gate did not ask
for, but which means this file offers no evidence that the five laws *could*
hold. And `pobs_tr_le` quantifies over store and counter without requiring
`pconf_wf`, so it demands agreement at configurations the machine cannot reach.
That makes the relation stronger, not unsound, and it was inherited from B1.7
rather than introduced here — but it is a way the laws could turn out false
for reasons having nothing to do with the algebra, and B2b should meet it
knowingly.

Four claims of the form "strictly stronger" were corrected across the module in
the same pass, all the same error: **taking a parameter, enlarging a domain, or
proving an implication one way does not establish strictness — that needs a
witness of non-equivalence, and this file has none.** So the laws now say that
exposing `lk` as a parameter lets B2b state them uniformly (not that it
strengthens them), and that deleting `settles` puts the ambient-handler
configurations *inside* the obligation (a claim about the domain, not about
logical strength).

#### How B2b should start, and when it should stop

**Prove one small positive instance first** — ideally a `pobs_tr_eq` between
two *different* programs. Everything the file establishes about the new relation
today is negative: separations, and a reflexive inhabitant found only in an
audit scratch copy. Nothing shows the relation is loose enough to relate two
distinct programs, so nothing yet suggests the five laws *can* hold.

And a stop condition, because the relation quantifies over stores and counters
without requiring `pconf_wf` and therefore demands agreement at configurations
the machine cannot reach:

> If the first law fails **only** because of ill-formed or unreachable
> configurations, do not push the proof through. Stop and decide whether the
> observation relation belongs over all configurations or should be restricted
> to well-formed reachable ones.

### Gate B2b: all five laws are false, and that is the result

Every one of the six propositions — the five laws, with `law_assoc`'s two
conjuncts counted apart — is refuted **as a proved negation**, not left as a
proof undone.

**This is not an implementation failure.** `ref_ops` is not wrong; production
*must* allocate, because a handle has to name something in the store. What the
refutation found is a defect in the **specification**: the observation relation
was exposing the allocator's internal names. B2b caught a wrong specification by
proving it wrong, which is what a gate is for.

*The mechanism.* `pobs_tr_le` fixes the store and counter at the start and
compares a `pval v` at the end; `pval v` contains `PCtxKey i`; `palloc` hands
out `cf.next`. **So the name of a freshly allocated handle is observable.**
Every law's left side allocates at least one context and its right side
allocates none, so an ordinary continuation that produces a context of its own
and returns the handle reports `PCtxKey 1` on the left and `PCtxKey 0` on the
right. At `plan_A = Plan [] fowner_plain` laws 1, 2 and 5 have literally the
same two sides, so one program pair refutes three propositions; `law_resume`
is 1 vs 0 and `law_assoc`'s anchored half is 2 vs 0.

**Both traces are empty.** The trace-aware work contributes nothing to this
separation — which is worth stating plainly, because it means the previous
gate was not wasted but was also not what caught this.

*The stop condition did not fire, and was refuted rather than assumed away.* The
counterexample stands at `pload`'s **own** store and counter — empty, zero —
and `guard_ce_conf_one_step_from_pload` proves the configuration is exactly one
`pstep` from `pload` of a closed program, with `guard_ce_conf_ok` establishing
the whole `pconf_ok` invariant through B2a's preservation theorem. For
`law_assoc`'s algebraic half, the only statement naming a context it did not
produce, `guard_ce_aa_reachable` proves store, counter and stack together are
what five transitions of a closed program reach.

*Fired at the mechanism, not only at the arithmetic.* Making the continuation
not allocate — `fnew_ctx` returning a plain value instead of entering a scope
— breaks the refutation at `guard_ce_runs_differ`. Allocation is what does it.

*What proving a positive instance first bought.* Two were proved before any law
was attempted, as required: `pbind (PVar x) f ≈ f x`, and `PSplice [] c ≈ c`
at an **arbitrary** `c`. They needed a silent-step calculus, and that
calculus is recorded as **not** a bisimulation — it relates programs only
when they converge on a common configuration, so it proves the administrative
equations and no others. That is precisely the wall the laws hit, met at the
first step rather than at the fifth.

*Two things that would not have helped.* `settles` would not: the counterexample
performs no `PPerform` at all, so it lies inside every domain `settles` carved
out. And restricting the observable to the image of `PV` would not: quite apart
from putting first-class handles outside the laws, the very thing B1.7 was for
— `fseen` and the result of resolving a handle can carry a key difference
back into a `PV`.

*A correction the refutation forced.* The note on `flat_ops` claimed that left
identity, right identity and the algebraic half of associativity all hold of it.
That is false of the propositions this file defines — `law_left_identity` is
now false of **all three** implementations, so it discriminates none of them.
The claim is corrected in place; the argument behind it (a uniformly wrong
algebra satisfies every equation between its own operations, so at least one
law must be anchored) still stands.

### Gate B2b.1: nominal observation for first-class contexts

The repair is to the relation, and **"store isomorphism" is not the right
statement of it** — the two sides allocate *different numbers* of contexts, so
their stores differ in size and no bijection between whole stores exists. What
is needed is a **world-indexed partial bijection on reachable handles, ignoring
garbage**:

- a world `W` is a finite partial bijection between the keys reachable from the
  outside on each side;
- `PCtxKey i` and `PCtxKey j` correspond when `W(i) = j`;
- corresponding store entries correspond in *behaviour when consumed*;
- entries unreachable from any public handle are **garbage** and are ignored;
- `next` is not observed at all — only freshness on each side is required;
- when a new handle becomes externally visible, `W` is extended by a fresh
  correspondence;
- **aliasing is preserved**: the same key twice maps to the same partner, two
  different keys to two different partners;
- the trace is matched exactly, as now. If handle names are ever put into the
  trace, the same renaming applies to that part and to nothing else.

**Handle opacity has to come with it.** In the model today `PCtxKey nat` can be
destructured by any F\* function, so a continuation can *guess a future key*.
Quantify over arbitrary continuations and any name-quotient whatever is broken.
The real PureScript API publishes neither the constructor nor a numeric
representation, and the model has to reflect that. So the gate is two things
together, not one:

1. the world-indexed relation on handles and stores;
2. an **equivariance discipline** — continuations, the clause interpreter and
   `post` commute with key renaming.

The second must not be an unchecked assumption. It has to be discharged the way
`papply_wb` was: satisfied by the real `fapply`, and preserved by the machine's
transitions.

| # | acceptance condition |
|---|---|
| 1 | the six counterexamples are related under a suitable world extension, rather than at equal raw keys |
| 2 | B1.7's two distinct live handles are **not** collapsed |
| 3 | aliasing, and the order in which handles are selected, are preserved |
| 4 | handles whose contexts behave differently are **not** related |
| 5 | forged and stale handles still fail, with no fallback to nearness |
| 6 | only unreachable store entries are ignored as garbage |
| 7 | the two positive instances and the trace-based suspension separation survive |
| 8 | the trace is not weakened to achieve any of the above |

Stop conditions:

> - equivariance of an arbitrary F\* closure cannot be established without
>   `assume`;
> - the counterexamples can only be removed by also identifying distinct live
>   handles, or by losing aliasing;
> - hiding a replay requires weakening the trace observation;
> - the laws remain false after the nominal difference is quotiented away,
>   because of the **semantic** difference in frame lists.

The last case is not a reason to loosen the relation further. It sends the work
back to the algebra and the transitions — specifically the bisimulation
between `plan_protocol_frames` beneath a `PModeF MExtend` and
`plan_enter_frames`, which
`law_right_identity` needs and which this gate did not attempt.

#### The feasibility probe: it works, in a scratch model

Run before committing a line to the prototype, in a self-contained 1,191-line
scratch module — the same instrument that settled strict positivity earlier.
It verifies with no `admit`, no `assume` and no weakening pragma, and it first
**reproduces the defect** (`guard_naive_separates`), so it is a model of the
problem and not of something easier.

*Expressible.* A world is a `list (nat & nat)` whose well-formedness is a
**biconditional** between the two lookup directions — and that biconditional
*is* the aliasing clause, forcing partial-functionality and injectivity at once.
The relation is step-indexed and world-indexed, and needs a **lexicographic**
measure `%[n;0]` / `%[n;1]`: `ctx_rel n` must call `comp_rel n` at the *same*
index, because the stored `post` is applied to a fresh argument rather than a
subterm. A plain `decreases n` is rejected. No positivity or universe obstacle.

*Equivariance is a usable hypothesis, and a proper one.* Seven lemmas discharge
it for concrete contexts and continuations — including the counterexample's
own `knew`, which allocates and returns a handle — and

```fstar
guard_kguess_not_equivariant : ~(equivariant_fn (fun _ -> MRet (MKey 5)))
```

refutes a continuation that *guesses* a key. **Handle opacity comes for free**:
nothing is made abstract; the guessing continuation simply falls outside the
quantification.

*The payoff.* `guard_ce_nobs_eq` relates the counterexample, and the world
extension is exactly **one pair, `1 ↦ 0`** — the left run's own discarded
context never enters the world at all, because `srel` constrains only the
world's domain, which is what lets the two sides hold different numbers of
contexts. `guard_defect_config_is_in_scope` proves the offending continuation,
store and counter satisfy *every* hypothesis the new relation imposes: **the
repair does not work by excluding the program that exposed the defect.**

*It does not overshoot.* Distinct live handles stay distinct, contexts whose
`post` behaves differently are related at no world, and the trace still
separates them observationally — three proved lemmas. Loosening `val_rel` to
relate all keys was fired and fails, though it fails inside the fundamental
theorem rather than at those three, so what it shows is that the loosened
relation cannot support the development at all.

*Three F\* traps, recorded because they fail silently.* Writing `Some?.v` inside
a `prop` definition type-checks and then quietly prevents SMT instantiation —
use a total accessor with a junk default. The store relation's quantifier needs
an explicit `{:pattern}`, since the automatic trigger only fires when both sides
appear in the goal. And `introduce ~(p) with e` is a syntax error; universally
quantifying the fuel in the antecedent avoids a whole class of friction with
existentials. Each presents as "obviously true goal will not prove", three
lemmas downstream.

#### `cl` gets a relation, not a stronger hypothesis

The prototype's `cl` is abstract, and a `cl` value reaches `apply`. The tempting
repair — strengthen `apply`'s equivariance until the content of `cl` stops
mattering — **is wrong, and the reason is specific**: a clause may capture an
existing handle in its closure. The two runs then hold *different* `cl` values
that correspond under the world, not the same one. A same-`cl` condition would
either exclude handle-capturing clauses, which a general higher-order facility
must permit, or silently assume the captured handles carry equal raw keys.
Relating arbitrary `cl` values is equally wrong, since `apply` must tell
different operation clauses apart.

So `cl` needs an explicit `cl_rel w c1 c2`, and the pieces belong together
rather than scattered as bare parameters:

```fstar
type nominal_boundary v cl = {
  cl_rel: world -> cl -> cl -> prop;
  lookup_equivariant: ...;
  apply_equivariant: ...;
}
```

with `table_rel` saying that corresponding tables' lookups return
`cl_rel`-related clauses. Building this record for the concrete `flook` /
`fapply` is what shows it non-vacuous. **This is a new verification boundary
stacked on `papply_wb`, not an unchecked `assume`** — the same discipline, one
level up.

Before fixing every signature, one more scratch condition is worth running: a
left clause capturing `PCtxKey 5`, a right clause capturing `PCtxKey 6`, a world
sending `5 ↦ 6`, `cl_rel` relating them, and `apply` still producing related
results when the captured handle is used — together with the observation that
the same-`cl` formulation **cannot express this example at all**.

#### Fuel: separate the step index from the transition count

Do not carry a hand-computed step offset per law. The probe's model bounds
*depth* and can state its fundamental theorem lockstep; the prototype counts
*transitions*, and the two sides genuinely take different numbers of them. Keep
the two roles apart:

- the **step index** exists to make the store/context relation's recursion well
  founded;
- the **transition count** is existentially quantified, independently on each
  side, inside `pconverges_tr` — which already hides fuel, so a world-indexed
  version may admit different convergence witnesses on the two sides;
- the **trace** matches exactly;
- silent transitions are absorbed once, by a general `prun` decomposition lemma
  and a trace-preserving silent closure.

> **If a machine-specific constant — a `+3`, a `+7` — appears in a law's proof,
> stop and go back to the alignment layer.** That constant is the thing that
> breaks the next time the machine is touched.

#### What the equivariance hypothesis corresponds to on the surface

It is the universal quantification of `ctx` in `ScopedClause`'s rank-N type. A
clause is written against a **rigid** `ctx`, so it cannot inspect one, compare
two, or fabricate one — only pass them to the tactics or carry them around.
Parametricity in `ctx` *is* equivariance, and the same quantifier that pays for
the FFI `magic` into `weave` now also carries the laws.

**This is a constraint on us, not a usage discipline for users.** The quantifier
is in a type the library writes; a user cannot add a constraint to a `forall`
they did not write, and no instance resolves for a rigid variable. The invariant
is lost only if *we* change the surface. Users reach it only through
`unsafeCoerce` or hand-written FFI, which are standing TCB items that break
everything equally.

The precise criterion, which is not "no type classes":

| | equivariant? |
|---|---|
| carrying, storing, selecting between handles | yes — this is what B1.7 bought |
| `Eq` by identity | **yes** — a bijection preserves equality |
| `Ord` | no — allocation order is not preserved by a renaming |
| `Show`, numeric conversion, hashing | no — the key's value escapes |
| exporting a concrete representation | no — and no class is involved |

The shipping rule stays the conservative one — no constrained `ctx`, no
concrete exposure — but the criterion is recorded so a future request can be
*evaluated*: `Eq` is admissible at the cost of one more proof obligation,
`Ord` is not, and the substitute for `Ord` is to carry insertion order
separately. Once B2b.1
fixes the relation, this belongs in `test-compile-fail/` so the build fires
instead of a reviewer remembering.

`fseen` is fixture instrumentation and is outside the nominal theorem — it
breaks handle opacity deliberately, and no transition applies it.

#### The correction: global equivariance was the empty-anchor instance

The probe's first equivariance predicate quantified over **every** well-formed
world. That is stronger than `nobs_le` needs, since `nobs_le` already restricts
to worlds extending `anchor s` — and the excess had teeth: it excluded
**legitimate handle-capturing continuations**, not only dishonest ones.
`fun _ -> MRet (MKey 5)` is *syntactically identical* whether the key was
guessed or captured honestly from the ambient store, so a predicate that looks
only at the term throws out both.

The central finding, and it is checked:

```fstar
lemma_global_is_empty_anchor f : Lemma (equivariant_fn f <==> equivariant_fn_at [] f)
```

**The old notion was not a different concept. It was the anchor pinned at `[]`
— at no ownership — for every closure however much provenance it actually
had.** The corrected definition adds one conjunct, `wext w w0`, and nothing
else. Deleting an over-approximation, not adopting a new idea.

> Equivariance is not invariance under every world. It is invariance under every
> future world extending the correspondence the closure already owns.

The distinction is not a syntactic mark on the term; it comes from the
**provenance carried by the starting world**. Empty anchor: `MKey 5` is an
unowned future name, `5 ↦ 6` can be chosen, not equivariant. Anchor pinning
`5 ↦ 5`: the same term is a legitimate capture and is self-related. Starting
world `5 ↦ 6`: two closures capturing `5` and `6` are equivariant *with each
other*.

#### The six conditions

All proved, at default rlimit and fuel. Three are worth drawing out.

*Condition 2 admits a real capture, not a mention.* The admitted closure
`fun _ -> MUse (MKey i)` actually **consumes** the captured entry.

*Condition 5 is the one with content, and it was fired.* `nobs_le_reanchored`
differs from the real relation in **one token** — `anchor s1'`, the left run's
final store, for `anchor s` — and it separates the counterexample.
Re-anchoring pins the left run's *garbage* key — the context it allocated and
discarded — as a public name, colliding with the correspondence the answer
needs. Rewriting
the real `nobs_le` this way breaks `guard_ce_nobs_le`.

*Condition 6's refusals are stated at an anchor that pins the captured handle*,
so they are not condition 1 recycled: a closure may honestly own `MKey 3` and
`Ord` is still refused, because a legal future world can relate `MKey 1` to
`MKey 5` while `3 < 1` and `3 < 5` disagree.

A closure the probe added unasked, because weakening a hypothesis is where holes
open: `guard_ownership_is_bounded_by_the_store` proves an anchor pins only keys
the store already holds, and the store holds nothing at or above the counter.
**So relativising to the anchor licenses capture and never guessing** —
without it, "relative to the anchor" would invite making the anchor large
enough to launder anything.

*What moved.* `lemma_fund` is byte-identical; so are the relation layer, the
world layer and every monotonicity lemma. `nobs_le` changed by one line and the
existing guards took substituted preconditions with their proof bodies
unchanged. The relativisation lives entirely in the **hypothesis layer**.

The strength claim, stated carefully. What is proved is that the admissibility
hypothesis is **strictly weaker** — implied by the old one, and satisfied by a
capturing closure the old one refuses. So the revised `nobs_le` quantifies over
a strictly larger class of continuations and is **at least as strong** as the
old relation, and proving a positive result under it is materially harder.
*Strictness of `nobs_le` itself* would need a separating program pair — one
the old relation joins and the new one does not — and is not claimed.

#### Continuations and clauses converged on the same shape

`NominalClause` concluded independently, for clause *values*, that a same-`cl`
condition cannot work: **no** handle-capturing clause satisfies any single-sided
condition, at any operation, behaviour or key. The corrected `fn_rel_at` is that
same conclusion for continuations, and its two-sidedness is forced by the same
fact — the two runs hold *different* closures, each having captured what its
own run allocated.

> Anything crossing the boundary that can capture a handle is related **pairwise
> at a world**, never constrained pointwise.

That is one story rather than two, and it is also the change with the largest
surface area on the way in: a boundary phrased single-sidedly has to be
rephrased.

#### The boundary obligation, and what it does and does not cost the TCB

`cl` is abstract in the prototype and, in the shipped machine, is an opaque
closure handed over by the FFI — `Hoop.Runtime.Syntax.fst` says so in as many
words: F\* "can guarantee nothing about the invariants enforced by the PS type
system". A clause can therefore capture a live handle, and `cl` needs

```fstar
cl_rel : nat -> world -> cl -> cl -> prop
```

step- *and* world-indexed. It need not join `comp_rel`'s mutual block: carried
as an abstract relation family in a boundary record, with the step index lowered
one notch to break the cycle. Structural for the first-order fixture `fcl`; a
boundary obligation for opaque closures.

**The TCB statement, precisely.** Defining `cl_rel` and proving the coherence
conditions of the concrete `flook` / `fapply` costs the TCB nothing. What
enlarges it is only the extent to which the extracted / FFI clause closures are
**assumed** rather than proved to satisfy `lookup_equivariant` and
`apply_equivariant`. That is the same responsibility boundary `apply_ok` and
`apply_scoped_ok` already occupy, with one nominal two-sided condition added.

#### Open: nesting, and sibling worlds

Everything above is at a **single level of nesting**. The monotonicity lemma
says an outer closure's obligation survives later allocation, and says nothing
about reconciling two anchors when an inner closure escapes past the outer one's
scope. Multi-shot resumption with first-class handles makes the sibling case
real as well: two branches from a common anchor each return a closure, and the
world extensions they chose independently have to be usable together.

#### The last scratch gate before the prototype

One example, carrying all of:

| # | condition |
|---|---|
| 1 | an outer closure captures an outer handle |
| 2 | an inner scope allocates a new handle |
| 3 | an inner closure captures **both** the outer and the inner handle |
| 4 | that closure **escapes** the inner scope |
| 5 | it is called later, at a world where further allocation has happened |
| 6 | both the outer and the inner aliasing are preserved |
| 7 | the proof uses monotone extension only — **no re-anchoring** |

plus, if it can be reached, the sibling case: two branches from one anchor each
returning a closure, both usable afterwards, their independently chosen
extensions reconciled without conflict.

Stop conditions:

> - an escaping inner closure forces re-anchoring the whole store;
> - two sibling worlds cannot be reconciled;
> - equivariance has to be re-proved at each closure's creation site;
> - monotone extension alone cannot preserve outer provenance.

And a porting note to keep: `guard_c5_reanchoring_breaks_the_repair` is the
guard to move across **first**, ahead of any positive result. Re-taking the
identity over the current store at each step is the obvious implementation of
"the anchor" — cheap, and it looks conservative. It is unsound at scale, in
the precise sense that it separates programs that should be equal. The correct
discipline — starting world, one explicit pair per allocation, nothing else
— has to be visible in the code rather than merely respected by it.

#### The gate, run: nesting is shallow, siblings are not

Three modules verify from a clean cache; the two earlier ones are byte-identical
(the new material is a sibling module, so "the existing results survive" is a
mechanical check rather than a claim). No `admit`, no `assume`, rlimit at most
10.

**1. Nesting needs monotone extension and nothing else.** All seven conditions
proved in one example: an outer closure capturing an outer handle, an inner
scope allocating, an inner closure capturing *both*, escaping, and called later
after further allocation, with both aliasings preserved. `lemma_fund` and the
relation layer are **unchanged** — what was missing were four *introduction*
lemmas, since the base module had only needed elimination. Nesting turned out
shallower than it looked.

Aliasing preservation is observable rather than asserted: the inner closure
compares its two captured handles with `veq`, emits a tag, and consumes the
inner one, so a broken aliasing shows up as **diverging traces**. And the
example does not take the easy road — `~(equivariant_fn k_amb)` is proved, so
the ambient continuation is one the old global notion refused and only
anchor-relativisation admits.

**2. The unconditional re-anchoring policy is refuted by a witness.** Stated
carefully, because the strong reading is not what was shown:

> In this concrete configuration — one with an escaping nested handle — **no
> world is compatible with the policy of re-taking the identity mapping over the
> current store.** So an implementation that re-anchors unconditionally is
> rejected. Configurations where re-anchoring happens to be consistent (nothing
> allocated, say) are not ruled out.

```fstar
guard_A_no_reanchoring_at_the_escape (w:world)
  : Lemma (requires val_rel w (MKey 9) (MKey 8))
          (ensures ~(wext w (anchor sl_escape)))
```

The practical consequence is good: a re-anchor introduced during the port fails
*as an unprovable goal*, not as a silent behaviour change.

**3. `wcompat` is necessary and sufficient for joining two fixed worlds.**

```fstar
lemma_wunion_wf         : wcompat wA wB ==> wA @ wB is wf and extends both
lemma_wcompat_necessary : a wf world extending both exists ==> wcompat wA wB
```

Being *necessary* is what makes the next item a result rather than a limitation
of one proof attempt: there is no definitional adjustment that avoids it.

**4. Rolling the allocator back makes sibling branches unjoinable.** Two
branches from a common anchor, each returning an escaping closure that captured
what its own branch allocated, join fine — **unless both start from the same
counter**, which is exactly what a multi-shot resumption does when it restores
the allocator along with the continuation:

```fstar
guard_B_fork_no_join (w:world)
  : Lemma (requires wf_world w /\ wext w wA_fork /\ wext w wB_fork)
          (ensures False)
```

The obstruction is neither size nor freshness: the two branches **disagree about
who owns the right-hand name**, and a world is a bijection, so it cannot hold
both opinions. The contrast experiment isolates it — same branches, same
discarding, and the only difference is whether branch B starts from the counter
branch A left or from the counter branch A started with.

**5. The semantic invariant this yields**, which is *not* "a global counter":

> **Jointly observable branches must allocate distinct, stable identities. An
> identity must not be reused while any handle carrying it may remain
> observable, unless one branch is freshened or namespaced before the results
> are joined.**

**6. The reference implementation's witness.** A global monotone counter, no
rollback, no reuse. That is fixed as the adoption condition of the *current*
reference semantics, and the prototype's non-reclaiming association list already
satisfies it.

**7. Alternatives are not excluded**, given an equivalence proof:
branch-qualified identities `(branch-id, local-id)`; generation-tagged slots;
stable object identity kept apart from dense storage; an indirection that
freshens one side at a merge; and reclamation after proving unreachability from
every continuation, closure and world. **What is non-negotiable is cross-branch
freshness and the stability of live identities, not the mechanism** — the
monotone counter is simply the only witness implemented today in the `nat`-key
model.

**8. An obligation this adds to B2b.1's structure.** It is not enough for each
branch to existentially choose its own future world; the results could then not
be combined afterwards. One of:

- thread a single monotone world/supply shared by sibling computations — the
  natural choice if the global store and counter are being modelled faithfully;
- or carry each branch's final world *plus* its `wcompat` and the join, as part
  of the result.

Designing the laws so that world witnesses are joined after the fact reproduces
the fork counterexample.

**9. Store enumeration must not be a public observation.** Exposing keys, a
count, an iteration order or a raw id through the language semantics, the public
API or a test observation breaks the repair at store granularity, for the same
reason `Show` on a key breaks it at key granularity. A developer-only diagnostic
that programs cannot read and that is not part of observational equivalence is
harmless — **but it becomes a semantic observation the moment its output
format is promised to users as stable.**

### B2b.1, run: the repair works, and its scope is one configuration deep

The module verifies from a clean cache at 8,215 → 11,059 lines, with **no
`z3rlimit` raised anywhere** — 2,800 added lines at the default. The world
layer, the step-indexed world-indexed relation (eight mutually recursive
relations under a lexicographic `%[n; level; size]`), anchor-relative
equivariance in two-sided form, and a `pboundary` record carrying `cl_rel`
together with `lookup_equivariant` and `apply_equivariant` are all in place, and
`prun` / `pstep_tr` / `pconverges_tr` / `pobs_tr_le` were not touched.

**The limitation, stated precisely:**

> B2b.1 proves the repaired relation's consequent for the former counterexample
> at one concrete configuration. It does not prove `pnobs_tr_eq`, whose
> universal quantification over equivariant ambient stacks, stores and
> boundaries requires a fundamental theorem for the whole machine.

So what this gate establishes is that **the repair bites on the concrete
counterexamples, and does not do so by banishing them from the quantification
domain** — `guard_nom_fk_new_equivariant` proves the very ambient stack that
defeated the old relation is admissible under the new one. Whether the repaired
equivalence holds *as a semantics* is B2b.2's.

Fired independently: relating all keys in `pval_rel` breaks
`guard_nom_eq_preserves_aliasing`, so the repair does not overshoot. (In the
scratch model the same mutation was caught inside the fundamental theorem and
never reached the negatives; here it lands on the negative property itself.)

Two of the ten mutations the port fired did not isolate, and are recorded as not
counting.

#### `fapply` is not equivariant, and that is the boundary working

`guard_nom_fapply_not_equivariant` **proves the negation**: no
`pboundary fv fcl` with `b_apply = fapply` exists. The cause is `fseen`, which
renders `PCtxKey i` complete with its raw name — the same shape as the `Show`
refusal. This is a **good boundary check, not a stop condition**, and neither
equivariance nor `fapply` should be bent to accommodate it. The separation to
keep is:

- **`fapply`, which carries fixture instrumentation** — outside the nominal
  theorem, by design;
- **a semantic / shipping interpreter that does not observe raw identity** —
  must be *proved* to satisfy the boundary discipline, by B3 at the latest.

That the record is inhabitable at all is shown at `ncl`, a clause language that
**captures handles**: `nboundary` is built, `lookup_equivariant` holds
constructively of `pref_lookup`, `apply_equivariant` is proved, and the
one-sided same-clause alternative is refuted there.

### Gate B2b.2: the nominal fundamental theorem

Not leftover work from B2b.1 — a separate gate, asking whether the repaired
relation closes over the whole machine. Completion conditions:

| # | condition |
|---|---|
| 1 | one step of related configurations goes to related configurations, with the corresponding trace and world extension |
| 2 | that step lifts to finite runs, so `pnobs_tr_le`'s universal quantification is actually derivable |
| 3 | `guard_nom_ce_related`'s instance is re-proved as a **corollary** of the theorem, not from hand-written witnesses |
| 4 | the theorem is instantiated at a non-trivial boundary such as `nboundary`, fixing that the boundary hypotheses are not vacuous |

If step compatibility and the lift to finite runs both turn out large, B2b.2 may
split internally into *transition compatibility* and *fundamental theorem*. One
row on the roadmap is enough.

### B2b.2, run: the fundamental theorem holds

11,059 → 13,673 lines, verifying from a clean cache in ~31s, and — as in
B2b.1 — **with no `z3rlimit` anywhere in the file**. No stop condition fired.

What is established, stated at the level each result actually reaches:

| result | scope |
|---|---|
| transition compatibility (`lemma_pstep_tr_compat`) | **universally quantified, proved** |
| finite-run compatibility (`lemma_prun_compat`) | **universally quantified, proved** |
| `pcrel` ⟹ `pnobs_tr_le` (`lemma_pnobs_tr_le_of_crel`) | **universally quantified, proved** |
| the former counterexample | **proved as a corollary** of the theorem |
| relating the two sides of a law | **not proved** — B2b redux |

The step theorem gives trace **equality** and a world that is a `pwext` of the
one it was handed; the world grows by exactly one pair, and only at the three
rules that allocate. The lift runs both sides at the **same fuel** and inducts
on it. **No re-anchoring and no fixed offset anywhere** — nothing computes a
world from a final store.

Independently fired: removing `pcl_down` from the step theorem's hypotheses
fails at `lemma_step_var`. The hypothesis is load-bearing, not decorative.

*Three limits, reported by the port rather than found in review.*
`prej_rel` compares an `UnborrowableScope`'s blocker labels **as a set**, because
`blocking_effects`'s refinement pins only the set; rejection is invisible to
`pnconverges`, so this weakens the step theorem's conclusion at that one state
and nowhere else. Condition 3 is an instance at one configuration. And the two
sides of a law are not related *as computations* — `pcomp_rel` relates only
matching nodes — so the universal form requires advancing both prefixes
symbolically, which is what proving the laws means.

**`pcl_down` moves into the boundary record.** It is an admissibility condition
on `b_rel` itself, exactly like `b_mono`, and both the fundamental theorem and
the observation theorem need it — so leaving it outside means a caller holding a
discipline-satisfying `pboundary` still cannot apply the theorem, and a future
use site can forget it. It is already proved of `fcl_rel` and `ncl_rel`, so
carrying it as `b_down` adds no trusted assumption. Done before the laws, where
it is cheapest. Lemmas stated at a bare relation rather than a boundary —
`lemma_pstep_tr_compat`, `lemma_prun_compat` — keep it as an explicit
hypothesis, deliberately: they are usable without a boundary.

Whether `pcl_down` is **derivable** from the other three conditions is not
settled in either direction. It is needed at index zero only, the one place
`ptable_rel` is not trivial, since a table inverted out of a frame speaks only
from index one up. Should it turn out derivable, the field becomes redundant
rather than wrong.

**An obligation left for B3:**

> If shipping rejection diagnostics expose blocker order, either canonicalise
> that order or prove that it is not a semantic or public observation. The
> prototype currently justifies only set equality.

*An F\* fact worth carrying to the next machine change.* A `GTot prop`
definition applied in **hypothesis** position is atomic — the quantifiers inside
it are invisible, `{:pattern}` or not — while in goal position it unfolds. This
is why `PPerform` was the hardest rule: `plookup_equivariant` and
`papply_equivariant` would not trigger. The repair is a `{:pattern}`-carrying
restatement plus a cast that goes through **by conversion alone, with no proof
obligation** — no definition had to change.

### B2b redux, run: refuted again, and this time the failure is localised

13,709 → 15,998 lines, verifying from a clean cache, still with **zero
`z3rlimit`**. All six propositions are refuted, and the reason is nothing like
B2b's.

**Judgement point 1 is answered YES for all six, and that is real progress.**
Each side of each law has a finite prefix computed in **general form** — plan,
inner computation, value, extension functions, ambient stack, store and counter
all variables — and the two prefixes land on the **same node**. No statement
relates the two sides' transition counts; `lemma_prun_split` does the composing.

**Judgement point 2 fails structurally, and the obstruction is proved in
general** — at every relation, world, plan, continuation and ambient stack:

```fstar
guard_align_produce_vs_enter r w pl f amb
  : Lemma (~(pkrel r w (PBoundaryF :: (plan_protocol_frames pl
                                       @ (PScopeF :: PBindF f :: amb)))
                       (plan_enter_frames pl @ amb)))
```

The argument is **length**. `pframes_rel` matches stacks cons by cons, and

```fstar
lemma_plan_frames_lengths pl
  : Lemma (length (plan_enter_frames pl) <= length (plan_protocol_frames pl) /\
           length (plan_resume_frames pl) == length (plan_protocol_frames pl))
```

*What that means.* **The laws are stated across two different projections of one
plan.** The left-hand side goes through production and so lives on
`plan_protocol_frames`, which keeps every `PIBind` as a dormant `PSiteF`; the
right-hand side goes through entering and so lives on `plan_enter_frames`, which
drops them. That difference is not incidental — B1.5 recorded it as "the whole
of the difference between entering a scope and resuming a perform site". A
cons-wise relation cannot match them, and it should not be expected to.

Note also that `plan_resume_frames` and `plan_protocol_frames` have **equal
length**, so the resumption law's two sides are separated by one marker only.
**Anchoring itself is not broken.**

*It is not about names.* Four of the counterexamples stand at the empty store,
the empty ambient stack and counter zero; two of them return the **same handle**
on both sides, so the world is forced and has nothing to choose. B2b.1's repair
works in every one of them. What no world can do is relate two residuals of
different length.

*The algebraic half's refutation is weak, and says so.* There the post-prefix
stacks are **identical**; the difference is that the marker's responder is one
bind chain under two bracketings. But the refuting interpreter **reads the
length of the segment it is handed** — a discretion `papply_t` has because
it is an arbitrary F\* function, and which an FFI closure that can only *call*
its continuation does not have. Whether the algebraic half is refutable by an
apply-only interpreter is **undetermined in both directions**.

*The one positive result*, and it is reusable: `lemma_obs_from_common` composes
**two independent prefix lengths** with a single invocation of the fundamental
theorem at the common configuration. The world is the theorem's and is never
written down.

*Six propositions are really five.* At `ref_ops`, `law_transparent_agrees_nom`
and `law_right_identity_nom` are the **same proposition** — a `prop` equality,
not an implication, and it says nothing about other `ctx_ops`.

### The repair: a mode-indexed administrative equivalence

The obvious reading of the obstruction, inserting an erasure into the laws, is
**wrong, and unsoundly so**:

- a `PSiteF` may not simply be deleted. Under `MExtend` it stays dormant and
  vanishes; under `MResume` it **fires, as the `PBindF` it was recorded from**;
- a `PModeF` is not an inert marker either. It **carries a responder**, and
  deleting a frame without showing the responders agree on all future behaviour
  is not sound.

And a law of the form `erase lhs ≈ erase rhs` would not say that `lhs` and
`rhs` mean the same thing — only that they agree once information has been
discarded before the comparison. The shape wanted is:

> `lhs ≈admin rhs`, and `≈admin` sound for `pnobs`, therefore `lhs ≈obs rhs`.

So the repair is three parts, and **`pcrel` is not one of them**:

1. **Keep `pcrel` as it is.** It is the strong lockstep congruence that carries
   the fundamental theorem, and it does that job correctly. This failure is not
   a reason to weaken it.
2. **Add an administrative relation for the laws** — a trace-preserving weak
   bisimulation or normalisation identifying: protocol production with the enter
   projection; a protocol consumer marker with the corresponding extend/resume
   projection; a dormant `PSiteF` vanishing under `MExtend`; a `PSiteF`
   reactivating as `PBindF` under `MResume`; and two bracketings of `pbind`.
3. **Prove that the administrative relation implies `pnobs_tr_eq`.** This is
   what keeps the user-facing law about the two actual programs.

**The headline, and it is the useful part of a negative result:** this is not a
failure of the reference semantics. It localises the gap to a **missing middle
layer** — between the strong lockstep relation the fundamental theorem needs and
the weak observational relation the algebraic laws are stated over, one more
layer is required to absorb administrative transitions.

*The interpreter restriction, generalised.* Restricting `papply` to
"apply the continuation once" would exclude ordinary multi-shot handlers and
result-dependent resumption — too blunt. Leaving it an arbitrary F\* function
leaves syntactic observation like reading a segment's length. The right
condition is that **`papply` preserves administrative equivalence**, added to
the boundary discipline beside the four it already carries.

*The store amendment is not the repair.* The nominal store relation already
ignores garbage outside the world; the residuals at issue here are **live** —
nameable from the returned handle — so their semantic difference cannot be
hidden as unreachable.

#### The gate before implementing it

| # | condition |
|---|---|
| 1 | a mode-indexed projection relation, with `MExtend` and `MResume` genuinely different, is statable as a type |
| 2 | it relates the four mismatches found here — protocol/enter and protocol/resume |
| 3 | consuming two related residuals **in the same mode** gives the same trace, related values and related stores |
| 4 | `xapply` preserves the relation, and `xapply2` — which observes frame length — is refused |
| 5 | a small positive instance of `pbind` associativity goes through |

**Condition 4 is the decision point.** If `xapply` is also refused, the erasure
is too fine and it is excluding general higher-order handlers for the laws'
convenience. If `xapply2` passes, the relation is too coarse.

#### B2b.3a, run: the relation discriminates on both sides

977 lines, **all appended**, with no existing line removed or changed, and
still with zero `z3rlimit`. No stop condition fired.

**Condition 4 came out in the intended direction, and neither half was
arranged.**

```fstar
guard_adm_condition_4 w c
  : Lemma (requires pwf_world w)
          (ensures papply_equivariant fcl_rel xapply  /\ padm_apply_pres fcl_rel xapply /\
                   papply_equivariant fcl_rel xapply2 /\ ~(padm_apply_pres fcl_rel xapply2))
```

Both interpreters satisfy `papply_equivariant`; only one satisfies the
administrative demand. **The line the relation draws is exactly the line between
*calling* a continuation and *inspecting* one** — `xapply`, which builds one
`PEnterCtx` and applies the continuation it was handed, survives; `xapply2`,
which reads the length of the segment, does not. Turning the refusal into a
positive claim fails, so it is a real refusal.

So the relation is discriminating on **both** sides — it accepts an ordinary
higher-order handler, refuses one that observes the internal representation,
judges marker/enter and marker/resume administrative, and refuses produce/enter
as a genuine difference in meaning. `guard_adm_strictly_coarser` proves both
halves of that on the *same* pair — related by `padm`, refused by `pkrel` —
so the middle layer is not a second name for the lockstep relation.

*The erasures are earned, not assumed.* A `PSiteF` is erased only under the side
condition `padm_marked m t1` — only where the machine's own value rule says it
is `PBindF`-or-nothing. A `PModeF` is deleted only in the `sh = false` regime,
where the relation has **structurally forbidden** the two frames that could
reach the responder.

#### The finding: produce/enter is not administrative

Two of the four mismatches are related at every plan, responder and ambient
stack. The other two are **refused**, at every mode, in both marker regimes, and
against *any* right-hand side. Stated at exactly the strength proved:

> Under the current production protocol and scope-floor semantics, the
> produce/enter pair is not an administrative discrepancy: the floor prevents the
> retained `PSiteF` from reaching a mode marker, so it can yield a context that
> direct entry does not. Therefore the current right-identity and transparency
> statements cannot be recovered merely by inserting a stack-level administrative
> relation.

This is **not** "right identity and transparency are impossible". It is that
they are unrecoverable while all three of these hold together: the current
production protocol, the rule that a search stops at a `PScopeF`, and the
current statement of the laws. The way forward is therefore not a stronger
middle relation but one of:

1. change the production protocol;
2. change the statements of right identity and transparency;
3. stop asking these two of a general context, and make them laws under a
   narrower condition.

What this gate has correctly removed is the option of pushing through with a
simple erasure.

#### `padm_apply_pres` is a candidate boundary condition, not an adopted one

What is proved is that the necessary discriminating power **exists**, is **not
vacuous**, and separates `xapply` from `xapply2` as intended. It can be taken
into the boundary record only once it is shown to be preserved by the stack
searches and updates and by the machine's transitions as a whole.

*The obstacle that will be met first*, and the port named it itself:
`PPerform` dispatches through `pfind_prompt`, which **captures the segment**
above the matching prompt — so two `padm`-related stacks hand the clause
**different** segments, administratively related but neither equal nor of equal
length. Whether `padm` survives a dispatch is what `padm_apply_pres` asks, and
condition 4 answers it only for this file's two interpreters. `pfind_prompt` is
not shown to respect the relation, and `pfind_param`, `pcut_scope` and
`pset_param` are untouched.

#### How the laws now divide, going into B2b.4

| law | prospect |
|---|---|
| left identity, resumption, anchored associativity | separated by a **marker** — candidates for recovery by the administrative relation |
| algebraic associativity | separated by a **re-bracketing of the responder** — needs a relation absorbing the monad laws of computations, which this gate did not build |
| right identity, transparency | compare **produce against enter** — not candidates under the current statements; back to a design decision |

**This is not stagnation.** The missing middle layer turned out to be real, and
the boundary between differences that may be hidden and differences that may not
is now drawn formally rather than by intuition. The open set is strictly smaller
than it was.

#### The design decision, taken before B2b.3b

The two laws that compare produce against enter need a decision, and it is taken
**before** the soundness work — because deciding to change the production
protocol would invalidate proofs about `pfind_prompt` and its neighbours that
B2b.3b would otherwise have already done.

**Keep the production protocol and the scope-floor rule. Restate the laws.**

The reason is what `o_enter_ctx` actually is. It is **not** a monadic `pure`:
it allocates a first-class handle, saves a residual, delimits the captured
region with a `PScopeF`, and yields a context that can be extended and resumed
later. It is a meaningful reification. The current right identity — "produce a
context, then extend it by `pure`" equated with "enter directly" — therefore
assumes silently that **context production is erasable**, and B2b.3a's
refutation is precisely the news that this assumption is false in this
semantics.

*Right identity, restated as a law about one produced context:*

```text
produce c >>= \cx -> extendContext cx pure >>= consume
```

against

```text
produce c >>= \cx -> consume cx
```

Production now happens **once on each side**, so what is asked is genuinely "is
extension by `pure` an identity?" — which is what a right identity should be
asking. A gate is running on whether this restatement is viable; if it is
refuted too, and especially if `xapply` refutes it, the difficulty is not
phrasing but the meaning of production and extension, and that goes back to
design.

*Transparency moves out of the algebraic laws entirely.* Its proper home is
B3's optimisation simulation:

> the general path at a `ContextTransparent` plan is observationally equal to
> the existing fast borrow.

That is not a retreat but a relocation to where the `ContextTransparent`
classification was always headed. The class was defined to name the prompts
the fast path may be used for, and "the fast path agrees with the general one
there" is a statement about an optimisation, not an algebraic identity.

The revised order is therefore: settle the restated right identity; move
transparency to B3; keep the protocol and the floor; then B2b.3b against that
fixed target; then B2b.4.

#### The restatement, gated: a strong candidate, on one non-trivial instance

522 lines appended, nothing existing changed, `z3rlimit` still zero. **The stop
condition did not fire** — the restated law is not refuted, and `xapply` does
not refute it.

Keep the two halves of the answer apart:

> **Q3** establishes that the reformulation removes the produce/enter
> obstruction in one non-trivial `xapply` instance.
>
> **Q4** shows that a general proof still requires a **computation-level**
> administrative relation: the stored `post`s differ by `POp c PVar` against
> `c`, which is the machine's representation of bind's right identity.

*What Q3 established.* At the same boundary, interpreter, plan, body and
extension that killed the old form: both sides now go through production, so the
produce/enter difference is gone; the old refutation's mechanism — residuals
of length 5 against 2 — becomes 4 against 4, on literally the same context;
and the differing handle names — `PCtxKey 2` against `PCtxKey 1` — are
absorbed by the nominal world exactly as they should be. The sharpest form of
it is one line: `guard_ri_ext_is_the_killers_fixture` proves the restated
law's **right-hand side is verbatim the left-hand side the old form loses
on**. The same
computation, refuted against a direct entry and not refuted against a
`pure`-extended production.

*What Q4 exposed.* Both sides produce, the residuals are frame-identical, and
what separates them is one administrative `POp _ PVar` inside a stored closure:
`extend_ctx_C` records the extension in `post`, so `post` goes from `PVar` to
`fun z -> POp (PVar z) PVar`, and `pctx_rel` compares `post`s by `pcomp_rel`
alone. The mid-point computations **are** related, at world `[(1,0)]`; the
**stores** are related at no world that relates them — proved for every
well-formed world.

So the reformulation did not hide the problem. It moved the comparison onto the
right object and exposed what is missing underneath.

#### Q4 is not a failure of B2b.3a — it is the same gap, one level in

The administrative relation was built on **stacks**. Identifying `post` with
`post >>= pure` needs it lifted along

```text
pcomp → post closure → pctx → store entry → store
```

This is the same relation the algebraic half of associativity was already known
to need — one that absorbs the monad laws of computations. It is not a second
hole; it is the same one, appearing inside a stored context.

#### Two things to settle before B2b.3b

**1. The `PScopeF` refutation candidate — adjudicate it first.** `pnobs_tr_le`
admits ambient stacks containing a `PScopeF`. If a drive's `PModeF MExtend`
marker gets beneath a floor and is caught by a yield, the responders' difference
becomes a difference between *stored contexts*, and Q4's negative turns into an
actual refutation. The port read that this cannot happen — a `PSiteF` or
`PBoundaryF` above the marker finds the marker before the floor — but **read
it only**: not proved, not even written down as a proposition.

Running the candidate is not enough. Adjudicate in this order:

| # | question |
|---|---|
| 1 | is it writable as a well-typed configuration? |
| 2 | does it satisfy `pstate_wb` / `pconf_ok`? |
| 3 | is it reachable from `pload` under a preserving interpreter? |
| 4 | do the two sides genuinely observe differently? |
| 5 | is the difference from the residual/responder, and not from raw handle names? |

**2 and 3 are the ones that matter.** `pnobs_tr_le` quantifies over every
equivariant ambient stack, which may well include floor arrangements the machine
never reaches. If the candidate is ill-formed or unreachable, the fault is not
in the law but in the **observation relation's domain being too strong** — and
then the standing stop condition applies: do not push the proof through, decide
whether the relation belongs over all equivariant configurations, over
well-formed ones, or over reachable ones. If the candidate is well formed *and*
reachable, it is a real refutation and the restatement goes back for review.

**2. Consumer equivariance.** The gate restricted the law's consumer to
`ops.o_extend pl _ g` rather than an arbitrary function, because an arbitrary
consumer branching on the handle number refutes immediately: a refutation about
*names*, not about extension. That restriction is sound for checking this
instance and is **not the final principle**. A consumer that branches on a raw
handle number is not a legitimate context a user can write; it is an observer
breaking the nominal abstraction. The semantic condition wanted is

```text
consumer is anchor-relative equivariant
```

with both directions required: the canonical `ops.o_extend pl _ g` satisfies it,
and a consumer that guesses or compares handle numbers does not. With that, the
syntactic restriction to `o_extend` can go. Note that the existing equivariance
hypothesis does **not** cover this: it constrains the *ambient stack*, while
this consumer sits inside the computation being observed.

#### The order from here

1. adjudicate the `PScopeF` candidate — well-formedness, reachability,
   observational difference;
2. formulate consumer anchor-relative equivariance;
3. decide whether to adopt the restated right identity;
4. design the computation-level administrative relation;
5. lift it to `pctx` and the store;
6. then B2b.3b — transitions, finite runs, observational soundness.

Transparency stays out of this. It shares no production with either side, so
nothing about the restatement's success carries to it.

#### The marker candidate, adjudicated: closed four times over

494 lines appended, `z3rlimit` still zero. **Not a refutation**, and the
adjudication did not stop at the first NO it could have:

| | result |
|---|---|
| writable as data | **yes** — and the hand-written responders are `assert_norm`-equal to the ones `ctx_drive` builds, not lookalikes |
| produced by a yield | **never** — at every configuration, reachable or not, well formed or not |
| `pconf_ok` | **fails**, and the failing conjunct is localised: `pstore_resid_wf`, via `presid_wf`'s `pno_mode` |
| reachable from `pload` | **no** — proved with *no hypothesis at all*: any fuel, key, lookup, interpreter, and also along the instrumented run `prun` uses |

The third row is the strong one, and it is stronger than unreachability because
it does not mention reachability:

> For the yield to fire, `pfind_mode rest == None` puts a floor **nearer than
> any marker**; `pcut_scope` cuts at **that same floor**; so the stored segment
> is exactly the part the mode search already walked without meeting a marker.
> "Beneath a floor" and "in the residual" are two sides of one floor.

**That is B2a-1's nearest-cut / nearest-search interlock, doing work months
after it was proved.** Proximity being a *semantic requirement* rather than a
normal form is exactly what forecloses a candidate nobody had thought of when it
was established. A good instance of an earlier proof functioning as a reusable
invariant rather than a one-off.

The limitation to keep, so the result is not read for more than it is:

> What is ruled out is the specific marker-bearing stored-context mechanism
> formalised by the candidate predicate. The broader claim that every route by
> which a responder might reach the store factors through such a marker remains
> a syntactic observation, not a theorem.

#### The observation relation's domain: well-formed equivariant

`guard_cand_domain_gap` shows the gap is **not empty**: `pnobs_tr_le` demands
equivariance and freshness of the initial store but **not** `pstore_resid_wf`,
so it quantifies over initial stores the machine could never have built. The
three candidates:

| domain | assessment |
|---|---|
| all equivariant configurations | includes broken stores the machine cannot build, so every future spurious candidate has to be excluded by hand, one at a time |
| reachable configurations only | most accurate, but reachability depends on the program, the interpreter and the execution history — poorly compositional, and too heavy as the domain of a law or a logical relation |
| **well-formed equivariant configurations** | contains the reachable ones, excludes junk that breaks a machine invariant, and is a *local* predicate, so it survives induction and composition |

**Well-formed is the right middle.** But do not rewrite `pnobs_tr_le` first —
gate it:

1. the target programs, from `pload`, are well formed;
2. the boundary interpreter preserves well-formedness;
3. both sides' machine transitions preserve it;
4. B2b.2's fundamental theorem and its observation corollary lift to the
   restricted domain;
5. the intended positives and negatives all survive.

This may require a `papply_wb`-equivalent field in `pboundary`. If so, **state
it as a new boundary condition** rather than letting it be derived implicitly
from equivariance — the same discipline `b_down` was given.

#### The `PBindF` candidate, and why it waits

The marker route is closed; the `PBindF` route is **named and not adjudicated**.
The left side runs `POp (POp (PVar z) PVar) xg` where the right runs
`POp (PVar z) xg`, so the left pushes one extra `PBindF PVar` frame — and
`pno_mode`, which closed the marker candidate, does not look at `PBindF` at all.
A different answer is possible.

It waits for the domain decision, because otherwise the same "real refutation or
junk configuration?" adjudication has to be redone from scratch. The order is
the one that worked here: writable as data → well formed → reachable →
producible by the machine → observationally different.

Its two possible outcomes are both informative:

- if the captured difference is only `c >>= pure` against `c`, it is **the**
  canonical example the computation-level administrative relation exists to
  absorb;
- if a legitimate consumer can tell the results apart, it is a genuine
  refutation of the restated right identity.

#### The domain restriction, gated and adopted

The restriction went through on all five checks, with no stop condition. What is
now fixed, in the module and here together:

- the domain of future law statements is **well-formed equivariant
  configurations**, not all equivariant ones;
- **reachability-only is not adopted**: more accurate, but it depends on the
  program, the interpreter and the execution history, so it is poorly
  compositional and too heavy as a law's domain. (That judgement is argued in
  the module, and marked there as stated rather than proved: reachability is not
  formalised in this file.)
- **`b_apply_wb` is a boundary condition independent of equivariance**, and now
  a field of `pboundary`;
- the `_wf` relations are placed **beside** the old ones; nothing was deleted;
- what is proved is the implication **from** the old relation **to** the `_wf`
  one, and that the two **domains differ** — nothing stronger;
- all six refutations still stand inside the restricted domain — none went
  vacuous;
- from here, a candidate positive or negative is asked **first** whether it
  satisfies `pnobs_dom`.

The adoption status, so that "added beside" is not misread as "undecided":

> `pnobs_tr_le_wf` / `pnobs_tr_eq_wf` are the intended domain for the next law
> statements. The unrestricted relations remain as an audit record and as
> stronger auxiliary notions; the existing laws have not yet been retargeted.

*Check 5 is the one that could have gone wrong silently*, since a narrower
domain makes universally quantified statements easier and a refutation could
become vacuous unnoticed. All six were **re-derived** in the restricted relation
rather than inherited, each preceded by a proof that its configuration is inside
the domain. Five stand at `pload`'s own empty stack and store; the sixth — the
algebraic half — stands at a **non-empty** store, and had that store failed
`pstore_resid_wf` the refutation would have evaporated and the stop condition
fired. It holds: the residual `[PBoundaryF]` carries neither floor nor marker
above it, which is `presid_wf` exactly.

*The new field, and its independence proved rather than asserted.* All three
boundary constructions supply `b_apply_wb`, including `x2boundary`, whose
interpreter measures the length of the continuation it is handed — so the
condition is orthogonal rather than a way of quietly excluding it. And the doc
comment's claim that it does not follow from `b_apply_eq` was **checked**:
`xapply_bad` satisfies `papply_equivariant` and fails `papply_wb`, the hinge
being that `PBoundaryF` carries no data and so is invisible to `pkrel`.

*The restriction pays for itself immediately.*
`guard_nobs_dom_kills_the_candidate` excludes the marker candidate **from the
domain, in one line**, where the gate before it needed four separate
arguments. Keeping the relations side by side is what makes both halves of the
trade provable rather than asserted: what it buys
is that exclusion, at any boundary, control computation, ambient stack and
counter; what it costs is re-running the six refutations, and the actual price
is exactly two `pterm_wb`s.

Two of seven mutations did not isolate, and are recorded as not counting, with
substitutes named for each.

#### The `PBindF` candidate: inside the domain, and harmless anyway

The verdict, at exactly the strength proved:

> The `PBindF` candidate is **not** excluded by the well-formed domain. It is
> harmless for a different reason: the extra `PBindF PVar` is consumed before
> either yield rule can observe or capture it, and both sides reconverge to the
> same configuration with unchanged store, counter and trace.

**The domain gate is silent here, and that is worth knowing about the tool.**
`pno_floor` looks only at `PScopeF` and `pno_mode` only at `PModeF`, so a
`PBindF` trips neither; `pstore_resid_wf` of this candidate's store is `true`.
The one-line disposal that settled the marker candidate does not apply. So
well-formedness is **not** a filter that removes every inconvenient
candidate. It removes exactly the configurations that break a machine
invariant, and this
one does not break any.

What closes it is frame lifetime, and the lemma is **unconditional** — any
lookup, interpreter, value, extension, ambient stack, store and counter:

```text
PStep (POp (POp (PVar z) PVar) g)  k
PStep (POp (PVar z) PVar)          (PBindF g :: k)
PStep (PVar z)                     (PBindF PVar :: PBindF g :: k)   ← the frame
PStep (PVar z)                     (PBindF g :: k)
PStep (g z)                        k
```

with the right side reaching the last line in two steps. The supporting facts
are as sharp: in the one configuration where the frame exists the stack head is
a `PBindF`, so neither caller of `pyield` fires; and production always stores
`PVar` for `post`, so `post z` is a *value* and the frame cannot outlive one
transition.

**This is a different mechanism from the one that closed the marker candidate**
— no `pfind_mode`, no nearest cut. The domain and the operational semantics
are each doing their own job.

*Reachability stays undecided, and the adjudication did not need it.*

> Reachability is undecided, but it is not needed for this adjudication:
> `lemma_qb_reconverges` is unconditional. Even if the candidate configuration
> arose, the extra frame would disappear before it could affect the residual
> protocol.

Not "harmless because unreachable" but "harmless because it reconverges".

#### The canonical specimen is elsewhere, and now identified

The most useful thing this gate produced is a correction of where to look:

- `guard_ri_ext_midpoint_no_world`'s negative is **untouched**. The
  administrative `POp _ PVar` inside `qext`'s `post` is still a real difference
  between two stored contexts; what was closed is only the route by which the
  corresponding *stack frame* could reach a residual;
- so the specimen the computation-level administrative relation must be built
  against is the mid-point store pair **`(qmid_sl, qmid_sr)`**, not this
  candidate's frame;
- the difference there is bind's right unit inside a stored `post`;
- and **nothing yet shows such a relation would be observationally sound** —
  that is the whole of what remains to be earned.

#### Two conditions not to be mixed

The next gate is consumer equivariance, and only the first of these:

1. **Nominal consumer equivariance** — the consumer does not observe a
   renaming of handles. The canonical `ops.o_extend pl _ g` passes; a consumer
   branching on a raw id fails.
2. **Administrative congruence** — `c >>= pure` and `c`, or `post`s differing
   by one, are treated alike. This can only be stated *after* the
   computation-level relation exists.

Requiring both at once would silently presuppose a relation not yet defined.

When that relation is designed, its first acceptance conditions are concrete:

| # | condition |
|---|---|
| 1 | it relates `qmid_sl` and `qmid_sr` |
| 2 | it does **not** relate `post`s that genuinely return different results |
| 3 | it preserves the anchor and world extension |
| 4 | it lifts from `pctx` to the store |
| 5 | soundness for `pnobs_tr_eq_wf` is shown at the `qext` instance |

#### The consumer gate: a real discriminator, and a quantifier-order defect

All four conditions proved, and the syntactic `o_extend` restriction can go —
the previous gate's *disclosure* is now a **theorem**:
`guard_open_form_refuted_by_branching` refutes the unconditional form for a
branching consumer by running the machine, traces `["one"]` against `["two"]`.
The conditional form holds of the same consumer, vacuously, which is what shows
the exclusion is done by the nominal condition and not by syntax. No
administrative congruence appears anywhere in the section.

**Condition 3 came out more precise than it was posed**, and along the line
already recorded for `Eq` and `Ord`:

| consumer | verdict |
|---|---|
| branches on a raw handle number | **refused** |
| orders raw handle numbers | **refused** — and at an anchor that *pins* the handle it holds, so this is not the guessed-name refutation again |
| compares handle **identity** | **admitted** |

So "compares" does not fail uniformly: reading the number fails, comparing
identity passes. The same asymmetry, reached independently.

**But the law's quantifier order collapses the condition.**
`lemma_pconsumer_nom_is_empty_anchor` proves `pconsumer_nom r f` is equivalent
to `pequivariant_fn_at r [] f`. The order today is

```text
fix the consumer f
forall initialStore. f is equivariant at anchor(initialStore)
```

and the empty store is among them, so the whole condition is exactly
equivariance at the empty anchor — **"behave as a closure that owns no handle
at all"**. A consumer that legitimately captured a handle *from the initial
store* is excluded.

This is the same defect anchor-relativisation removed once already, walking back
in through the law's own quantifier. The wanted order is the other way round:

```text
EquivariantAt w0 f  ==>  forall sto. anchor(sto) extends w0  ==>  law holds
```

which admits handles legitimately captured within `w0`, refuses numbers not in
`w0`, survives world extension by allocation without re-proof, and degenerates
to today's global condition at `w0 = []`.

**Not adopted as the final domain.** The repair is not to drop the store
quantification but to **index the observation and the law by a provenance
anchor** — `pnobs_tr_le_wf_at b w0 …`, quantifying only over initial stores
whose anchor extends `w0`. And since the computations and closures inside a law
can capture handles too, the law should eventually be stated *whole* under one
`w0`; the computation-level relation will need the same. The current `_wf`
relations remain as the `w0 = []` special case and as the stronger audit form.

Recorded at the strength proved:

> The consumer gate succeeds as a discriminator: raw-name branching and ordering
> are rejected, while identity comparison is admitted. But the law's current
> quantifier order collapses the condition to the empty-anchor instance,
> excluding consumers that legitimately capture a handle from the initial store.
> This is not adopted as the final law domain; the next gate must index the
> observation and the law by a provenance anchor.

Still open from this gate: the law itself is unproved in general. The
surviving instance is again a body at one configuration; condition 2 covers
only algebras whose `o_extend` is the reference node; and "every consumer
that reads only identity conforms" is **not** proved as a characterisation —
only the specific form admitted, and the two number-reading forms refused.

#### Two proof-engineering notes, not semantic results

Kept apart from the findings above deliberately: these are about
reproducibility and stability, not about the machine.

- **The same file changed verdict under different include paths.** A proof
  depending on quantifier-pattern firing passed with one `--include`
  configuration and failed with another. Fixed by passing the side condition as
  a proof-function argument so no pattern matching is involved; the result is
  now confirmed under both configurations. Worth remembering because it is the
  shape of a defect that makes CI and a local run disagree.
- **A Z3 interaction failure**, `Parse error: </labels> not found`, on a query
  instantiating a general lemma at a large plan. Worked around by instantiating
  at a small plan instead.

#### The order, revised again

1. record this result;
2. ~~establish that restricting the observation relation to well-formed
   configurations goes through~~ — **done**;
3. ~~adjudicate the `PBindF` candidate~~ — **done**: in the domain, harmless
   by reconvergence;
4. ~~nominal consumer equivariance~~ — **done as a discriminator**, but its
   quantifier order is wrong;
5. ~~provenance-anchor-indexed observation~~ — **done**: the order is repaired,
   with the empty-anchor case proved to be the existing relation;
6. ~~fix the consumer-carrying law's signature~~ — **done**: statement fixed,
   premise proved necessary, law still unproved;
7. the computation-level administrative relation, built against
   `(qmid_sl, qmid_sr)`;
8. lift it to `pctx` and the store;
9. B2b.3b.

Fixing the order now rather than later is the point: accepting the empty-anchor
restriction and moving on would very likely reproduce the same quantifier
mistake in the next relation.

#### The provenance-indexed observation: the order repaired

Seven checks, all proved, no stop condition. The reach, stated precisely:

> The provenance-indexed form repairs the quantifier order: a consumer is
> checked at the anchor recording what it legitimately owns, and the law ranges
> only over initial stores extending that anchor. The empty-anchor form is
> exactly the previously adopted `_wf` relation, not a competing definition.

That last clause is proved, not asserted — `lemma_pnobs_tr_le_wf_at_empty` and
its companion are **biconditionals**, and the law's degeneration at `w0 = []` is
written in existing symbols only.

**The same consumer, opposite verdicts.** `guard_check2_capture_conforms_at_pin`
proves `pequivariant_fn_at fcl_rel qw_pin3 qcons_cap` together with
`~(pconsumer_nom fcl_rel qcons_cap)`: a consumer that captures a handle passes
under the indexed condition and fails under the collapsed one. And "captures"
is machine-checked rather than argued — the captured key stands in operator
position, and the run reaches `PDone` from a store that owns it and `PStuck`
from the empty store, so the outcome depends on the store entry the handle
names.

Check 7 is what makes indexing practical, and its content is worth stating:

> Allocation extends the world but does not create a new proof obligation for an
> existing consumer: consumer equivariance is monotone in the world, while the
> indexed observation law is contravariant in its required initial anchor.

The `requires` of `lemma_law_ri_ext_cons_at_reused_after_alloc` mentions no
obligation about the consumer at the extended world at all.

**Non-vacuity is four discharged facts, not an argument.** The restriction is
inhabited, *and* the empty store — which every earlier instance in this file
starts from — is proved excluded, so the quantifier really narrowed. The
admitted store is **machine-built**: `pterm_wb` of a seed program, then `pload`
run and the store and counter read off the result. It is not excluded by B2b.7's
domain, so the two restrictions do not cancel. And both sides really run on it,
to `PDone`, on the same empty trace. The exhibited world contains all four
anchor pairs beside the answer pair, so `psrel` is checked at every pre-existing
handle.

Worth recording: **the first attempt was discarded for exactly the reason the
stop condition named.** A hand-written `[(3, _)]` at counter 4 was used at
first; since `palloc` only conses, that is not a state the machine can reach,
and the instance was rebuilt on a store the machine produces. The stop condition
worked as a self-check rather than as something a reviewer had to catch.

Two things stated and not proved, both fine as they stand: the *negative* half
of that reachability observation, that `[(3, _)]` at counter 4 is unreachable,
is inspection of `palloc`, while the positive half is proved by running the
machine, and only the positive half is needed; and the indexed form is **not**
compared with the previous one at a non-empty `w0`, only the `w0 = []`
biconditional is established, which is the right restraint rather than an
unearned strength claim.

#### Next: fix the consumer-carrying law's signature

This is not a large new proof so much as fixing what the last two gates
established into the law's signature:

```text
law_right_identity_ext_at
  w0
  consumer
  requires  consumer equivariant at w0
  observes  only stores whose anchor extends w0
```

What that settles:

- the syntactic restriction to `o_extend` is **withdrawn**;
- the consumer is required to satisfy `pequivariant_fn_at … w0`;
- raw-number branching and ordering are refused;
- handle identity comparison is admitted;
- a captured handle is admitted when `w0` records ownership of it;
- `pconsumer_nom` remains as the empty-anchor special case and as an audit
  definition;
- **the law itself stays unproved** — what is being fixed is the statement and
  its domain of quantification, nothing more.

And the boundary holds: **no administrative congruence yet.** That waits for the
computation-level relation, which is the gate after.

#### The signature, fixed

```fstar
let law_right_identity_ext_at (b) (w0) (ops) (pl) (c) (f) : GTot prop
  = pequivariant_fn_at b.b_rel w0 f ==>
    pnobs_tr_eq_wf_at b w0
      (pbind (ops.o_enter_ctx pl c)
             (fun cx -> pbind (ops.o_extend_ctx pl cx (PVar #v #cl)) f))
      (pbind (ops.o_enter_ctx pl c) f)
```

proved equal to the development form in both directions, so this is a naming and
the earlier degeneration, antitonicity and reuse facts transport along it.

Three things, kept apart:

1. **The statement's computational shape and quantification domain are fixed** —
   the provenance quantification, the consumer premise, the well-formed starting
   domain, and the shape of the two computations compared. **Which observation
   relation it finally uses — the existing nominal one, or an administrative one
   — is not yet settled**; the gate below is why.
2. **The premise is substantive** — dropping it makes the conclusion *false*,
   under the very same `pnobs_tr_eq_wf_at`.
3. **The law itself is still unproved** — that every conforming consumer gets
   the consequent is what the computation-level relation is for.

> The gate fixes the law's **statement**, not its truth. It proves that the
> provenance-indexed formulation is the intended one, that its consumer premise
> is necessary, and that the premise admits strictly more than the former
> syntactic `o_extend` restriction. Proving the consequent for every conforming
> consumer remains the next semantic obligation.

*The refutation guard's job, precisely.*
`guard_final_conclusion_refuted_by_branching` shows the premise is
**needed**: it proves `~(pnobs_tr_eq_wf_at xboundary [] rlhs_b rrhs_b)`, so
the conclusion the hypothesis-free form would have claimed is false at the
signature's *own* observation, not merely at the older unrestricted one. It
does **not** show that the conditional law holds. Those are different
statements, and only the first is proved.

*Withdrawal of the syntactic restriction is not formal.*
`guard_final_admits_a_non_extend_consumer` exhibits an admitted consumer that
differs from **every** `o_extend` term already at a point, so the range really
grew.

*`pconsumer_nom`'s standing*, which the ledger now records per form:

- a **sufficient** condition, usable at every provenance, the empty one
  included;
- **not necessary**: it refuses capturing consumers, and `qcons_cap` is the
  witness;
- useful for backward compatibility and as an audit definition;
- the final law's premise is `pequivariant_fn_at … w0`, not this.

*No refutation is claimed at a non-empty provenance*, and that is the right
restraint: the counterexample runs at the empty store, which an owning anchor
excludes, and transplanting it would have meant manufacturing a refutation
rather than finding one.

*A reproducibility note, not a result.* A full re-check of the module now takes
about 90–100 s on this machine, not the ~50 s a brief estimated. Worth
recording for future gate estimates.

#### What the computation-level relation should aim at first

Without changing the signature just fixed:

| # | target |
|---|---|
| 1 | relate `(qmid_sl, qmid_sr)` |
| 2 | absorb `post >>= pure` against `post` |
| 3 | refuse `post`s that genuinely return different results |
| 4 | preserve the provenance anchor and world extension |
| 5 | be defined **independently of** the consumer condition |
| 6 | then derive the consequent at an instance of the fixed signature |

Item 5 keeps the policy that has been worth keeping throughout: **consumer
equivariance and administrative congruence stay apart.** One is about names, the
other about computations, and mixing them has each time hidden which was doing
the work.

#### The relation exists; the bridge to the law does not

Targets 1–5 met, target 6 split. 958 lines appended, `z3rlimit` still zero. A
full re-check now takes **2–4 minutes**, which future estimates should assume.

*The specimen is related, and the relation is not loose.* `padm_srel` relates
`(qmid_sl, qmid_sr)` at the world relating the two mid-point computations, and
`psrel` relates them at none. At the fixture, three contexts agree on payload
and on all four residual frames and differ **only** in the stored closure:
`post >>= pure` is related, while `post >>= xg` (which performs) and a closure
that discards its argument are refused.

*Target 3 is a theorem, not a fixture reading:*

```fstar
lemma_padm_pcrel_unit_var_inv r w y1 y2 f
  : Lemma (requires padm_pcrel r w (pbind (PVar y1) f) (PVar y2))
          (ensures pval_rel w y1 y2)
```

for **every** `f` — absorbing administrative units cannot lose the result.

*And the balance is not where it looks.* What refuses a changed result is
**not** the strip clause's side condition: the lemma above holds for arbitrary
`f`. It is that the strip reaches only the head, and the recursion bottoms out
in `pcomp_rel`, which joins two different constructors nowhere. The side
condition buys something else and is separately load-bearing — a `POp` whose
continuation is not `PVar` is not absorbed. **Two knobs, two jobs**, worth
knowing before either is touched.

*Position relative to `padm_stack`:* parallel, not reused, and neither calls the
other. `padm_stack` is mode-indexed because a stack is driven by a consumer; a
stored `post` is driven by nothing, so there is no mode and no regime here. Both
are deliberately directional. The step index drops on each strip, which is what
stops "strip forever".

#### Target 6 split, and the split is the finding

Under the configuration-level reading it goes through: the correspondence the
negative blocked now holds, and `pconf_rel` holds at no world.

Under **the observation's own consequent it does not**, and it was not
engineered around. `pnobs_tr_le_wf_at` demands `psrel` at the final stores, and

```fstar
guard_padm_srel_strictly_weaker ()
  : Lemma ((forall w s1 s2. psrel fcl_rel w s1 s2 ==> padm_srel fcl_rel w s1 s2) /\
           padm_srel fcl_rel qmid_w qmid_sl qmid_sr /\
           ~(psrel fcl_rel qmid_w qmid_sl qmid_sr))
```

so relating the mid-point administratively does not produce the witness the
observation asks for. At this instance the witness is still the `psrel` obtained
without the new relation.

> **The relation is built; the bridge to the law is not.** What remains is not
> the relation's definition but a soundness theorem connecting it to an
> observation.

**`padm_srel ⟹ psrel` is not the goal** — the specimen is itself a
counterexample to that implication, so that direction is already closed. Nor is
replacing the existing observation by `padm_srel` the immediate move. The layers
should be:

```text
pcrel / psrel            the strong lockstep relation, for the fundamental theorem
        ↓
padm_pcrel / padm_srel   administrative simulation
        ↓
                         the observational equivalence the laws are stated over
```

— existing observations **kept**, an administrative observation
(`pnobs_tr_le_adm_at` and its symmetric form, comparing final stores by
`padm_srel`) placed **beside** them, with its soundness proved in B2b.3b. Not a
weakening replacement; a division of labour.

*One guard was accepted, and it is carried forward as a debt.* Setting
`padm_pctx`'s residual clause to `True` still verifies, because every fixture
has the same residual on both sides. The clause is `pctx_rel`'s verbatim, so its
tightness is **inherited, not demonstrated**. Before any simulation work, one
negative specimen is needed: same `post` with corresponding residuals, against
same `post` with residuals that mean something different.

*Also unfinished:* no simulation — the two configurations are shown to
correspond, not to *stay* corresponding, and `padm_srel` is not shown preserved
by `pstep`; `padm_pcomp` absorbs at the head only, which is all `extend_ctx_C`
needs today; and the law remains unproved.

#### The order after the bridge finding

1. instantiate the fixed signature at the **simplest conforming consumer**, one
   that returns the handle unchanged, and decide, under the *current*
   observation, whether it holds or is refuted;
2. make `padm_pctx`'s residual clause non-vacuous;
3. if step 1 refutes, place an administrative observation beside the existing
   one;
4. one-step and finite-run simulation for `padm`;
5. connect the law to the administrative observation.

This is not a step backwards. The computation-level relation's granularity
holds, and the remaining hole has narrowed from "what should the relation be"
to "which soundness theorem connects it to an observation".

#### The identity consumer: refuted, by the specimen itself

The premise is discharged **at every provenance in one proof** —
`guard_ri_id_consumer_equivariant` takes `w0` as a parameter. So the verdict is
about the consequent and nothing weaker. Then:

```fstar
guard_ri_id_law_refuted_at_pin ()
  : Lemma (pequivariant_fn_at fcl_rel qw_pin3 ricons /\
           ~(law_right_identity_ext_at xboundary qw_pin3 ref_ops xpl qc ricons))
```

The `qw_pin3` form is the stronger one: the observation is **antitone** in `w0`,
so refuting at a larger provenance implies refuting at `[]` and not the reverse.
It runs from `gsto`, whose anchor is proved to extend `qw_pin3`, so the empty
store the weaker refutation uses is excluded there.

Scoped exactly:

- of **`ref_ops`**;
- at an **identity consumer** that satisfies the provenance-indexed premise;
- under the **well-formed nominal observation** `pnobs_tr_eq_wf_at`;
- at a **pinned** provenance as well as the empty one;
- the fixed computational form of right identity is **false**.

This is neither "right identity is impossible in general" nor "the reference
semantics is broken". It is that the current observation **counts an
administrative difference as a difference in meaning**, and under that
observation the law is false.

*And the refutation is the specimen, literally.* The two final stores are
`qmid_sl` and `qmid_sr`: **at the identity consumer the mid-point is the
end-point.**

#### Two bridges, and only one of them was ever the missing piece

> The missing bridge to `psrel` was not the missing component: the finalized
> right-identity law is **false** under the current nominal observation.
> Retargeting the law to an administrative observation is therefore necessary if
> this law is to be retained. A different bridge — proving that administrative
> relatedness is **sound for public observations** — remains to be established.

- `padm_srel ⟹ psrel`: **not a repair**, closed twice over. The specimen is
  a counterexample to the implication, and the law is genuinely false as stated.
- `padm_srel` safe as a public observation: **still required**, and it is what
  B2b.3b is for. Adopting an administrative observation as *the* semantics needs
  exactly that.

The refutation used no administrative congruence, no simulation and no
preservation lemma — four machine runs, one uniqueness argument, and the
mid-point negative. So the ordering judgement was right: this gate was prior to
the bridge, and its answer is that the bridge is not the missing piece.

#### The earlier positive instance, demoted

> The earlier positive instance did not relate `qext` and `qprod`; a later
> allocation made them garbage outside the witness world. It remains a valid
> instance, but it is **not** evidence that the law survives when the
> administratively different context remains live.

The mechanism, since it is the useful part: `qcons` *performs*, so `xapply`
fires and allocates one further context on each side, and each run answers with
**that** later context, leaving `qprod`/`qext` named by no handle, hence
garbage that `psrel` skips (`guard_qce_world`'s domain is `{2 ↦ 1}`). At
`ricons` nothing further is allocated, the answers name the specimen itself,
`pval_rel` forces the world onto `(1, 0)`, and `psrel` must then compare `qext`
against `qprod` — refused at every well-formed world.

#### What this settles

The question that has been open since the mid-point negative was found —

```text
is the relation insufficient   or   is the observation too demanding?
```

— is settled: **the observation is too demanding.** And the way it was settled
is worth keeping: the difference was invisible while a later allocation left the
administratively different context as garbage, and became visible by choosing a
consumer that allocates nothing, so the live handle names the specimen. The hole
has narrowed again — from "where to build a bridge" to "which observation to
adopt as the semantics, and how to prove it sound".

One guard was **accepted** and is recorded as weak: deleting the premise-lemma
call from the refutation still verifies, because `pequivariant_fn_at` unfolds in
goal position and Z3 re-proves it. What stands in its place is the premise
proved standalone, plus a mutation showing its negation is not provable.

#### The order, settled by the verdict

1. ~~make `padm_pctx`'s residual clause non-vacuous~~ — **done**: the
   previously accepted mutation now lands, on a specimen that differs
   observably;
2. place an administrative observation **beside** the nominal one, the latter
   kept;
3. check that this gate's identity-consumer counterexample becomes a
   **positive** instance under the new observation;
4. check that a performing `post`, an argument-discarding `post`, and differing
   residuals are still **refused**;
5. one-step and finite-run preservation for the administrative relation;
6. soundness against public observation;
7. only then, prove right identity again.

#### The residual clause: debt paid

The mutation B2b.12 recorded as **accepted** — `padm_pctx`'s residual clause
set to `True` — now **lands inside the new refusal guard**. That is the whole
of the debt, and it is paid rather than re-documented: the read of the residual
clause was deliberately inlined into the guard so the rejection lands there
rather than in a factored lemma.

*The specimen is well made.* Three contexts share payload **and** `post` — the
same term `PVar` that `qprod` carries — and their residuals differ only in the
body of the `PSiteF`. Shape (length, the four constructors, both tables,
provenance) agrees as terms. The observable difference is established by
**running the machine**:

| context | value | trace |
|---|---|---|
| `qctxL` | `FI 7` | `["left"]` |
| `qctxR` | `FI 8` | `["right"]` |
| `qctxV` | `FI 8` | **`["left"]`** |

**`L` against `V` have identical traces and differ only in the answer**, which
is what shows the clause is not merely catching trace differences. All three
take the same number of transitions and end with the same counter, so neither
fuel nor a side allocation is doing the work. The refusals divide by depth too:
`L`/`R` contradicts at index 1 on the event, `L`/`V` passes index 1 and
contradicts at index 2 on the value. And `padm_xrel w qctxL qctxL` holds, so
the shape is not refused wholesale.

*What `presid_wf` licenses, stated precisely:*

> All three residuals satisfy `presid_wf`, so they lie inside the well-formed
> observation domain and cannot be dismissed by the store invariant. A closed
> machine execution that actually stores them is **not** established.

That is enough here. Having decided the laws are stated over well-formed
configurations, a specimen inside the domain tests the relation's discriminating
power whether or not it is reachable.

*Honest about the guards.* One mutation was accepted and is recorded as weak
(`pfrel` unfolds in goal position, so Z3 re-derives the inversion without the
lemma; M1 stands in its place). Two mutations landed on the **observation**
guard rather than the refusal guard, so "removing the specimen removes the
refusal" is **inferred, not observed** — F\* halts at the first failure.
Whether the second refusal guard also fails under M1 is likewise unobserved.

*A toolchain note, not a result.* A `Error 276` Z3 response-parsing failure was
worked around with `--split_queries always` during development; the final
inlined version needs no such flag and lands on `Error 19` under the plain
command. Note that F\* v2026.08.16 has **removed** that option, so the
workaround is specific to the toolchain in use at the time and does not affect
the deliverable.

#### What the administrative-observation gate must fix

| # | requirement |
|---|---|
| 1 | the nominal observation is **unchanged**; the administrative one is added beside it |
| 2 | the only thing that changes is the final-store clause: `psrel` becomes `padm_srel` |
| 3 | the value relation, the trace's order and multiplicity, world extension, provenance and the well-formed starting domain are all **retained** |
| 4 | the identity-consumer counterexample becomes a **positive** instance at the very same configuration |
| 5 | a performing `post`, an argument-discarding `post`, and the `L`/`R` and `L`/`V` residual pairs are **still refused** under the new observation |
| 6 | containment from the nominal observation into the administrative one is **proved** |
| 7 | the new observation is **not** the universal relation, fixed by an independent negative |

What this stage establishes is only that **a candidate observation has the
expected discriminating power**. Soundness against public observation comes
after one-step and finite-run preservation, as planned.

#### The administrative observation: oriented, naive symmetrisation fails

All seven requirements met. 1,321 lines appended, `z3rlimit` still zero, and no
weak guard this gate — every mutation isolated.

*The payoff, at the very configuration that killed the nominal law.* The
antecedent is met in all four conjuncts with nothing assumed; the **nominal**
consequent is false; the **administrative** consequent is true, with the
witnesses uniqueness of convergence forces. Both consequents are proved to *be*
the respective observations' bodies there, so they are not lookalikes.

*Requirement 2 is proved elegantly.* The two observations are **biconditional
under the single hypothesis that the two store relations agree** — so no
clause other than the store clause can carry any difference. The hypothesis is
false, so this is a statement about the two *definitions*, which is exactly what
was wanted.

*Requirement 7's negative is genuinely independent.* It reuses the left-identity
counterexample and turns on residual **length**, 4 against 2 — it mentions no
stored `post` and would stand however the strip disjunct were written.

**But the symmetrised form is refuted**, at `ricons`, premise discharged.
`padm_pcomp` is directional by construction — only the left may carry the
administrative unit — and `~(padm_xrel w qprod qext)` holds at **every**
well-formed world, the exact mirror of the pair it relates the other way. The
nominal law is proved to imply both analogues, so this is not an artefact of
comparing different statements.

#### Oriented reduction is not the same as one-directional equivalence

My first reading of that — "right identity is essentially an ordered law" —
was wrong, and the correction is worth keeping: it is a standard confusion.

`qext` is `post >>= pure` and `qprod` is `post`, so **`qext →adm qprod` and
not the reverse** is exactly right as a *reduction*. But the absence of a
reverse reduction does not make the two unequal. β-reduction is
one-directional; β-equivalence is symmetric, and proving two terms β-equal
never requires the right-hand side to re-insert a redex.

What was refuted is the **naive** symmetrisation — `adm_le x y /\ adm_le y x`
— which demands administrative *expansion* right-to-left. Symmetric relations
can be built otherwise: joinability by a common reduct, the equivalence closure
of the oriented relation, or agreement of administrative normal forms. At the
specimen, joinability is immediate: `qext →adm qprod` and `qprod = qprod`, so
`qprod` is the common reduct and nothing has to be expanded.

So the claim is recorded at this strength:

> `padm_srel` is suitable as an **oriented administrative reduction**. The naive
> observation obtained by requiring this oriented relation in both directions is
> too strong. Whether its equivalence closure, joinability relation, or
> common-normal-form relation yields a sound symmetric observation **remains
> open**.

The intended division of labour, then, is to keep the oriented relation with a
narrowed role and build the laws' equivalence on top of it:

```text
padm_srel   administrative reduction / simulation preorder
    ↓
padm_eq     common administrative reduct, or equal normal form
```

Right identity then has `lhs ⊑adm rhs` immediately as an oriented lemma, with
`lhs ≈adm rhs` as the monad-law goal. This also looks better for
associativity, whose two sides need not reduce to each other but may well reduce
to a common normal form.

#### The feasibility gate before B2b.3b

| # | question |
|---|---|
| 1 | can `padm_join` be defined at the context and store levels? |
| 2 | are `qext` and `qprod` joined, by the common reduct `qprod`? |
| 3 | do `qwork` and `qbad` have **no** common reduct? |
| 4 | do `qctxL`/`qctxR` and `qctxL`/`qctxV` have none? |
| 5 | do differing residuals have none? |
| 6 | are reflexivity and symmetry provable? |
| 7 | does transitivity need confluence, or a canonical normal form? |

**7 may stop it**, and only then is there a real choice to make between defining
an administrative normaliser, using the equivalence closure, or restricting the
law to a refinement preorder.

One debt to clear before final adoption: **the `qw_pin3` positive is not
delivered** — only the empty-store half of requirement 4. Whether a relation
that works at the empty provenance also works at a configuration owning handles
is a separate obligation, and B2b.13 refutes the nominal law there too.

Requirement 5's four refusals are at the clause the observation reads, not at
whole runs; no closed program is exhibited whose run stores those contexts. Same
division of labour as before.

#### Joinability: definable, discriminating, and stopped at transitivity

The specimen is joined, with `qprod` as the common reduct on **both** readings
and nothing expanded; `~(padm_xrel w qprod qext)` is carried in the same guard
so the symmetry cannot be misread as a weakening of the oriented relation. The
performing `post`, the argument-discarding `post`, and both residual pairs are
**not** joined, each with its diagonal positive beside it so the refusal is not
"neither reduces to anything", and all quantified over every well-formed world.

*The store level forced a correction, proved rather than argued.* The naive
existential `∃ sz. padm_srel s1 sz /\ padm_srel s2 sz` is **false** at the
specimen: `psrel` and `padm_srel` are world-**directed** — an index is read in
the left store and its partner in the right — so reading `qmid_sr` as a left
argument demands a key the right run never allocated. The store-level join must
therefore be the **pointwise lift**, and the naive form is kept so the
correction stays checkable.

Symmetry holds unconditionally. **Reflexivity is refuted**: at the empty world a
handle no world speaks for relates to nothing. That is inherited from `pxrel`
and `padm_xrel`, not introduced here.

#### What Q7 actually refuted — a type error, not a defect

Transitivity needs confluence (unproved) **and** transitivity of the oriented
relation, and the second is refuted. But the refutation is narrower than it
first looks, and the correction matters:

> The gate refutes **fiberwise** transitivity at a fixed world. It does **not**
> refute compositional transitivity of the nominal relation, whose conclusion
> must be indexed by the **composite** world.

A world is a partial bijection from left names to right names — a *morphism*,
not an index. From `R w12 x1 x2` and `R w23 x2 x3` the conclusion to expect is
`R (w23 ∘ w12) x1 x3`, not `R w12 x1 x3`. The counterexample uses one `w`
sending `0 ↦ 1` and `1 ↦ 2`; `A R[w] B` and `B R[w] C` hold while `A R[w] C`
would need `0 ↦ 2` — which is exactly what `w ∘ w` supplies. So requiring
the ordinary shape of transitivity of a world-indexed relation was a **type
error on our side**, not a defect in the relation.

The same reading fixes the other two laws. The natural shape is

```text
identity     R (identity_on (support x)) x x
symmetry     R w x y            ==>  R (inverse w) y x
composition  R w12 x y /\ R w23 y z  ==>  R (w23 ∘ w12) x z
```

so reflexivity should never have been asked at the **empty** world: a public
handle is unrelated to itself there because the world does not own its identity.
Stated at an identity world over the handle's support — or over the existing
provenance anchor — it is the right law. This is better described as a
**groupoid-indexed** (world-indexed heterogeneous) relation than as a PER.

#### Joinability needs the same correction

`∃ z. padm x z /\ padm y z` demands a **syntactically identical** reduct,
name-spaces included. The nominal shape is two-layered:

```text
∃ nx ny w.  x →*adm nx  /\  y →*adm ny  /\  nominal_rel w nx ny
```

— reduce on each side, then compare the reducts **through a world** rather
than requiring the same raw keys. That is the same diagnosis as the store-level
naive join's failure: a store holds *named* resources, so "nominally related
reducts" is the right notion and syntactic join is not.

Confluence remains a separate problem: introducing world composition does not
give it for free.

#### The order this settles

1. build the world algebra as a category/groupoid — identity, inverse,
   composition;
2. recover the fixed-world counterexample at the composed world;
3. separate administrative *reduction* from nominal *comparison*;
4. decide administrative normal form or confluence;
5. only then construct the symmetric administrative observation.

**So Q7's stop was productive.** Before the three-way choice — normaliser,
equivalence closure, or refinement preorder — there was a missing layer, and
it is the world algebra.

#### Verification hygiene: `Verified module:` means nothing

F\* prints `Verified module: M` **even when the module failed**. Confirmed
directly on a two-line scratch file: the output ends

```text
Verified module: Hyg
1 error was reported (see above)
```

Success is: **exit code 0**, *and* `All verification conditions discharged
successfully` present, *and* no `error(s) was reported`. Any script that pipes
F\*'s output also needs `pipefail`, or the exit code is lost. Earlier verdicts
in this note were read off the success line and stand; nothing is withdrawn.

#### The world algebra: the type error confirmed as a type error

The decisive guard goes through, **on the very terms the refutation used**:

```fstar
guard_padm_xrel_transitive_at_the_composed_world ()
  : Lemma (pwf_world qw012 /\
           padm_xrel fcl_rel qw012 qdA qdB /\
           padm_xrel fcl_rel qw012 qdB qdC /\
           pwf_world (pwcompose qw012 qw012) /\
           padm_xrel fcl_rel (pwcompose qw012 qw012) qdA qdC /\
           pwlookup_l 1 (pwcompose qw012 qw012) == None)
```

`guard_padm_xrel_not_transitive` stays true and proved — the two are
statements about different worlds and do not compete. **Nothing was weakened;
only the index moved.** The last conjunct is the non-vacuity check: the
composite is silent at `1`, so it is not a world that relates everything.

All ten items proved, and beyond them associativity, both identity laws and
inverse cancellation — so the structure is demonstrated, not asserted.

*Composition needs no side condition*, and the reason is structural: `pwunion`
required `pwcompat` because a union asks two worlds to agree about **the same
namespace pair**, whereas composition only plugs the first world's right space
into the second's left space, and each is already a bijection on its own space.

*One subtlety, caught.* Recursing naively over `w12` is **wrong** when left keys
repeat: a shadowed later pair whose right component lies in `w23`'s domain would
make the composite claim an image `w12` itself does not give. The walk decides
by `pwlookup_l i w12` — the world's own answer — and takes only the left key
from the pair being walked. That is what lets the characterisation hold with no
well-formedness hypothesis, and a mutation isolates it.

*Conflicting input is surfaced, not repaired.* Composition drops no pair
(unconditional); conflict is **impossible** between well-formed worlds (refuted
at the source); and given ill-formed input the composite keeps both pairs and is
visibly not well formed. Silently discarding one to preserve well-formedness
would be convenient and would lie about the input, so ill-formedness is left
attributed to the argument that introduced it.

*The naming, limited.* "Groupoid" is right only relative to supports:

> The proved identity, inverse and composition laws give the worlds a groupoid
> structure **relative to their finite supports**. Since composition is also
> defined for arbitrary partial bijections, the underlying untyped algebra may
> equivalently be viewed as an algebra of partial bijections; only the
> support-matched fragment is used as the nominal groupoid.

The result is the law, not the name:

```text
R[w12] x y      R[w23] y z
──────────────────────────
     R[w23 ∘ w12] x z
```

#### The next gate's real difficulty: future-world factorisation

Lifting the relation onto the algebra is **not** a recursive re-application of
the existing lemmas. The `PCtxRequests` clause quantifies over future worlds:

```text
forall w' ⊒ w.  related inputs at w'  ==>  related post results at w'
```

Having composed `w12` and `w23` into `w13`, the conclusion must answer for an
**arbitrary** future `w13' ⊒ w23 ∘ w12`. To use the two hypotheses that
`w13'` has to be factored as

```text
w12' ⊒ w12,   w23' ⊒ w23,   w13' = w23' ∘ w12'
```

and for each newly added `i ↦ k` a **fresh middle name** `j` must be chosen,
so that `w12' = w12 + (i ↦ j)` and `w23' = w23 + (j ↦ k)`. That is a
future-world **interpolation** problem. Names are `nat` and worlds are finite so
a fresh `j` exists, but what has to be proved is that

- `j` collides with neither world's middle support;
- distinct new correspondences get **distinct** `j`s;
- both extensions are `pwf_world`;
- both `pwext` the worlds they extend;
- the composite of the two agrees with `w13'` by mutual `pwext`;
- the provenance anchor and allocator freshness are preserved.

**This is the next stop-condition candidate.** If factorisation does not go
through, do not push the proof: the choice is then between the post relation's
future-world quantification being too strong, worlds needing a fresh-name
supply, and the relation being restated over *compatible pairs* of future
worlds.

Acceptance order for that gate:

1. re-confirm `PCtxDone` composition as a general lemma;
2. payload `pval_rel` composition;
3. residual/frame relation composition;
4. future-world factorisation for a **single** new pair;
5. lift to arbitrary finite world extension;
6. post-closure composition, using the factorisation;
7. compositional transitivity of `PCtxRequests` as a whole;
8. lift to the store relation;
9. a guard at a real `PCtxRequests` triple;
10. a wrong implementation that **reuses** a middle name is caught by the
    aliasing guard.

#### Verification convention, promoted

A run counts as successful only when **all three** hold:

- process exit status `0`;
- the line `All verification conditions discharged successfully` is present;
- no `error(s) was reported` line is present.

`Verified module: M` alone is **not** evidence — F\* prints it on failing runs
too. Scripts that pipe F\*'s output need `pipefail` or the exit status is lost.

#### The lift gate: factorisation is false, and that is the result

The gate stopped at steps 4 and 5, and the stop is a **refutation**, not a
failure to find a proof. Stated at the strength established:

> The gate proves that unrestricted factorisation through plain `pwext` is
> false, because composition forgets name usage in the middle run. Carrying the
> middle allocation bound is the leading repair candidate, supported by the
> existing `pwbound`/counter invariant, but its sufficiency is not established:
> allocator-respecting future extension and the existence of corresponding
> middle-store entries remain to be proved.

The witness, `guard_pwfactor_needs_right_freshness`:

```fstar
let fw12 : pworld = [(0, 1)]
let fw23 : pworld = [(5, 7)]
let fwtarget : pworld = [(0, 7)]
```

`pwcompose fw12 fw23 == []` — the right world is silent at `1` — so `fwtarget`
is a well-formed future world of the composite adding **exactly one** new pair,
which is the setting of step 4 itself. And yet:

```fstar
~(exists (a b: pworld).
    pwf_world a /\ pwf_world b /\ pwext a fw12 /\ pwext b fw23 /\
    pwlookup_l 0 (pwcompose a b) == Some 7)
```

Three lines. A future world of `fw12` still sends `0` to `1`, so the middle
name at `0` is fixed at `1`. A future world of `fw23` still sends `5` to `7`,
and — being a partial **bijection** — `5` is the only middle name it sends to
`7`. So the composite sends `0` to `7` only if `1 = 5`.

The refutation is in the **existential** form: not "the constructed
factorisation fails" but "no pair of future worlds covers the pair at all". The
strong side conditions the brief had sketched — mutual `pwext`, fresh middle
names — are not used, so there is no way around it by strengthening them.

Two independent guards, run separately from the gate, fix what the obstruction
is and is not:

| guard | expectation | outcome |
|---|---|---|
| free the right name only — `[(5,8)]` in place of `[(5,7)]` | factorisation exists | exit 0; `a`, `b` constructed from `lemma_pwfactor_one` |
| delete `pwlookup_r k w23 == None` from `lemma_pwfactor_one`, body unchanged | rejected | exit 1, at `lemma_pwextend_wf j k w23` — the deleted precondition itself |

So the obstruction is exactly right-freshness of `k` in `w23`, and the side
condition carrying step 4 is load-bearing rather than decorative.

#### Where each step landed

| # | status |
|---|---|
| 1 | PROVED `lemma_padm_pctx_compose_done`, `lemma_padm_xrel_compose_done` — all indices, no hypothesis |
| 2 | PROVED `lemma_padm_pctx_requests_payload_compose` |
| 3 | **split form only**: `lemma_pframes_rel_compose_of_pointwise` (pointwise ⟹ list, unconditional) plus unconditional discharge for `PParamF`/`PBoundaryF`/`PScopeF`. **General pointwise frame composition is not proved** |
| 4–5 | PROVED under a side condition; the general form REFUTED |
| 6–8 | not attempted — the stop condition |
| 9 | PROVED: a real `PCtxRequests` triple with a discharged `post` clause relates at the composed world and **not** at the fixed world `qw012` |
| 10 | PROVED: reusing a middle name is `~pwf_world`, and — so the rejection is not merely type-level — the composite sends `0` to `30` where the target sends `0` to `20`, so it does not even `pwext` |

Steps 6–8 were not delivered as conditional lemmas because `padm_pcomp` unfolds
to `pcomp_rel`, whose `POp` / `PHandle` / `PExtendC` / `PExtendCtxC` /
`PResumeC` clauses all carry the **same** future-world quantification. Assuming
compositionality of `padm_pcomp` would be close to assuming the theorem.

#### The diagnosis, at its actual strength

What is mechanically settled is this and no more: plain `pwcompose` together
with **unrestricted** `pwext` makes future-world factorisation false, so the
name usage the composite discards must be retained in some form.

The tempting summary — "the future-world quantification in the post clause is
too strong" — is not right as stated. The Kripke quantification itself is
needed. What is too wide is its **domain**: quantifying over every `pwext`
extension imposes obligations for extensions no allocator could produce. The
refinement is

```text
forall w'. pwext w' w ==> ...
```

into

```text
forall w'. allocator_respecting_extension nL nR w w' ==> ...
```

and a fresh-name supply is the information that refinement needs. It is a
narrowing of the quantifier's range, not its removal.

Why the middle counter is the candidate: in the counterexample `1` and `5` are
distinct identities in the middle space, but plain composition drops both
unmatched edges and yields the empty world, which then admits `0 ↦ 7` as a
future extension. Retaining the middle counter or support makes `1` and `5`
both already-used middle identities, and a factorisation identifying them
rejectable. The index of the relation should therefore be conceptually a
**bounded world** `(nL, w, nR)`, composing as

```text
(n1, w12, n2)
(n2, w23, n3)
────────────────
(n1, compose w12 w23, n3)
```

with the eliminated `n2` retained as a witness for the transitivity proof. The
prototype already has the two halves of this: `pwbound w n1 n2` says every key
the world speaks for is below the respective counter, and `pcfrel` carries
`pwbound w cf1.next cf2.next` as part of the configuration relation. What is
missing is the middle counter — and it is exactly what `pwfresh2` needs, since
it computes from `pwmaxname w12 w23`, information the composite does not hold.

#### Why counters alone may still be too coarse

A new pair `(i, k)` in a future extension has at least four cases:

1. `w12` already has `i ↦ j` and `w23` already has `j ↦ k` — an existing
   composition;
2. `w12` has `i ↦ j` but `w23` is undefined at `j` — the middle name is forced
   to `j`, only `k` is fresh;
3. `w23` has `j ↦ k` but `w12` has no correspondence into `j` — the middle name
   is forced to `j`, only `i` is fresh;
4. neither is defined — both ends fresh, and a new middle name `j >= n2` is
   chosen.

The counterexample poses as case 1 and is rejected because the two forced
middle names disagree. Requiring `i >= n1 /\ k >= n3` of **every** new pair may
therefore also exclude cases 2 and 3. Whether that is correct depends on
whether the machine ever attaches a correspondence to an already-existing
identity on one side — which is a question about the machine, not about worlds.

Before adopting the counter-based repair, this has to be settled:

> A handle allocated before the current counters but absent from the current
> world can never later become publicly observable, unless it was already
> recorded by the provenance anchor.

If it holds, future world growth is confined to new allocations and the
counter-above discipline is justified. If it does not, counters are
insufficient, and the composite must retain unmatched intermediate mappings,
existing-but-unpublished identities, and forced middle-name constraints —
that is, the **span** `w12 -> middle <- w23` rather than a single world.

#### The next scratch gate, before touching the relation

1. `pbounded_world nL nR w = pwf_world w /\ pwbound w nL nR`;
2. define a candidate allocator-respecting future extension;
3. one paired allocation of the machine satisfies it;
4. today's `0 ↦ 7` falls outside the extension domain;
5. decide against the machine whether existing-left/fresh-right and
   fresh-left/existing-right are to be admitted;
6. single-pair factorisation;
7. factorisation for finitely many pairs;
8. the factor worlds agree with the middle store and counter;
9. B2b.2's one-step world extension satisfies the new discipline;
10. no counterexample where a captured handle suddenly enters the world later.

Step 8 is the one that matters. A middle name `j` can be chosen logically and
still name nothing: without a corresponding entry in the middle store the
factorisation has fabricated a name rather than found one. `j` must correspond
to an allocation of the middle run.

#### The middle name is not always fresh

The brief's sketch was wrong in one of two cases. If `w12` already speaks at
`i`, no future world may revise that answer, so the middle name is **forced**
and a fresh name is incorrect; the choice exists only where `w12` is silent at
`i`. `pwmidname` therefore branches on the world's own lookup, as
`pwcompose_from` does:

```fstar
let pwmidname (w12 w23: pworld) (i: nat) : nat
  = match pwlookup_l i w12 with
    | Some j -> j
    | None -> pwfresh2 w12 w23
```

Injectivity of the middle names is not an extra property but a consequence of
this choice: `pwfactor_many` re-takes `pwfresh2` against the **grown** worlds
at each step, so an earlier middle name already lies in the left factor's
range, and `lemma_pwfactor_middle_names_distinct` reads distinctness off that.

#### What this gate does not claim

- **The post clause's composition is not shown false.** Only the factorisation
  route is. Several attempts at a counterexample to the clause itself died —
  the future-world quantification pins the closure near the identity outside
  the world's domain — but that is an observation, not a proof. Undecided.
- Step 9's guard passes because `ppost_id` is equivariant, which reduces its
  future-world clause to the hypothesis given. It witnesses that a
  `PCtxRequests` clause **can** compose, not that one always does.
- That `PBindF` / `PSiteF` / `PModeF` / `PPromptF` are blocked by the same
  counterexample is read off the shape of `pframe_rel`. It is a claim about the
  proof route, not a machine-checked fact.
- The `pwbound` repair sketched above is an argument, not a theorem. Only the
  refutation is proved.

An unexplained phenomenon is recorded as an outstanding obligation: an Error
168 (syntax) that occurs **only** in the full-file context, where textually
identical code verifies in a small module. No minimal reproduction exists and
the cause is unidentified; `#push-options` should not affect parsing.

The stop does not refute the design. It locates what plain partial-bijection
composition loses — the names the middle run has already used — and shows the
Kripke closure needs it. The middle counter is the smallest candidate, and its
admission condition is not only that a name is fresh but that it is an identity
really present in the middle run.

#### The bounded-world gate: the repair's local sufficiency, established

The gate did not stop. What it settles, at exactly that strength:

> The bounded allocator discipline is sufficient for the one-pair factorisation
> required by the three allocating transition rules, and the chosen middle
> identity is the identity actually allocated by the middle machine
> configuration. It has not yet been propagated through the whole transition
> dispatcher or installed into the logical relations and observations.

Three things make this more than a repair candidate kept alive.

**The counterexample is excluded by the allocator's discipline, not by an
ad-hoc lookup condition.** The old `lemma_pwfactor_one` had to *assume*
`pwlookup_r k w23 == None` — a condition read off the worlds, which the previous
gate refuted the deletion of. In the new `lemma_pwallocfactor_one` that
condition is a **conclusion**, derived from `k >= n3` and `pwbound w23 n2 n3`:

```fstar
let pwalloc_ext (n1 n2 m1 m2: nat) (w' w: pworld) : prop
  = pwf_world w' /\ pwext w' w /\ n1 <= m1 /\ n2 <= m2 /\
    (forall (i k: nat).
       pwlookup_l i w' == Some k /\ pwlookup_l i w == None ==>
       n1 <= i /\ i < m1 /\ n2 <= k /\ k < m2)
```

The hypotheses of step 6 are now two `pbounded_world`s and two numeric
inequalities; no world lookup appears. Step 7's discipline is likewise purely
numeric — `pwallocfactorable` mentions no world at all. A mutation guard fixes
that this is load-bearing: deleting only `n3 <= k` and leaving the proof body
alone fails at `assert (pwlookup_r k w23 == None)`, the very conclusion the
inequality buys.

**The middle identity is constructed, not fabricated.** The prediction held: the
middle name is not `pwfresh2 w12 w23` but the middle allocator's `n2`.
`lemma_pwallocfactor_one_middle_store` is stated against a middle
*configuration*, and shows the chosen name is the handle `PCtxKey n2` that
`palloc` hands the middle run and the key its store then holds. The negative
half is proved too: whenever `n2 < pwfresh2 w12 w23`, the `pwfresh2` name is
absent from the middle store *even after* the middle run allocates. At the
refutation's own worlds the middle counter is `6` while `pwfresh2 fw12 fw23`
is `8`, and in a concrete middle store with keys `0..5` the post-allocation
lookup gives `Some cx` at `6` and `None` at `8`. A name fresh for two *worlds*
names nothing; a name the middle *run* is about to allocate names something.
Instantiating the lemma at those worlds, at the counters they force, with a
real middle configuration, and reading concrete facts out of it confirms the
hypotheses are satisfiable — a lemma with unsatisfiable hypotheses could not do
that.

**Narrowing the quantifier's domain buys a semantic property.** Under plain
`pwext`, identity revival really happens: `guard_bw_revival_under_plain_pwext`
exhibits a handle below the counters, absent from the world, that a legal
`pwext` future makes publicly observable again. `pwalloc_ext` rejects it for
every choice of end counters. So step 10's claim is not a fact about worlds; it
is a fact about the **narrowed domain**, and the narrowing is what pays for it.

#### Where each step landed

| # | status |
|---|---|
| 1 | PROVED `pbounded_world`, preserved by paired allocation |
| 2 | PROVED `pwalloc_ext`; `lemma_pwalloc_ext_bound` **derives** the counter growth rather than assuming it; no `{:pattern}` needed, since it is a plain `Tot prop` abbreviation that unfolds in hypothesis position |
| 3 | PROVED — one paired allocation of the machine is an allocator-respecting extension (soundness: the predicate admits what the machine really does) |
| 4 | REFUTED — the previous gate's `[(0,7)]` lies outside the domain for **every** admissible counter assignment (`n1 >= 1`, `n2 >= 6`, `n3 >= 8`; the new pair violates both ends); the neighbouring pair `[(1,8)]` is admitted and really factors, through middle name `6` |
| 5 | see below |
| 6 | PROVED — the ad-hoc side condition is gone, moved from hypothesis to conclusion |
| 7 | PROVED — `pwallocfactorable` is numeric; no world occurs in it |
| 8 | PROVED — the middle name is `n2`, tied to a real middle allocation |
| 9 | PROVED — the three world-growing rules of B2b.2 re-proved with the strengthened conclusion, and strengthened ⟹ the existing `pstep_compat_at`; the discipline **refines** the proved theorem rather than contradicting it |
| 10 | PROVED under the discipline; REFUTED under plain `pwext` |

#### The verdict on cases 2 and 3, limited

Every site where a world grows is a *paired* allocation
`pwextend cf1.next cf2.next w` under `pwbound w cf1.next cf2.next`. There are
three in the machine — `lemma_step_extendctxc` (`PExtendCtxC`),
`lemma_pyield_compat` (production), and the `PScopeF` branch of
`lemma_step_var` (the scope floor). Every other rule goes through
`lemma_step_same_world` and leaves the world alone. The non-machine sites —
anchor growth, the sibling union, the probe world, the fixed guard fixtures —
were each checked against the discipline separately.

The conclusion is to be read at this strength and no wider:

> Cases 2 and 3 do not occur for a pair newly introduced by a related machine
> transition under the bounded-world invariant.

It says nothing about arbitrary mathematical `pwext`, nothing about pairs
already inside a world, and nothing about a future implementation. The
disappearance of `pwmidname`'s two-case branch — forced middle name versus
chosen one — holds inside the allocator-respecting extension domain, not
generally.

The exhaustiveness of the enumeration is a **grep-based reading**, not a
machine-checked claim. Each individual site's conformance is machine-checked;
that these are all the sites is not. This is precisely what the next gate is
for.

#### The gap that must close before the relations move

The strengthened conclusion was proved for the three world-growing rules only.
The whole dispatcher `lemma_pstep_tr_compat` — some forty rules — has **not**
been re-proved with it, and this **cannot be derived after the fact**:
`pstep_compat_at` merely existentially quantifies a successor world without
recording which one it is, so the upper bound `pcfrel` supplies (keys below the
successor counters) yields no lower bound (keys at or above the starting
counters). The forty rules have to be re-proved from scratch.

The quantification domain of the relations must not be swapped before that
lands. The strengthened theorem has to retain at least:

- the successor world satisfies `pbounded_world` at the two successor
  configurations' counters;
- the world's change is either *unchanged* or *extended by the pair of the two
  sides' current counters*, and nothing else;
- in the allocating rules, the added key pair is the actual `palloc` result on
  each side;
- the non-allocating rules leave the world untouched;
- the existing `lemma_pstep_tr_compat` follows from the strengthened one.

In that form the forty rules are not bulk work: they promote "only three rules
grow the world" from an observation about `grep` output into an exhaustive
machine proof about the dispatcher.

The stop condition is correspondingly sharp. If any remaining rule changes the
world, advances a counter alone, or does not let the successor world's
provenance be recovered, the gate reports and the quantification domain does
not move.

#### Position

> The bounded-world repair's local sufficiency is established; it is not yet
> adopted as a preservation theorem for the machine as a whole.

The direction is settled. Integration waits on the next gate.

#### What this gate did not prove

- **No relation was changed** — `pcomp_rel`, `padm_pcomp`, `pframe_rel` and the
  observations are untouched, and what breaks when `pwalloc_ext` is substituted
  into them is unknown.
- The full dispatcher, as above.
- The enumeration's exhaustiveness, as above.
- Step 10's machine-level refutation attempt did **not** succeed. Two routes
  were tried and blocked: building a transition that revives a below-counter
  handle (blocked because all three growth sites add only `cf1.next`), and
  reaching observability through the store while bypassing the world (blocked
  because `pval_rel`'s `PCtxKey` clause requires the world to speak, and the
  emission trace is `list string` and carries no keys). A blocked refutation
  attempt is an observation, not a proof.

#### The dispatcher gate: a preservation theorem for every related step

The gate did not stop. The previous gate's local sufficiency is now a
preservation theorem for the machine's whole one-step relation:

> For every related machine step, the successor world either remains unchanged
> together with both allocation frontiers, or is extended by exactly the pair of
> identities returned by the two corresponding allocations, with both frontiers
> advanced once.

It is a **relative** theorem, and the premise belongs next to the statement:

> The dichotomy is a relative preservation theorem under the bounded-world
> invariant. In the intended dispatcher use this premise is supplied by
> `pcfrel`; as a standalone statement it is necessary and cannot be dropped.

So this is not a result about conveniently chosen initial worlds. It preserves a
property across the legitimate machine states the relation itself guarantees.
That the premise cannot be dropped is machine-checked:
`guard_prov_needs_the_bound` refutes the version of the first implication with
`pbounded_world` removed.

The dichotomy, with the counter clause that does the work:

```fstar
let pprov_step_at (#v #cl: Type) (w' w: pworld) (cf1 cf2 cf1' cf2': pconf v cl)
  : prop
  = (w' == w /\ cf1'.next == cf1.next /\ cf2'.next == cf2.next) \/
    (w' == pwextend cf1.next cf2.next w /\
     cf1'.next == cf1.next + 1 /\ cf2'.next == cf2.next + 1 /\
     pprov_alloc_at w' w cf1 cf2 cf1' cf2')
```

`pprov_alloc_at` pins the added pair to `palloc`'s actual result on each side,
so the second disjunct cannot be satisfied by an arbitrary fresh pair.

#### What is established: semantic exhaustiveness

- every arm of the dispatcher proves one of the two shapes;
- a hidden world growth could satisfy neither shape, and the proof would fail;
- an arm advancing a counter alone fails the same way;
- on growth the pair is not any fresh pair but the two sides' actual `palloc`
  results;
- the existing one-step compatibility is a corollary of the strengthened
  theorem — `lemma_pstep_tr_prov_compat` carries **exactly** the hypotheses of
  `lemma_pstep_tr_compat`, and the old theorem is derived from it.

The chain `pstep_prov_compat_at ==> pstep_alloc_compat_at ==> pstep_compat_at`
is proved, so nothing previously established is disturbed. One by-product is
worth naming: `lemma_pprov_step_recovers_the_pair` reads the added
correspondence and both stores' shape back out of a growing step. That is the
**lower bound** the previous gate showed `pcfrel` alone could never supply, and
its absence was the whole reason the dispatcher had to be re-proved rather than
patched.

All nineteen named rule lemmas, the two plumbing lemmas, the terminal and
mismatch arms, the dispatcher, and the two derivations are machine-checked.
Nothing stopped and nothing was left unattempted.

The dichotomy discriminates on real transitions in both directions.
Independently of the gate, four checks were run against the finished file:
claiming the scope-floor transition has the unchanged shape fails; claiming the
emitting transition has the allocating shape fails; and both matching claims
pass. No rule can choose its own shape.

#### What is explicitly not claimed

- **Not** a syntactic theorem that `palloc` occurs at only three sites. The
  `grep` reading remains a syntactic claim; what was theorematised is the
  semantic one. The syntactic claim implies the semantic one, and the converse
  is not asserted.
- **Not** an unconditional dichotomy for arbitrary initial configurations — see
  the bounded-world premise above.
- **Not** allocator provenance across a finite run.
- **Not** any change to the logical relations: the future-world quantification
  domain has **not** been swapped, and what breaks when it is remains unknown.
- **Not** full store invariance on the unchanged branch. What the first disjunct
  fixes directly is the world and the two counters. Ruling out overwriting or
  deleting an existing entry needs a separate store-monotonicity or
  single-writer lemma; the earlier "`palloc` is the only writer" result may
  serve, but it is not part of this gate's result and should not be folded into
  it.

#### Position

> The bounded-world repair is now established as a preservation theorem for
> every related single machine transition. Its finite-run closure and its
> installation into the Kripke quantification remain open.

The gap is narrower and has changed character. The question is no longer whether
the dispatcher has an exceptional arm. It is how to fold a proved one-step
provenance along a finite sequence, and how to transplant the result into the
relation's quantification domain.

#### The finite-run order

1. derive one-step `pwalloc_ext` from one-step `pprov_step_at`;
2. prove transitivity of `pwalloc_ext` with the middle counters connected;
3. induct over `prun` / `psteps`, showing the final world is an
   allocator-respecting extension of the starting world;
4. read off that the final counters advanced by the same amount on both sides,
   and that each added correspondence lies within that range;
5. derive the existing finite-run compatibility from the strengthened one;
6. only once all of that lands, move the relation's quantification domain.

Beyond `pwalloc_ext n1 n2 n1' n2' w' w`, the finite-run theorem should also
yield

```text
n1' - n1 == n2' - n2
```

— equivalently, that related runs perform the same number of allocations on each
side. The one-step dichotomy should give it naturally, since each step either
advances neither frontier or advances both by one.

#### The finite-run gate: provenance closed under arbitrary fuel

The induction closed. The bounded-world repair now holds not for one step but
for a related run of any finite fuel:

> Under exactly the hypotheses of the original finite-run compatibility theorem,
> related runs end in a bounded successor world that is an allocator-respecting
> extension of the initial world, and the two allocation frontiers advance by
> the same amount.

Four things are worth keeping apart.

**1. The hypotheses are identical to the old `lemma_prun_compat`'s.** Same six
conjuncts, same order — compared directly, not asserted. `pbounded_world` was
not added: `pcfrel` already contains `pwbound w cf1.next cf2.next`, and it is
discharged inside rather than assumed.

**2. What the conclusion gained.** An allocator-respecting extension of the
initial world for the run's counter window, `pbounded_world` at the final
counters, and the balanced-frontier equation. It is stated additively —

```text
(fst (prun lk apply fuel cf1)).next + cf2.next
  == (fst (prun lk apply fuel cf2)).next + cf1.next
```

— which expresses `n1' - n1 == n2' - n2` while avoiding F*'s truncating `nat`
subtraction.

**3. The equation does not come from the extension.** This is the central point:

> The balanced-frontier equation is not recovered from the weak final-world
> extension. It is carried independently from the exact one-step dichotomy and
> composed along the run.

`lemma_prov_step_facts` reads extension, successor boundedness and the counter
difference off `pprov_step_at` at each step — the difference being `0 == 0` in
the static shape and `1 == 1` in the allocating one. `lemma_prun_alloc_compose`
then composes them; it is a pure world-and-counter lemma with no `prun` in it at
all. The route that folds only the `pwalloc_ext` weakening was not taken, and
could not have been: `guard_run_counter_eq_not_from_alloc_ext` refutes the
implication **schema**, not merely one instance, so the provenance of the
information is formally separated rather than a matter of proof style.

**4. The old theorem is a corollary.** `lemma_prun_compat_of_prov` derives it.
Nothing is replaced; the existing result is refined and stays in use.

#### Two things the guards fix

The concrete run runs both shapes: two non-allocating transitions, then one that
allocates on both sides in lockstep, then nothing. Its two configurations start
at **different** frontiers — 1 and 0, the left having already allocated and
discarded a context — and finish at 2 and 1. So:

> The equation does not hold merely because the two final counters are equal;
> the runs may start and finish at different absolute frontiers while advancing
> by the same amount.

Independently of the gate, mis-pairing the operands of the additive equation on
that run is rejected, and the two final frontiers really are 2 and 1.

The second guard exhibits a world that names a key the left side had already
discarded before the two met. It satisfies `pwext`; it does not satisfy
`pwalloc_ext`. Stated at the strength shown:

> the admissible successor-world witnesses have been narrowed.

Not that the new theorem is strictly stronger than the old — no complete
inequivalence witness separating the two propositions was produced. What was
proved is the discriminating power of the world-witness condition.

#### `psteps`

Covered as a corollary, not by a second induction: `lemma_prun_erase` already
says `fst (prun …) == psteps …` at every fuel and configuration, so world,
boundedness and counter difference transfer. This is **not** two semantics
proved separately; it is reuse of the erasure theorem for the instrumented
semantics.

#### Position

> The bounded-world repair is now closed for arbitrary finite related runs. It
> has not yet been installed into the recursive logical relations, their Kripke
> quantification, or the observation relations.

#### The next gate is an indexing design, not a substitution

Replacing `pwext` by `pwalloc_ext` in the relations is not a textual swap.
`pwalloc_ext` needs the starting and finishing counters as well as the world, so
the first decision is how to carry allocation frontiers into relations that are
currently indexed by a world alone. The order that keeps the comparison
available:

1. define the allocation-aware relation **beside** the existing one, changing
   nothing;
2. fix the signature that carries a world and the two frontiers as one Kripke
   state;
3. prove accessibility reflexive and transitive;
4. check that concrete `nboundary`s, captured consumers and machine-built stores
   remain inside the domain once future-world quantification is restricted to
   `pwalloc_ext`;
5. re-prove the one-step fundamental theorem from the provenance-strengthened
   version;
6. lift to finite runs, actually using `lemma_prun_prov_compat`;
7. define the new observation relations from the new relation;
8. state only the direction that is proved about the relationship to the old
   relation;
9. only then reconnect the laws and the administrative relation.

Rewriting `pcomp_rel` in place from the start would destroy the ability to tell
whether a proof went through because allocator provenance really closed or
because the narrowed domain made it vacuous. Juxtaposition, as before.

The stop conditions are: a concrete machine-built boundary that cannot satisfy
the frontier-indexed relation; a closure `post` whose required future world
cannot be built as an allocator-respecting extension; a related step that needs
an allocation on one side only; a finite extension of a world composition that
cannot be factored; or a new relation that makes an existing positive nominal
fixture vacuous.

The gap is now one thing: moving a closed finite-run provenance into the index
design of a recursive Kripke relation.

#### The indexing gate: an allocation-indexed Kripke family, juxtaposed

Steps 1–4 of the nine-step plan landed. None of the five stop conditions was
hit. Stated at the strength established:

> An allocation-indexed Kripke family can be defined alongside the original
> world-indexed family. Its accessibility relation is allocator-respecting
> future extension between states carrying the world and both allocation
> frontiers. The family is well-founded and non-vacuous on all tested fixture
> classes; no transition compatibility or comparison with the original family is
> established yet.

Four things are worth recording.

**The narrowing does not exclude base-world carriers; it restricts only future
accessibility.** This is the structural fact that saves the existing fixtures,
and it is easy to mistake for a triviality. It is not one: the restriction bites
on extensions, and that it bites is proved.

**Any finite probe world can be given a large enough frontier.** So the fixed
counter-less worlds the development already built fit into a `pastate`:
`qw00` at 1, `qmid_w_flip` at 2, `qw012` at 3, `ganchor` at 4, `nw56` at 7. The
lemma behind this says exactly:

> Every finite probe world can be embedded into some frontier-indexed state.

and no more. It does **not** say that frontier is the actual counter of any
particular execution configuration. Machine-built fixtures carry that additional
obligation separately, through guards using the real counters and the store
anchor. The two kinds of non-vacuity are different and are kept apart here.

**Whether a stale pair is admitted depends on the starting frontier, not on the
pair.** At frontiers `(5,5)` the pair `(0,0)` is a perfectly legal `pwext`
extension of the empty world and is accessible for *no* final frontiers; at
frontiers `(0,0)` the same pair is accessible with final `(1,1)`. Both halves
are machine-checked, independently of the gate.

**The new family is a faithful copy, not a copy with incidental edits.** The two
families were diffed directly. Every difference is one of exactly three kinds:
the name prefix; `w` becoming `s.aw`; and the future-world quantifier

```text
(forall (w': pworld) (y1 y2: pval v).
   pwf_world w' /\ pwext w' w /\ pval_rel w' y1 y2 ==> …)
```

becoming

```text
(forall (s': pastate) (y1 y2: pval v).
   paext s' s /\ pval_rel s'.aw y1 y2 ==> …)
```

Every clause with no future-world quantifier — `PVar`, `PPerform`, `PParamF`,
`PICell`, `PITransparent`, `PWriteP`, the list cases, `pplan_rel` — is
structurally identical modulo the rename. `pwf_world w'` was not dropped: it is
a conjunct of `pwalloc_ext`, so `paext` subsumes it. Juxtaposition therefore
still permits the comparison it exists for.

#### The carrier and the accessibility

```fstar
type pastate = { aw: pworld; an1: nat; an2: nat }
let pawf (s: pastate) : prop = pbounded_world s.an1 s.an2 s.aw
let paext (s' s: pastate) : prop
  = pwalloc_ext s.an1 s.an2 s'.an1 s'.an2 s'.aw s.aw
```

A record rather than three parameters, because seven mutually recursive
relations would each gain two arguments and every quantifier two binders,
destroying the readability that juxtaposition depends on; and rather than a
tuple, because `fst`/`snd` chains inside a `prop` are exactly the projection
noise the development already avoids.

The termination measure is unchanged — the state is a parameter no recursive
call inspects, so the existing lexicographic measures carry over untouched, and
type-checking is the proof.

Reflexivity and transitivity reduce to `lemma_pwalloc_ext_refl` and
`lemma_pwalloc_ext_trans` and to nothing else. Transitivity reduces cleanly
**because the intermediate state supplies the middle counters** — which is
precisely what a world-only index could not do. Stated with its premises:

> `paext` forms a preorder on admissible allocation states.

Not on raw `pastate`s: the lemmas carry the well-formedness and boundedness
premises, and `pwalloc_ext` itself contains at least the successor world's
`pwf_world`.

#### Non-vacuity

Seven negative guards survive the narrowing, and for each one the reverse claim
was checked to be unprovable — so every discrimination has all three of a proved
positive, a proved negative, and an unprovable converse. Among them, one guard
refutes through the narrowed clause itself, using an **asymmetric** allocation
witness: `pwalloc_ext` confines new names to their own windows without tying the
two sides together, so taking the right name past the guessed one keeps a
captured handle from accidentally pinning itself.

Notably, the `PParamF` residual discrimination has no `forall w'` in its clause
at all, so it is untouched by the narrowing — it serves as the control that the
copy did not damage the parts it should not have touched.

#### What is not established

- No compatibility with the machine's transitions, and no comparison in either
  direction with the original family.
- **Kripke monotonicity for the new family is not attempted.** The old family's
  `pwext` monotonicity does not transfer as it stands: `paext` mentions the
  frontiers on both sides, so pushing a relation forward along an access also
  moves the domain of its own future quantification.
- One conjecture is recorded and explicitly fenced: that because the term
  language has no way to compare handles, the narrowing can never make a *new*
  pair related. That is step 8 territory, it is unproved, and the next stage
  must not rely on it.

#### Position

> The new Kripke carrier and accessibility relation are now inhabited and
> discriminating. The next question is whether the recursive relations are
> monotone under that accessibility; only after that may transition
> compatibility be attempted.

#### Monotonicity comes before step 5, as its own gate

This is not auxiliary polish. It is the test of whether the new index really
behaves as a Kripke index.

1. state the admissibility condition on a `pastate` explicitly;
2. collect reflexivity and transitivity of `paext` on that domain;
3. prove `pval_rel` preserved along growth of `s.aw`;
4. prove, for every layer of the `pa*_rel` family, that `paext s' s` lets a
   current relation be pushed forward to the future state;
5. check that captured consumers, capturing clauses and `PCtxRequests.post`
   survive an allocation without being re-proved;
6. contrast: an extension admitting identity revival below a frontier falls
   outside accessibility.

For a standard Kripke relation this would follow from transitivity alone —
anything reachable from a future state is reachable from the original. Here the
value relation at the current world and the domain of the future quantifier move
*together*, so it must be proved across the whole mutual recursion rather than
assumed.

Stop conditions: monotonicity does not close under `paext` transitivity alone
and needs an extra hypothesis per closure; an existing captured closure's proof
has to be rebuilt after an allocation; the machine-built `nboundary`'s clause or
application cannot be preserved for the new family; or `PCtxRequests.post`'s
future quantification does not agree with pushing the frontiers forward.

On that last point, what is confirmed today is only that `nboundary`'s `b_rel`
applies at `s.aw` and that its concrete capturing pair inhabits the new family.
The boundary record's `apply` coherence conditions are stated against the
**old** relation, so they cannot yet be reused for a new fundamental theorem. Step 5
will need either a boundary discipline for the new family or a bridge from the
old conditions to the new.

#### The monotonicity gate: the new index behaves as a Kripke index

The gate closed, and none of its four stop conditions fired.

> Every recursive member of the allocation-indexed relation family is
> Kripke-monotone along `paext`, under no side condition beyond the direct
> allocation-aware counterparts of the original family's premises. The proof
> requires an explicit future-shrinking lemma because allocator-respecting
> accessibility is propositional rather than definitional.

The premises line up exactly:

```fstar
old: requires pcomp_rel  r n w c1 c2 /\ pwext w' w /\ pcl_mono r
new: requires pacomp_rel r n s c1 c2 /\ paext s1 s /\ pcl_mono r
(both at measure %[n;0;0])
```

Same number of premises, same roles, same measure; nothing added — no `pawf`,
no `pbounded_world`, no closure-specific condition. But `paext` is semantically
narrower than `pwext`, so this is not "the same logical premises". It is

> the same premise schema, with the accessibility relation replaced by its
> allocation-aware counterpart.

The asymmetry the gate was told to look for does not exist at the level of the
statement. It exists at the level of the proof, and precisely once per layer:
`pwext`'s transitivity is definitional and the solver finds it unaided, while
`pwalloc_ext`'s is a case-splitting lemma that has to be handed over. That is
what `lemma_paext_future_shrinks` — the `{:pattern}`-carrying quantified form of
`lemma_paext_trans` — is for, and removing a single call to it makes the
induction fail.

#### Bare `pwext` is refuted as the accessibility relation

`guard_pa_mono_fails_along_bare_pwext` states the negation of the
`pwext`-shaped monotonicity principle outright. Its witness is a pair of
functions that agree on every key at or above 5 and disagree at key 0: related
at `pa_low` (empty world, frontiers `(5,5)`, so every accessible state's new
names are at or above 5), unrelated at `pa_revive` (world `[(0,0)]`, frontiers
`(0,0)`), which plain `pwext` reaches.

At the strength the in-file guard establishes:

> The guard refutes bare `pwext` as the accessibility relation for
> frontier-indexed states. Its witness includes both a below-frontier identity
> revival and a frontier rollback; isolating revival under nondecreasing
> frontiers would require a stronger guard.

That stronger guard was written and checked in a **scratch module** — not
appended, so not part of the verified prototype: the same world step
`[] -> [(0,0)]` with frontiers held at `(5,5)`, hence nondecreasing, still fails
both `paext` and the monotonicity conclusion. It should be added to the file in
the next gate so the isolation is on the record where the rest of the
development is.

Separately and already in the file, `guard_bw_revival_under_plain_pwext`
quantifies over **all** final frontiers, so the accessibility half of the
isolation is settled there. Reading the two together suggests the cause is the
revival alone; that reading is a **diagnosis from two proved facts**, not a
theorem, until the isolating guard is in the file.

#### Captured closures cross an allocation without re-proof

Each guard's body is three lines — an old fact, `lemma_paext_of_alloc`, one
application of monotonicity — and the `post` clause's future quantification is
never re-unfolded. `PCtxRequests.post` agrees with pushing the frontiers
forward.

`nboundary` is reused verbatim, and the `pcl_mono` the transport needed came
from the record's own `b_mono` field. So:

> no new boundary premise was needed for monotonicity

is established. This is **not** the same as saying the old boundary record
suffices for an allocation-aware fundamental theorem — `b_apply_eq`,
`b_apply_wb` and `b_lookup` are still stated against the **old** relation, and
whether they carry over is undetermined.

#### Store realization is not monotone, and is not meant to be

`pasrel` is not Kripke-monotone, and this is a separation of roles rather than a
hole. It is not a semantic clause of the relation family; it is a **world
satisfaction / store realization** statement: for every key pair the world
relates, both concrete stores must have an entry, and those entries must be
related. Extending the world therefore *creates* obligations. Advancing the
world without extending the stores naturally breaks satisfaction.

> The recursive semantic relations are Kripke-monotone. Store realization is
> not, and is not expected to be: extending the world creates new store
> obligations. Its preservation belongs to transition compatibility, where world
> growth is coupled with the corresponding allocations.

The original `psrel` behaves identically — checked directly: it holds vacuously
at the empty world, fails at `[(0,0)]` against empty stores, and its
monotonicity principle is false. There is no monotonicity lemma for it anywhere
in the development. So this is inherited from the design being copied, not
introduced by the new index.

#### Position

> The allocation-indexed semantic relations are now genuine Kripke relations.
> What remains is to prove that the machine realizes their future worlds by
> extending the concrete stores in lockstep; store realization cannot be
> obtained from monotonicity alone.

#### The next gate decides the boundary's shape first

One-step transition compatibility, but the boundary question comes at the front
of it, not as an afterthought:

1. formulate allocation-aware `apply` / `lookup` compatibility;
2. decide whether it follows from the existing boundary or needs a parallel
   `paboundary`;
3. instantiate at `nboundary` concretely, to check non-vacuity;
4. the non-allocating rules preserve the same `pastate` and the same `pasrel`;
5. the three allocating rules construct the successor `pasrel` using the actual
   `palloc`, `pwextend` and frontier increment together;
6. the allocation-aware step theorem for the whole dispatcher;
7. keep the old step theorem as a corollary, or juxtapose both;
8. only then lift to finite runs.

`pasrel`'s non-monotonicity is not an obstacle there — it is the load-bearing
point that tests whether the three allocating rules really grow world and store
in step.

#### The boundary gate: a parallel discipline, and store realization locally

> The allocation-aware fundamental theorem requires a parallel boundary
> discipline rather than the old boundary record alone. This discipline is
> non-vacuous: `naboundary` satisfies it. Locally, non-allocating transitions
> preserve store realization at the same allocation state, while allocating
> transitions preserve it by advancing the world, both frontiers, and both
> concrete stores together through the actual `palloc` results. These local
> obligations have not yet been assembled into a dispatcher theorem.

#### The boundary choice resolved

This is better recorded as a designed fork settling than as a stop condition
firing:

> The boundary-choice condition resolved in favour of a parallel
> allocation-aware record.

The three coherence conditions behaved differently. `papply_wb` mentions no
relation at all and is reused by name. `plookup_equivariant` is stated over
`ptable_rel`, which the new family reuses unchanged, and it carried over as an
**equivalence**, not merely an implication — the reverse direction is witnessed
by instantiating at `{ aw = w; an1 = 0; an2 = 0 }`. So `paboundary` differs from
`pboundary` in exactly one of its eight fields: `pb_apply_eq`. `pb_lookup` still
carries the **old** `plookup_equivariant`.

The variance is what forces the split. In `papply_equivariant`, both
`pfn_rel_at` and `pcrel` belong to the family with future-world quantification.
On the conclusion side `pcrel r s.aw ==> pacrel r s` is the direction that
holds; on the hypothesis side the direction that holds is
`pfn_rel_at r s.aw ==> pafn_rel_at r s`, which is the wrong way round. Invoking
the old condition would need `pafn_rel_at ==> pfn_rel_at`, over strictly more
futures. Both strictness claims are refuted rather than argued, and the bridge
the derivation would require is itself refuted.

The witness is one consumer pair: it satisfies `pafn_rel_at` at `pa_low` — empty
world, frontiers `(5,5)`, so every accessible state's new names are at or above
5 — and fails `pfn_rel_at` at `pa_low.aw`, because plain `pwext` admits
`[(0,0)]`, where the two disagree. Verified independently of the gate.

Nothing here introduces a new trust assumption:

- the old record keeps `apply`/`lookup` coherence for the old relation;
- the new record keeps the counterpart for the allocation-indexed relation;
- `naboundary` proves every field concretely;
- no `admit`, no axiomatic field.

So: **the proof interface had to change, not the concrete interpreter
semantics.**

The strength of "not derivable" should be read as the proof supports:

> the old record does not provide enough information to derive the new condition
> in this development

and not as a claim that no formulation whatsoever could derive it. What was
proved is the non-existence of the derivation through the continuation premise,
plus refutations of the two strictness directions — not a semantic
counterexample separating an interpreter that satisfies the old condition from
one that breaks the new.

#### The two local forms, and why they divide

**Non-allocation.** `lemma_pasrel_nonalloc`: the allocation state is unchanged,
both concrete stores are unchanged, and store realization survives on
reflexivity of the world alone. That `pcl_mono` and the family's monotonicity
lemmas are not needed is natural — neither the world's obligations nor the
stores' witnesses have grown. The `requires` reads as the evidence: world
well-formedness, for reflexivity, and the two store identities. Nothing else.

**Allocation.** This is the load-bearing side. `lemma_pasrel_alloc` moves five
things at once:

- a new correspondence in the world;
- each frontier advanced by one;
- a matching entry added to each concrete store;
- the handle being the **actual** `palloc` return value;
- the successor `pasrel` constructed from those.

The central evidence is the guard showing that moving any one of them
separately fails: at the *same* transition, extending the store gives the
successor `pasrel` and not extending it does not — and the machine's own
`pstep` result for that configuration matches the coupling lemma's store and
counter literally.

That it also goes through in `PCtxRequests` shape matters. The coupling is not
established only for a simple `PCtxDone` value correspondence, but for an actual
residual-context shape carrying a stored `post` with its own future-world
quantification.

The state-indexed allocation lemma needed **no** extra hypothesis where the old
`lemma_psrel_alloc` took `m1`, `m2` and assumed `pwbound`: the frontiers are
read off the state.

#### Also landed

The isolating guard checked outside the file in the previous gate is now in it,
verbatim: with the frontiers held nondecreasing, the failure of monotonicity
along bare `pwext` is the below-frontier identity revival alone, not a frontier
rollback.

#### Proof engineering, kept separate from the semantic result

The old `lemma_napply_equivariant` needed `--fuel 3 --ifuel 3`. Its
allocation-aware counterpart verifies at **default fuel**, because the case
analysis was split into auxiliary lemmas rather than the limit being raised.
Decomposition stabilised proof search where loosening the budget would have
hidden the shape of the problem. Reusable, and unrelated to what the gate established
semantically.

#### Not claimed

- an allocation-aware one-step fundamental theorem;
- compatibility for every dispatcher arm;
- any relation between successor configurations including the trace;
- finite-run compatibility;
- any implication between the old and new relations, or between the two boundary
  records;
- any connection to the observation relations or the laws.

The stage reached is **not** "all the material for every transition is in
place". It is:

> the two local store-realization preservation laws that the dispatcher proof
> will need are in place.

#### Position

> The allocation-aware boundary is inhabited, and both local forms of
> store-realization preservation are proved. The next gate must show that every
> dispatcher arm selects one of those forms and returns a single successor state
> satisfying the complete transition relation.

#### The next gate: the dispatcher's one step

Its conclusion must carry, simultaneously: a successor allocation state `s'`;
`paext s' s`; the allocation-aware relation on the successor configurations;
`pasrel` on the successor stores; equality of traces; for the allocating rules,
world, frontier and store provenance in the actual `palloc`; and for the
non-allocating rules, `s' = s`.

1. fix the allocation-aware one-step compatibility statement;
2. close the non-allocating arms with `lemma_pasrel_nonalloc`;
3. close the three allocating arms with the coupling lemma;
4. at `PPerform`, actually use `paboundary`'s apply and lookup conditions;
5. re-prove every arm of the dispatcher;
6. discriminate the two shapes with one allocating and one non-allocating
   fixture;
7. run the `PCtxRequests` route again on a residual-bearing allocation fixture;
8. only then lift to finite runs.

Stop conditions: a dispatcher arm that fits neither local form; `PPerform`
demanding the old boundary condition back; world and store successors needing
different allocation witnesses; trace compatibility and allocation-state
compatibility unsatisfiable at the same successor configuration; or `pasrel`
obtainable only by assuming an unreachable or ill-formed initial store.

#### The dispatcher gate: one-step compatibility for the new relation

> Under the allocation-aware boundary premises, every arm of the traced
> dispatcher produces a single successor allocation state that simultaneously
> relates the traces, extends the Kripke state admissibly, records whether
> allocation occurred and where its identities came from, preserves store
> realization, and relates the successor configurations.

This is not yet a fundamental theorem. It is

> the one-step transition-compatibility component of the allocation-aware
> fundamental theorem.

Finite runs, the lift to observations, and application to the laws all remain.

Sixteen computation arms and four terminal arms, all machine-checked. The
signature came out exactly as predicted, with no additional requirement:

```fstar
requires pawf s /\ pcl_mono r /\ pcl_down r /\
         plookup_equivariant r lk /\ paapply_equivariant r apply /\
         pacfrel r s cf1 cf2
```

and the conclusion carries, at once: trace equality, an existential `s'` with
`paext s' s` and `pawf s'`, the two-shape provenance `paprov_step_at`, and
`pacfrel` at the successor — which itself contains the successor stores'
`pasrel` and the counter identities.

#### The carriers, and where the hypotheses moved

The family had no state relation and no configuration relation; both had to be
defined. The design decision was whether the configuration relation should bound
the frontiers, as the old `pcfrel` did, or identify them with the
configurations' counters. The identity form was taken and no arm forced a
fallback:

```fstar
let pacfrel r s cf1 cf2
  = pastrel r s cf1.st cf2.st /\ pasrel r s cf1.store cf2.store /\
    cf1.next == s.an1 /\ cf2.next == s.an2
```

Where the information sits has moved. The old form takes world well-formedness
from outside and the counter bound from inside `pcfrel`; the new form has
`pawf s` carrying world well-formedness *and* the frontier bound, with
`pacfrel` pinning the concrete `next`s to `s.an1`/`s.an2`. Stated at the
strength that is actually established:

> The new signature is designed as a redistribution of the old information into
> an explicit allocation state. A formal equivalence or implication between the
> complete old and new theorem statements is not proved here.

What *is* proved is that the counter identity is strictly more than
`pwbound` together with `pasrel`: a guard exhibits a configuration the old third
conjunct accepts and the new one rejects. That one could rebuild the new state
from the old information by choosing the canonical
`s = { aw = w; an1 = cf1.next; an2 = cf2.next }` is a **reading of the design**,
not a bridge between the theorems, and the two should not be conflated.

#### `PPerform` confirms the parallel record by use

The arm closed on `paapply_equivariant` alone. Independently of the gate, the
whole appended region contains the old `papply_equivariant` in a **comment
only** — no arm falls back to it. Which fields were consumed, and where:

- `pb_lookup` — the old `plookup_equivariant`, unchanged, because the table
  relation is world-only; called verbatim at `s.aw`;
- `pb_apply_eq` — the new condition, for the boundary crossing itself;
- `pb_mono` — Kripke monotonicity of the captured continuation;
- `pb_down` — inversion at the prompt frame;
- `pb_apply_wb` — **not consumed**.

So:

> `paboundary` was not merely inhabitable; its changed field is exactly the
> field consumed by the dispatcher arm whose continuation crosses the semantic
> boundary.

Two probes — dropping the new condition, and substituting the old one — both
fail. They are **failed proof attempts observed in scratch, not guards**. What
they show is that the present proof route needs the new condition, not that no
semantic derivation from the old to the new could exist anywhere.

That `pb_apply_wb` went unused is worth recording: one-step relational
compatibility does not touch well-bracketedness preservation. If it stays unused
downstream the record's shared shape can be revisited; there is no reason to
call it redundant yet.

#### The two local laws are now one successor state

The previous gate proved them separately. Here they are assembled:

- non-allocating arms: `s' == s`;
- allocating arms: `s' == paalloc s`;
- the **same** `s'` satisfies the world extension, the frontier increment, the
  store extension, `pasrel` and `pacfrel`;
- trace equality holds for that same transition pair.

The world successor and the store successor need only one allocation witness
between them. And the `PCtxRequests` fixture goes through, so the coupling is
not something that holds only for a simple `PCtxDone` value correspondence.

The two fixtures were checked, independently of the gate, to sit on opposite
sides of the dichotomy as computed by the machine itself: the emitting one keeps
its counter and emits `["e"]`; the scope-floor one advances its counter and
emits nothing. Claiming the emitting fixture allocates is rejected.

#### Proof engineering

Seventy-nine transposed derived laws of the family all verify at **default
fuel and ifuel**. Nothing corresponding to the places where the old side needed
`--fuel 3 --ifuel 3` reappeared.

#### Not proved

- finite-run compatibility;
- `pnconverges` and the observation relations;
- the finite-run form of the allocation-aware fundamental theorem;
- any implication between the old and new step theorems — **in either
  direction**; only the remark that `pacfrel` follows from the old `pcfrel`
  while the converse is blocked by an existing strictness guard, neither of
  which is proved here;
- connection to the laws or the administrative observation;
- a wrapper taking a `paboundary` record directly; the premises are currently
  passed field by field.

That wrapper is not semantically required, but a thin corollary

```text
paboundary ⟹ allocation-aware dispatcher premises
```

is worth proving once before going further, so the finite-run and observation
theorems cannot silently drop a field. It does not require redoing the one-step
theorem.

#### Position

> The allocation-aware relation is now compatible with every single traced
> machine transition. The remaining semantic lift is temporal rather than local:
> compose those successor states and traces across arbitrary finite runs, then
> expose the result through convergence and observation.

#### The finite-run gate

1. the thin `paboundary` wrapper for the one-step theorem;
2. the reflexive case at fuel `0`;
3. connect the one-step successor `s₁` to the induction hypothesis's successor
   `s₂` by transitivity of `paext`;
4. concatenate the step trace with the rest of the run's trace in the same
   order;
5. read the concrete final counters and `s₂`'s frontiers off the final
   `pacfrel`;
6. fold `paprov_step_at` inductively, preserving equality of the two sides'
   allocation counts;
7. allocation-aware compatibility for `prun`;
8. `psteps` as a corollary of the existing erasure theorem;
9. non-vacuity on a concrete run containing both shapes.

The conclusion should carry at least: one final allocation state `s'`;
`paext s' s`; `pawf s'`; the final `pacfrel`; equality of the whole traces; and
equality of the two sides' frontier increments.

Stop conditions: the intermediate `s₁` cannot be eliminated in favour of a
final `s₂`; the trace concatenation orders disagree; or `pasrel` can be rebuilt
at each step but not collected into the single store realization the inductive
conclusion needs.

#### The finite-run gate: the temporal lift closes

> Under the allocation-aware counterparts of the original run theorem's
> premises, two related executions of arbitrary finite fuel produce equal traces
> and a single final allocation state that is accessible from the initial state,
> well formed, related to both final configurations, and balanced in the amount
> by which the two allocation frontiers advance.

This is still not the whole fundamental theorem:

> This closes the finite-run compatibility component. Convergence and
> observational compatibility remain to be derived from it.

The hypotheses correspond to `lemma_prun_compat`'s field for field, with nothing
added — compared directly, not asserted:

| old | new |
|---|---|
| `pwf_world w` | `pawf s` |
| `pcl_mono r`, `pcl_down r`, `plookup_equivariant r lk` | unchanged |
| `papply_equivariant r apply` | `paapply_equivariant r apply` |
| `pcfrel r w cf1 cf2` | `pacfrel r s cf1 cf2` |

#### Where the balanced-frontier equation comes from

`paext` says only that both frontiers are nondecreasing. The two-shape
provenance says that each step moves neither frontier or moves both by one.
`lemma_paprov_step_counter` extracts that — its body is `()`, so it is
definitional given the dichotomy, there being no third branch — and
`lemma_parun_alloc_compose` composes it along the run: a pure state-and-counter
lemma with no `prun` in it at all. So the balanced equation is **not** a
consequence of `paext`, and a guard refutes the implication schema, not merely
one instance. Reproduced independently: two states with `paext` and
admissibility whose increments are 1 and 2.

The character of the result is worth naming:

> The run theorem is provenance-derived but not provenance-retaining: exact
> one-step provenance is consumed during the induction and retained only through
> the aggregate accessible-state relation and balanced-frontier equation.

No run-level allocation history survives in the conclusion, and no
correspondence between each added pair and the transition that added it. That is not a problem
now. If a later world factorisation needs an **ordered** allocation history, it
will not be recoverable from this conclusion and would have to be re-derived.

#### The counter identities pay off two gates later

> The counter identities chosen at the configuration-relation gate turned a
> state-level balance equation into the concrete run-level equation by
> substitution. Had the relation recorded only upper bounds, the equation would
> not have survived definitionally.

This is not proof shortening. It is the return on indexing the relation so that
it is exactly synchronised with the concrete machine state.

#### The diagonal fixture: an evidential gap, not a hole in the theorem

`lemma_parun_compat` is proved for arbitrary related pairs of configurations, so
the theorem is not restricted to the diagonal. What is unverified is narrower:

> The theorem is universal, but its run-level fixture is diagonal. The fixture
> exercises state evolution, both allocation shapes and frontier accounting, but
> trace equality there is reflexive. Non-vacuity of the relational trace claim
> on two genuinely different executions remains unmeasured.

The world-indexed development's non-diagonal `ce_cfl`/`ce_cfr` were not
ported — confirmed absent from the appended region. Building a non-diagonal fixture needs
the world and store relations discharged afresh, not a citation of the old
`pcrel`.

Acceptance conditions for that fixture:

- the initial configurations or stores differ structurally;
- the identity world is not the trivial empty world, or the two sides' raw
  handles differ;
- `pacfrel` holds at the actual counters and stores;
- both runs emit a non-empty trace;
- the traces agree in order and multiplicity;
- at least one allocation occurs, so the successor `paext` and `pasrel` are
  exercised too;
- changing one side's event, order or multiplicity makes the guard fail.

#### Two things kept separate from the semantic result

`psteps` is covered by the erasure theorem, and the note is the same as before:

> The uninstrumented result is an erasure corollary, not a second induction.

Warning 349 appeared on `if fuel = 0 then … else <match>` and was cleared by
**splitting the definition** into a mutual recursion with a lexicographic
measure, not by raising a budget. Proof engineering: proof search stabilised
without giving the solver more room. Everything verifies at default fuel.

#### `pb_apply_wb`, unused twice

> `pb_apply_wb` has now been unused by both the one-step and finite-run
> relational compatibility proofs. This suggests that it belongs to the
> well-formed observation layer rather than the relational core, but that
> classification is deferred until the observation theorem either consumes it or
> leaves it unused again.

The places it might still be needed are the well-formed observation domain,
`pstate_wb`/`pterm_wb`, unreachability of `PPaused`, and the observation
theorem's starting-configuration conditions.

#### Not proved

- convergence and the observation relations — untouched; the only occurrences
  of their names in the appended region are ledger comments saying so;
- the laws and the administrative observation;
- any bridge between the old and new run theorems, in either direction;
- a run-level provenance predicate;
- non-vacuity on a non-diagonal run.

#### Position

> Allocation-aware compatibility is now closed under arbitrary finite fuel. The
> remaining gap before observation is evidential rather than inductive:
> exhibit a genuinely non-diagonal trace-producing run, then package the run
> theorem as convergence and observational compatibility.

#### The next order

A short non-diagonal run gate first, before any observation relation is defined:

1. build a non-diagonal allocation-aware initial configuration pair;
2. prove `pacfrel` at the actual frontiers, world and stores;
3. run it for finite fuel with a non-empty trace;
4. read out the whole conclusion of `lemma_parun_compat` at that pair;
5. mutation guards changing one trace element, its order, and its multiplicity;
6. only then define allocation-aware convergence and observation.

The observation gate will then have to derive, from the run theorem: right-hand
convergence, trace equality, related result values, the final `pasrel`, the
final `paext`, and well-formedness of the final state.

#### The non-diagonal gate: the evidential hole closes

> The allocation-aware finite-run theorem has a genuinely non-diagonal,
> trace-producing inhabitant. The two executions begin with different counters
> and stores, evolve the world by relating distinct freshly allocated raw
> identities, emit the same non-empty trace, and satisfy the complete
> final-state conclusion of `lemma_parun_compat`.

This is not a new general theorem. It is a check that the general theorem
already proved is not an empty relation off the diagonal.

#### What became non-trivial

The fixture is non-diagonal in several ways at once: starting frontiers `2` and
`1`; different stores; **different entry contents at the shared key `0`**
(`FI 7` on the left, `FI 1` on the right); a non-empty world `[(1,0)]`; raw keys
`2` and `1` corresponded after allocation; final frontiers `3` and `2`; and a
common non-empty trace `["a0"; "a1"]`.

So the balanced equation

```text
3 + 1 == 2 + 2
```

is an equality of *increments*, not of absolute values — the two final
frontiers differ. And the final-state witness cannot be replaced by the initial state, so
`paext`'s existential really does grow.

> The witness exercises nominal renaming, store realization, frontier
> advancement and trace production simultaneously. It is not merely two
> syntactically different terms running over the same empty state.

#### How to read the trace mutations

Three mutations were rejected, each changing only the right side's emission
structure and leaving stores, frontiers, handles and stack alone: one event's
identity; the order of two events; and the multiplicity of one event with its
order and its event set unchanged. A negative control confirms they fire — the
same refutation script applied to the *unmutated* pair fails, in a module where
the positive `pacfrel` is proved.

Independently of the gate, the **mirror** mutation was also checked: swapping
the two events on the **left** instead of the right is likewise rejected. So the
discrimination is not an artefact of which side was edited.

The strength has to be stated carefully:

> The positive fixture proves non-vacuity of equal non-empty traces on genuinely
> different related executions. The order mutations are rejected already by the
> input relation, showing that the relation enforces the corresponding emission
> discipline; they are not mutation tests of the theorem's trace-equality
> conjunct in isolation.

The mutations fail at the *premise*, not at the conclusion. Nothing here
independently refutes the theorem's trace-equality conjunct by deleting or
altering it.

#### Why the existing non-diagonal pair was not reused directly

`ce_cfl`/`ce_cfr` sit at the **empty** world, where `pval_rel` relates no handle
at all, so they cannot meet the requirement that either the identity world be
non-empty or the two sides' raw handles differ. The gate instead started from a
state of the shape those two reach after one lockstep allocation — world
`[(1,0)]`, frontiers `2` and `1`.

Precisely: this is **the shape of a state after one allocation**, not a
machine-reached state. `nd_s0` is constructed directly and its `pawf` is proved
from the allocation lemma; no run of `ce_cfl`/`ce_cfr` is executed to produce
it, and the fixture's stores are its own. That is sufficient here, because the
finite-run theorem's domain is admissible related configurations, not reachable
ones — but reachability is not claimed.

#### What the collapse route supplied, and what it did not

The collapse `lemma_paxrel_of_pxrel` was used for exactly one thing: the store
entries' relation at the world's single pair `(1,0)`, transporting an
old-family fact. Everything else — the two `PEmit` layers' computation
relation, the one-frame stack relation, the quantifier ranging over the
world's domain, and the **counter identities** — was discharged directly in the allocation-indexed
family. The counter identities do not follow from the collapse; they hold by the
choice of `nd_s0` and are stated.

#### Established here

- non-diagonal inhabitation of the allocation-aware run relation;
- a concrete related run with a non-empty trace;
- a worked instance where the world corresponds **distinct** raw names;
- final `paext`, `pawf`, `pacfrel` and balanced frontiers holding together;
- concrete discriminating power against event order, identity and multiplicity.

#### Still open

- the convergence relation;
- an observational preorder or equivalence;
- contextual adequacy;
- the move from nominal to administrative observation;
- the laws;
- any bridge between the old and new theorems.

#### Position

> The evidential gap before observation is closed: the run theorem now has a
> non-diagonal, non-silent inhabitant. What remains is no longer to show that
> the relation has real executions, but to package the universal run theorem into
> convergence and observation.

#### The observation gate is not a rename

`pnconverges` cannot simply be re-indexed, because a `pastate` carries both
frontiers and the world at once, so the observation's **starting domain** has to
be decided first. Two layers keep that decision honest:

1. **general form** — a paired-start observation relating two different
   ambient configurations through `pacfrel`;
2. **public form** — starting from the same public stack, store and counter,
   specialised to a canonical diagonal allocation state.

The general form takes today's non-diagonal fixture and the fundamental theorem;
the public form is what the eventual statement of the laws can use.

1. decide how allocation-aware convergence carries the final `pastate`;
2. define the paired-start observational preorder beside the old observation;
3. prove one-directional observational compatibility from `lemma_parun_compat`;
4. run today's non-diagonal fixture through it as a positive instance;
5. define the public diagonal specialisation;
6. check whether `pb_apply_wb` is consumed by the well-formed observation
   domain;
7. guards showing each conjunct — values, trace, final `pasrel`, `paext` — is
   load-bearing;
8. only then re-adjudicate the nominal right-identity counterexample.

That last step matters and should not be anticipated. The allocator-name problem
is repaired, but the administrative stored-`post` difference between `qext` and
`qprod` is a **separate** problem, so right identity should not be expected to
come back automatically under an allocation-aware nominal observation.

Stop conditions: paired convergence cannot carry a unique final state; the
public specialisation cannot be derived from today's general theorem; or
introducing the well-formed domain makes the positive non-diagonal fixture
vacuous.

#### The observation gate: a paired-configuration simulation

> The allocation-aware finite-run theorem induces a one-directional
> observational simulation on explicitly related pairs of initial
> configurations. It preserves related result values, exact trace order and
> multiplicity, final store realization, and allocator-respecting evolution of
> the relational state.

And, of equal standing:

> This is a paired-configuration observation theorem, not yet a closed public
> observational equivalence.

`lemma_paobs_le_cf_of_pacfrel` derives it from `lemma_parun_compat` alone — no
second induction, no re-proof of the step cases. It is **soundness in one
direction**. Recovering relatedness from observation — completeness — is neither
proved nor the present objective.

#### The final world is existentially quantified, and must be

What paired convergence carries uniquely is the **data**: the trace, both result
values, both final stores, and both final frontiers, the frontiers determined
separately by each side's own run. The final **state** is not unique, and that
is not a weakness — it follows from the world's list representation being
non-canonical. Checked independently of the gate: `[(0,0)]` and
`[(0,0); (0,0)]` are both `pwf_world`, decide every lookup identically, and
extend each other, while being different values.

A semantic identity could be recorded as mutual `pwext`, but no quotient is
constructed here and none is claimed.

#### `pb_apply_wb` is finally placed

After going unused by both the one-step and the finite-run relational
compatibility proofs, it is consumed exactly once: in showing that the
well-formed observation domain is **closed under running**. Its status is
settled — not a condition on relational compatibility of transitions, but a
boundary condition that forms the well-formed observation domain. It uses only
`pconf_ok`'s `pstate_wb` conjunct, and `pconf_wf`'s preservation across every
transition needs no `papply_wb` at all, so the final stores' freshness comes for
free. No use for it was manufactured; the proofs that do not need it still do
not mention it.

#### Four conjuncts, each shown irremovable

Each guard drops one conjunct and exhibits a pair the weakened relation then
admits and the intact relation rejects:

- **trace** — `"a1"` changed to `"zz"` with store, frontiers, handles and stack
  identical, so the unmutated `s'` satisfies everything else;
- **related values** — a left returning a handle against a right returning a
  payload, which no world relates;
- **final store realization** — a right running on an **empty** store while the
  returned handles are still related;
- **final `paext`** — a state whose world speaks a key **below** the starting
  frontier, which is the re-anchoring that `panchor` exists to prevent, read at
  the state index.

They show each conjunct cannot be removed. They do **not** establish that the
four are logically independent of one another, and that should not be read into
them.

The symmetric candidate `paobs_tr_eq_at` is only a definition. Neither direction
of symmetry, nor transitivity, nor any correspondence with contextual
equivalence is proved.

#### The central open point: the public form's store conjunct

This is not a footnote after the result. It is the gap:

> The non-store components of the public observation can be recovered, but store
> realization remains indexed by the allocation state. `panobs_tr_le_nosto`
> measures exactly the part that collapses back to the public form; it is an
> audit boundary, not the final public observation.

The public specialisation reproduces `pnobs_tr_le`'s three hypotheses verbatim,
and its trace equality, `pwf_world w`, `pwext w (panchor sto)` and
`pval_rel w x1 x2` verbatim. Only the store conjunct stays at the new index, and
the bridge that would lower it —

```text
pawf s /\ paxrel r s cx1 cx2 ==> pxrel r s.aw cx1 cx2
```

— is **refuted**. The obstruction is the narrowing itself, not a gap in a proof.
Confirmed independently: no lemma in the appended region concludes a full
`pnobs_tr_le`.

```text
explicitly related initial configurations
          │
          ▼  PROVED
allocation-aware observational simulation
          │
          ├─ value / trace / frontier evolution ── returns to the public form
          │
          └─ store realization ─────────────────── the allocation state remains
```

One correction to the plan: `padiag`'s `pawf` does **not** follow from
`lemma_panchor_bound` alone. `pawf` is `pwf_world` conjoined with `pwbound`, and
that lemma supplies only the second; `lemma_panchor_wf` supplies the first. That
was the whole of what the specialisation needed beyond the sketch.

#### Position

> Allocation-aware observational soundness is established for explicitly related
> initial configurations. The remaining obstacle to a closed public observation
> is exactly the initial and final store-realization discipline; every non-store
> component has already been recovered.

#### The public store-domain gate, before returning to the laws

1. build the canonical diagonal `pastate` from a shared public store and
   counter;
2. show it satisfies `pawf`;
3. settle the condition under which a well-formed public store is `pasrel`-
   related to **itself** at that state;
4. fold that condition into the public observation's starting domain;
5. check non-vacuity on both the empty store and a non-empty store the machine
   actually built;
6. derive a closed public observation theorem from the paired theorem;
7. pin down that its only difference from `panobs_tr_le_nosto` is the store
   conjunct;
8. only then re-adjudicate right identity under the allocation-aware and
   administrative observations.

Stop conditions: a machine-built non-empty store is not self-related; the anchor
and the counter do not mesh; self-relatedness of *all* stores has to be assumed
unchecked; or the public form can be closed only by dropping the store conjunct.

Step 8 stays fenced. The allocator-name problem is repaired, but the
administrative stored-`post` difference between `qext` and `qprod` is a separate
problem, and right identity must not be expected back automatically.

#### The public store-domain gate: closure is possible, and it is global

The gate closes, and the premise **can** be replaced — not merely implied, but
as an equivalence. What that costs is the gate's real content.

> Under the current store-uniform formulation, closing the premise over every
> initial store collapses it to relatedness at `pabot`, hence to the global
> notion. Retaining computations that legitimately name handles therefore
> requires the store-anchored form.

Nothing here proves that a closed general theorem is impossible. What is settled
is a **fork**:

- **`paobs_tr_le_pub_at b sto n0`** — closed *after fixing its provenance
  parameters*, and a store-indexed relative theorem. It can keep computations
  that legitimately own handles.
- **`paobs_tr_le_pub b`** — a single proposition uniform over every store. Its
  quantifier includes the empty store, so the premise collapses to
  `pacrel r pabot` and becomes global relatedness.

#### The evidence, in three steps

1. `pawf s <==> paext s pabot` — the bottom of the admissible allocation states.
   Its proof is `()`; verified independently.
2. Relatedness at every diagonal state is **equivalent** to `pacrel r pabot`.
   This is `lemma_padiag_hyp_iff_pabot`, a biconditional, not a conjecture. The
   engine is step 1 plus the family's existing monotonicity, which lifts the
   bottom instance to every `pawf` state; `pcl_mono` is consumed exactly there.
   `pabot` is in the family because the empty store is a store and
   `psfresh [] 0` holds.
3. The cost is structural. At `pabot.aw = []` **no** pair of handles is
   related — checked independently for arbitrary `i` and `j`, not just for the
   fixture — so the development's own non-diagonal pair and the handle-naming
   fixture both drop out of the global premise.

> The non-diagonal witness is not lost because of an accidental choice of names.
> Every handle relation is absent at the bottom world, so any pair whose
> relatedness depends on owned handles lies outside the store-uniform premise.

The anchored form is also **strictly more general**, machine-checked: a pair
related at a machine-built store's diagonal state fails at `pabot`.

#### What the two forms are for

The fork does not require discarding either side; it assigns them roles.

- **provenance-indexed, anchored laws** — the principal theorems, for general
  higher-order contexts, captured closures, and computations holding existing
  handles;
- **global laws at `pabot`** — a corollary and audit form, for top-level,
  handle-free closed programs.

This is the same shape as the earlier anchor-relative equivariance. Promoting
the global condition back to the primary notion would again exclude exactly the
legitimate handle capture that the work up to here was done to admit. So the
principal laws — right identity among them — should be adjudicated first on
`_pub_at`, with the `pabot` specialisation taken afterwards as a closed
corollary.

#### The starting domain was already in place

Three planned steps were already done, and the interesting one needed no new
condition: the canonical diagonal state, its `pawf`, and the store's
self-relation at it, whose hypothesis is the **existing**
`pstore_equivariant_at`. The gate machine-checked that the public form's
antecedent *is* that starting-domain condition, rather than assuming it.

Non-vacuity was measured on three stores separately: the empty store, `ce_sto`,
and a store `prun` actually built — three entries, one of them a **stored
handle** `PCtxDone (PCtxKey 1)`. A global store condition would reject the
third; the anchored condition admits it, which is what keeps the public form
from being empty in practice. And the condition is a real restriction:
`[(0, PCtxDone (PCtxKey 5))]` is not equivariant at its own anchor.

#### The residue between the two public forms

Exactly one store conjunct, and it returns — at the **new** index.
`panobs_tr_le_asto` is `panobs_tr_le_nosto` with `pasrel b.pb_rel s' s1' s2'`
put back, and it follows from the public form. Stated at the strength proved:

> It carries the additional allocation-indexed store conjunct that
> `panobs_tr_le_nosto` omits. No strictness relation between the two complete
> propositions is claimed.

What does not return is the old-index `psrel`; that bridge was refuted in the
previous gate. The two ends stay distinct: the **starting** store's
self-relation comes from the old side condition and is settled; the
**concluding** store conjunct stays at the allocation index.

#### Not proved

- that fixing the anchor per store preserves relativisation **in general** — a
  design reading from one worked example, not a theorem;
- any strictness between `panobs_tr_le_asto` and `panobs_tr_le_nosto`;
- symmetry, in any form — everything in this line is `le`;
- completeness, in either public form;
- the laws, the administrative observation, `qext`, `qprod`, `padm_*`, and the
  re-adjudication of right identity — untouched, the only mentions in the
  appended region being ledger comments saying so.

#### Position

> The public-observation gate does close, but its store-uniform closure is
> necessarily global in the present formulation. General handle-owning
> computations remain covered by the provenance-indexed, store-anchored family
> rather than by that global corollary.

#### Right identity, re-adjudicated at the allocation index

What survived is **not** a counterexample to the law. It is the midpoint
separation specimen that closed the earlier proof route.

> Allocation-aware indexing does not absorb the administrative difference in the
> stored `post`. At the post-prefix midpoint, the computations are related but
> the stores cannot be related at any candidate state by `pasrel`, because the
> `post` clause can always be instantiated at that state itself and the
> recursive computation relation has no `POp`/`PVar` case.

And immediately:

> This refutes the staged proof through a nominally related midpoint. It neither
> proves nor refutes the right-identity law itself.

#### Why narrowing cannot help

```text
paext s s
   │
   ▼
stored-post clause can be tested at s itself
   │
   ▼
pacomp_rel … (POp a f) (PVar x)
   │
   ▼
definitionally false at index 1
```

Both ends were checked independently of the gate. The bottom step is
**structural, not fixture-specific**: for *any* clause relation, *any* state and
*any* terms, `~(pacomp_rel r 1 s (POp a f) (PVar x))` holds with proof body
`()` — the relation's case analysis simply has no clause joining those two head
constructors. And `pwf_world s.aw ==> paext s s` is the reflexivity that keeps
the current state inside its own future domain.

So restricting the future-state domain to allocator-respecting extensions cannot
remove the current state from that domain. Removing it would cost reflexivity of
accessibility, which would be a different and worse problem for a Kripke
relation. **The route of fixing this obstruction by further adjusting
accessibility is closed.**

It was checked that the conclusion is unchanged when restricted to the narrowed
domain, and separately that the witness state's counters `(2, 1)` are the two
midpoint configurations' own `next` values and `paext`-accessible from the
diagonal start. The obstruction is not at a badly chosen world; it is at a state
the allocator actually reaches.

#### What did and did not move

The re-adjudication was a genuine test, not a formality:

- **`xapply` satisfies the allocation-aware apply condition** — non-trivially,
  since the old condition does not imply the new one in general; it goes through
  because `xapply`'s single clause reads its continuation at the very state it
  stands at. So `xaboundary` exists with only `pb_apply_eq` new.
- **The transposition is faithful.** Both sides are those of
  `law_right_identity_ext_nom`, verbatim, with only the observation changed;
  the `fun cy -> ops.o_extend pl cy g` shape was already in the nominal form
  and is not introduced here. Verified by
  direct comparison. Making `sto` and `n0` indices rather than internal
  quantifiers is a change of granularity, and closing over them recovers the
  store-uniform form in both directions.
- **The domain checks pass, so nothing here is vacuous.**
  `pstore_equivariant_at` for both midpoint stores; `pconf_ok` for both
  configurations, carried along the run rather than hand-computed; `pastart_dom` at the law's start point and at
  both midpoints; and the observation's antecedent **satisfied**, not absent.
- **The name repair did not dissolve this administrative stored-`post`
  obstruction.** That is the accurate statement — not that the repair achieved
  nothing. It did resolve allocator identity, future-world factorisation, and
  compatibility through the dispatcher, finite runs and observation. What today
  establishes is that those results and this constructor mismatch are
  **orthogonal**.

> The midpoint obstruction survives inside the allocation-aware boundary
> discipline; it is not manufactured by excluding the interpreter or by making
> the law's antecedent empty.

#### The status of the law itself

Unchanged, and this must not be overstated. The positive result is a single
point — `k = []`, `sto = []`, `n0 = 0` — where antecedent and consequent hold
together. That is a **non-vacuous instance**, not a partial proof: the law
quantifies over `k`, and no quantification was discharged.

Neither the naive symmetrisation's refutation nor the joinability line moves;
today's result feeds into neither, and neither was attempted.

One argument, recorded as an argument: at the nominal index the administrative
relations `padm_xrel` and `padm_srel` *do* relate the specimen. So the midpoint
is already filled on the `padm` side; what is unfilled is the `pacrel`/`pasrel`
side, and today proves only that the latter stays unfilled at the allocation
index. Whether the `padm` side survives under `paext` is untouched.

#### Position

> The allocator-aware repair has done its job, but that job is orthogonal to
> administrative congruence. The remaining midpoint obstruction is
> constructor-level, is exposed by reflexivity at every admissible state, and
> must be addressed by an administrative relation rather than by further
> narrowing accessibility.

#### The next gate: an allocation-aware administrative relation

`padm_*` should not simply be cited at the new index. Build and test it:

1. juxtapose a `paext`-indexed computation-level administrative relation;
2. relate `(qext, qprod)` in the direction required;
3. still refuse constructor mismatches other than `POp c PVar` against `c`;
4. port the negative fixtures — a performing `post`, a `post` that discards its
   argument, a different residual;
5. lift to contexts and stores, and relate the midpoint `qmid_sl`/`qmid_sr`;
6. define the one-directional administrative observation matching `_pub_at`;
7. check whether right identity's consequent is recovered at the same single
   point;
8. only then move to one-step and finite-run preservation.

Stop conditions: relating `qext`/`qprod` also relates an existing negative
fixture; monotonicity along `paext` fails; or composing states and worlds
reopens the earlier joinability problem.

#### The administrative relation: it reaches, it does not carry

> The allocation-aware administrative relation has the intended local
> discriminating power: it relates `qext` to `qprod` at the reachable midpoint,
> remains directional, and continues to reject all six negative specimens. But
> no theorem yet transports this relatedness through machine execution, so it
> does not yet induce an administrative observation or establish a law.

And of equal standing:

> The positive endpoint instance is inherited through `pasrel`; the
> administrative relaxation contributes nothing there. Its demonstrated benefit
> is confined to the midpoint, and the missing transport theorem is what would
> have to connect that midpoint fact to an observation.

```text
start
  │
  │ ordinary allocation-aware execution
  ▼
midpoint
  │  padma_srel relates qmid_sl to qmid_sr   ← filled for the first time
  │
  │ administrative transport                 ← not proved
  ▼
end
  │  pasrel already suffices                 ← not a return on the relaxation
  ▼
one positive observation instance
```

#### The negative specimens first

All six are still refused, every one a **direct port** — no new proof needed,
none unportable: a changed `post`, a `post` that performs, a changed residual, a
changed answer, the store-level changed residual, and the reverse specimen. A
store-level mirror of the last was added as well. The world-indexed inversion
lemmas already had allocation-indexed counterparts in the file, so only the
reflexivity step had to be replaced.

This is a fact **at the level of the relation**: those six are refused by
`padma_*`. It is not a claim that they are observationally distinguishable, nor
that any execution separates them.

#### The relaxation is confined, and it is real

Two definitional facts, checked independently of the gate, with proof body `()`
in each case:

- with a `PVar` on the left the administrative relation **coincides** with
  `pacomp_rel`;
- a left-hand `PVar` is never administratively related to a right-hand `POp`.

So the accurate description is not "the relation was loosened" but:

> a one-directional rule was added that strips an administrative `POp _ PVar`
> from the head of the left-hand side.

The general form is proved in the file — for any head other than `POp` the strip
disjunct is `False`, so the administrative relation *is* the plain one there.
And the strip disjunct is non-vacuous, so the six refusals are not the refusals
of an empty relation.

#### Faithfulness

Compared directly against `padm_pcomp`: the differences are exactly the three
permitted kinds — the name prefix, `w` becoming `s.aw`, and the future
quantifier `pwf_world w' /\ pwext w' w` becoming `paext s' s`, with
`pcomp_rel`/`pframes_rel` becoming `pacomp_rel`/`paframes_rel`. The measure
`(decreases n)` and the `{:pattern}` are carried over unchanged. The
administrative observation is outside those three kinds and is marked as a new
definition rather than a copy: it is `paobs_tr_le_pub_at` with the final store
conjunct alone changed from `pasrel` to `padma_srel`.

#### Not proved

- **No transport.** There is not one lemma carrying `padma_srel` across a
  transition, so the midpoint result does not compose into an observation.
- Monotonicity of `padma_*` along `paext` — not needed by any guard here, since
  none transports a state, and not claimed.
- Transitivity, joinability, confluence, normal forms.
- `paobs_tr_le_pub_adm_at xaboundary [] 0 qlhs qrhs` itself: the law quantifies
  over `k`, and what was shown is its body at one `k`.
- The law, in either direction; no administrative form of it was even stated.

#### Position

> The missing relation is now present at exactly the configuration where it was
> needed. The remaining problem is no longer how to relate the midpoint, but how
> to soundly transport that relation through unequal administrative execution
> lengths.

#### The next gate: two kinds of monotonicity, and a weak simulation

Monotonicity must be split, and the goal must **not** be written as the simple
"`padma_srel` is monotone":

- the recursive semantic relations — `padma_pcomp`, contexts, frames — are
  expected to be Kripke-monotone along `paext`; failure there is a stop
  condition;
- `padma_srel` is **store realization**, and monotonicity of two fixed stores
  under a growing state should *not* be expected. As with `pasrel`, a new
  world's obligations have to come with an actual store allocation.

Transport is also unlikely to close as an ordinary one-step lockstep. A
left-hand administrative unit disappears over several silent steps on the left
against zero or few on the right — the earlier `PBindF` specimen already showed
the two sides taking different numbers of steps to reconverge. What is probably
needed is:

> An administrative weak simulation: one machine step or a finite silent
> administrative burst on one side is matched by zero or more steps on the
> other, preserving trace, allocation state, and administrative store
> realization at reconvergence.

1. `paext` monotonicity for the recursive `padma_*` family;
2. inclusion from `pacrel`/`paxrel`/`pasrel` into the corresponding `padma_*`;
3. a local lemma that an administrative strip changes neither trace, store nor
   counter, and reconverges in finitely many steps;
4. a concrete execution where the `post` of `qext`/`qprod` actually fires,
   reconverging to a common configuration from unequal step counts;
5. separate the non-allocating administrative burst from ordinary transitions
   that really allocate;
6. assemble those into a weak one-step simulation;
7. lift to finite runs and to the `_pub_at` administrative observation;
8. only then re-adjudicate right identity.

Stop conditions: `paext` monotonicity fails for the recursive family; an
administrative burst changes the trace, the store or a counter; or finite
reconvergence needs an extra unchecked condition on general interpreters.

#### Administrative monotonicity: two verdicts, as the split predicted

> The recursive allocation-aware administrative relations are Kripke-monotone
> along `paext`, with the same premise schema as the corresponding
> non-administrative family. Administrative store realization is not monotone
> under state growth with fixed stores, and should not be: a newly related name
> creates a new realization obligation that only an actual store allocation can
> satisfy.

The premise identity carries the same limitation as before:

> The premise schema is identical; the accessibility premise is the semantically
> narrower `paext`, not the old `pwext`.

Compared directly, not asserted:

```fstar
lemma_pacomp_rel_mono
  : requires pacomp_rel  r n s c1 c2 /\ paext s1 s /\ pcl_mono r
lemma_padma_pcomp_mono
  : requires padma_pcomp r n s c1 c2 /\ paext s1 s /\ pcl_mono r
```

No `pawf`, no `pbounded_world`, no per-closure side condition, and nothing
at all for the administrative disjunct. The anchored form is weaker still, needing only
`paext` and not `pcl_mono`. The measure is `decreases n` rather than the plain
family's lexicographic one, because `padma_pcomp` does not cross layers.
`lemma_paext_future_shrinks` was needed once per layer, as expected.

#### The two roles, kept apart

```text
recursive padma_* relations
        │
        └─ paext monotonicity                    PROVED

padma_srel (world satisfaction / store realization)
        │
        ├─ state grows, stores fixed             REFUTED
        └─ state grows with corresponding stores next gate
```

The refutation is stated with `pcl_mono` still in the hypotheses, so it is not a
missing side condition. Reproduced independently at the bottom state with empty
stores: `paalloc pabot` speaks `0 ↦ 0` and neither store has an entry for it.
The administrative strip plays no part — this is the same property that stops
`pasrel` and `psrel`.

`lemma_padma_srel_old_keys_mono` sharpens it, at exactly this strength:

> Existing world obligations survive the state extension; failure can arise only
> from obligations introduced by newly allocated name pairs.

#### The positive side is machine-checked

`guard_padma_mono_fires` is **PROVED** — it carries a proof body and passes
with the file. The gate's own report classified it as STATED; that was an
under-classification, corrected here. It matters because of what it contains:

- the transport is along a **strictly forward** `paext` —
  `~(paext qmid_as (paalloc qmid_as))` is proved, so this is not reflexivity
  read back;
- `padma_xrel` holds at both states while `paxrel` fails at both.

So monotonicity here is not a vacuous instance.

One ablation of the six, M3, failed with an F\* internal error (Error 276)
rather than a clean verification failure. It is recorded as **tool failure;
inconclusive** and is not counted as evidence. The other five are ordinary
failures and the proof status of every guard is unaffected.

#### Position

> Kripke transport of the recursive administrative relation is now available.
> What remains is operational transport: coupling non-allocating administrative
> control steps with ordinary execution, while coupling every genuine state
> extension with the actual allocations that make store realization true.

#### The next gate, and a scoping warning

"An administrative burst changes nothing" is **false as stated in general**. In

```fstar
POp c PVar
```

the inner `c` may emit, perform and allocate perfectly normally. What is
administrative is not `c`'s execution but the extra control wrapped around it:

```text
POp c PVar
   │  administrative decomposition
   ▼
c under PBindF PVar
   │  c may emit / perform / allocate normally
   ▼
value under PBindF PVar
   │  administrative discharge
   ▼
same value
```

So split the next gate in two:

1. the minimal specimen `POp (PVar x) PVar` against `PVar x` — reconverging to
   the same configuration from unequal step counts, with the extra steps
   themselves changing neither trace, store nor counter;
2. for general `c`, fix the shape that relates a left-hand intermediate phase
   carrying `PBindF PVar` to the right-hand ordinary execution.

Note that after the left's first step the two differ not only in the head of the
computation but in the **stack**. If `padma_pcomp` alone cannot express that
intermediate state, that is not a failure — it is the finding that an
allocation-aware administrative **stack or configuration** relation is needed.

Stop conditions: the minimal redex itself changes trace, store or a counter; the
extra `PBindF PVar` cannot be expressed even by the existing administrative
stack relation; when `c` allocates, ordinary `paalloc` and store growth cannot be
coupled to one successor state on both sides; or a general interpreter needs an
unchecked purity or linearity condition.

#### The minimal administrative redex is an exact stutter

> The minimal administrative redex is an exact operational stutter: for every
> interpreter, ambient stack, store, counter and value,
> `POp (PVar x) PVar` reaches `PVar x` in exactly two left steps against zero
> right steps, with empty trace and unchanged store and counter.

And of equal standing:

> This is the base administrative stutter, not a weak-simulation theorem for
> `POp c PVar` with arbitrary `c`.

The two sides do not merely *relate*; they reconverge to the **same
configuration**, given as an equality. The trace is `[]` as an equality, not a
bound. There are no hypotheses at all — no `requires`, every parameter
universally quantified. Re-derived independently with proof body `()`, so this
is not a consequence of the logical relation or of any boundary discipline: it is
the two transition rules of the machine, computed.

```text
PStep (POp (PVar x) PVar) k
   │  keep, no emission
   ▼
PStep (PVar x) (PBindF PVar :: k)
   │  keep, no emission
   ▼
PStep (PVar x) k              ← exactly the right-hand configuration
```

Claiming one step suffices is rejected, and the intermediate configuration
differs from both endpoints, so the detour is genuine rather than reflexivity
restated.

The witness runs with a non-empty store, a non-zero counter, and an ambient
stack `[PScopeF; PBoundaryF]`. That is worth stating precisely:

> The ambient stack may contain allocating frames, but those frames are not
> activated during the two administrative steps. This establishes parametricity
> in the surrounding configuration, not compatibility across an actual
> allocation.

The conclusion's final conjunct `0 + 2 == 2` is arithmetically trivial and
carries no information; it is noted here only because it appears in the
statement, and is not counted among the results.

#### Why this does not extend to general `c`

Not merely "because `c` is effectful". Three specific obligations appear, and
the third is the hard one:

- `emit` — both sides must produce the same trace;
- allocation — the two sides' state and store growth must be coupled;
- `perform` — the captured continuation segment may **include** the extra
  `PBindF PVar`.

That last one is decisive. The extra bind frame stops being mere control state
and becomes **data handed to the interpreter**. So the generalisation may need
more than an ordinary induction: an administrative stack relation, plus a
boundary discipline saying the interpreter preserves it.

#### The next gate: adjudicate the `perform` branch first

Before general `c`, settle the branch that could turn control into data.

1. formulate an allocation-aware administrative **configuration** relation
   joining the left intermediate `PStep c (PBindF PVar :: k)` to the right
   `PStep c k`;
2. show the extra frame disappears exactly at `PVar`;
3. show `PEmit` emits the same event while the frame is retained;
4. show the allocating rules can be coupled to the same `paalloc` and the same
   actual store growth;
5. adjudicate whether the two segments `PPerform` captures are joined by the
   administrative stack relation;
6. determine whether the interpreter needs an allocation-aware
   administrative-preservation condition;
7. if one is needed, pin it from both sides — `xapply` satisfies it, and an
   interpreter that reads frame length is refused;
8. only then move to a whole-dispatcher weak simulation.

**Failing to close the `perform` branch for a general interpreter is not by
itself a stop.** It would most likely be the rediscovery of a legitimate
boundary condition, in the same way `padm_apply_pres` was. It becomes a stop only if such
a condition cannot be met by an ordinary higher-order interpreter like `xapply`,
or if it has to be weakened until it admits one of the existing negative
specimens.

#### Position

> The machine's primitive administrative stutter is exact, silent and
> state-preserving. The remaining difficulty begins only when the enclosed
> computation runs: the extra identity frame must survive ordinary effects and
> allocation, and may become observable data when a continuation segment is
> captured.

#### The perform branch: erasure, forced

> The perform-side administrative stack relation is forced into an erasure
> shape: the existing fusion clause does not relate the captured segments, while
> deleting exactly one left-hand `PBindF PVar` does. Under `pakrel`, the two
> segments captured by the machine yield related `pkont_of` continuations,
> exposing a precise candidate preservation obligation for the interpreter
> boundary.

The refutation is machine-checked, and so is which conjunct fails:

```fstar
~(padm_stack r m sh 1 [] [PBindF PVar; PBindF PVar] [PBindF PVar])
```

The fusion clause discharges its fused frame with the plain `pframe_rel`, and
`pbind c f` is `POp c f`, so covering the case would need `POp (PVar x) g`
related to `g x` under a relation that has no such clause.

The surviving construction relates nothing to the extra frame; it **deletes**
it. `padx_stack` is `padm_stack`'s two `PBindF` disjuncts with the fusion one
replaced by deletion, and its `[]` clause is `False` because the left is longer
by exactly one frame.

At the strength established:

> Within the current administrative stack design, the fusion alternative is
> refuted on the perform specimen, and exact deletion of the left identity-bind
> frame is the surviving construction.

Not that every conceivable fusion relation is impossible.

And on the deletion's justification:

> The deletion is locally justified by the machine's `PBindF` rule and by the
> exact two-step stutter theorem. Its soundness across arbitrary execution and
> public observation remains the weak-simulation obligation.

What is proved is that erasure is the right *shape* — it fits the local rule,
the captured segments and the continuation construction. That a relation containing
it is observationally sound is not.

#### The relation does not merely shorten stacks

Four independent checks, three of them re-run here after the gate's own report
was lost:

- deletion is not for an arbitrary frame — the head must be `PBindF f` with
  `f == PVar` **syntactically**;
- a `PScopeF` head is not silently erased;
- two stacks of equal length are not accepted as "already erased";
- `pakrel` is load-bearing in the captured-segment lemma — dropping it fails.

So `padx_stack` is not "a relation that may shorten a stack at will". It erases
exactly one surplus identity-bind frame on the left.

#### The boundary condition, and its exact status

```text
pakrel captured segments
          │
          ▼  PROVED
related pkont_of continuations
          │
          ▼
padx_apply_pres — candidate boundary condition
          │
          ▼
interpreter outputs related             NOT YET INSTANTIATED
```

`lemma_padx_captured_segments_joined` needs only `pakrel r s cap1 cap2`. And the
condition is well localised: `lemma_padx_kont_fn_at` proves its hypothesis is
met by the pair the perform rule actually builds, so `padx_apply_pres` is not a
condition on arbitrary continuations but a preservation condition on the two
`pkont_of`s the two transitions hand over. That is the right localisation — it
does not make the condition stronger than the proof needs.

But **no interpreter has been shown to satisfy it**. `xapply` does not appear in
the appended region at all. Until one does, this is a candidate boundary
discipline, not an established one.

Steps 1–4 should be read the same way: not "the dispatcher's arms are proved",
but the local material a perform-arm proof will need is now in place — the
extra frame disappearing exactly at `PVar`, `PEmit` emitting the same event while the
frame is retained, and the allocating rule coupled to the same `paalloc` and the
same actual store growth.

#### Verification provenance

The gate's agent died to a network error (`ENOTFOUND`) immediately after its
single append and before reporting, so there is no agent report for this gate.
What counts as evidence here is: the full-file verification, re-run from a
cleared cache (exit 0, success line present, no error line, no warnings); the
append checked as 1,058 insertions and 0 deletions; and the three ablations
above, which were re-run directly. The gate's own ablation files remain in
scratch and were **not** confirmed to fail as intended; they are not counted.

#### Position

> The captured continuation mismatch now has an exact representation: erase one
> left identity-bind frame, relate the resulting segments, and require the
> interpreter to preserve the two machine-generated continuations. What remains
> is to show that this boundary condition is both inhabited by an ordinary
> interpreter and strong enough to carry the actual perform transition.

#### The next gate: boundary calibration only

1. prove `xapply` satisfies `padx_apply_pres`;
2. prove an interpreter that reads frame length — `xapply2` — does not;
3. show both satisfy the existing allocation-aware equivariance conditions, so
   that the administrative condition is what separates them;
4. read out that `xapply`'s output computations are related, using real captured
   segments joined by `pakrel` and their `pkont_of`s;
5. connect that to the actual `PPerform` step, or to a weak one-step
   compatibility;
6. construct an execution in which, with the condition dropped, `xapply2`
   observes the segment-length difference.

That last negative is what would settle `padx_apply_pres` as a genuinely
necessary semantic boundary condition rather than a proof convenience.

#### Boundary calibration: administrative preservation is a second discipline

> Administrative preservation is independent of nominal equivariance. Both
> `xapply` and the frame-counting `xapply2` respect the old and
> allocation-aware name disciplines, but only `xapply` preserves the
> administrative erasure. Without such a condition, `xapply2` turns one erased
> identity-bind frame into an observable difference in the final store.

The whole calibration sits in one lemma, so neither half can be read without the
other:

```fstar
guard_cal_separation ()
  : Lemma (papply_equivariant  fcl_rel xapply  /\
           papply_equivariant  fcl_rel xapply2 /\
           paapply_equivariant fcl_rel xapply  /\
           paapply_equivariant fcl_rel xapply2 /\
           padx_apply_pres     fcl_rel xapply  /\
           ~(padx_apply_pres   fcl_rel xapply2))
```

#### The mechanism, computed

```text
captured segment cap
        │
        ├─ pkont_of cap
        │      xklen = length cap
        │
        └─ pkont_of (PBindF PVar :: cap)
               xklen = length cap + 1
```

Verified independently for an arbitrary captured stack and value. `xklen` reads
**no name at all**, so equivariance cannot exclude it: `pacrel` matches stacks
frame for frame and therefore preserves the length, which is exactly why
`xapply2` passes both equivariance conditions; `padx_comp` erases one frame and
therefore does not.

Two orthogonal disciplines have now appeared, mechanically:

- the **nominal** discipline — do not let raw handle identity be observed;
- the **administrative** discipline — do not let meaningless control
  representation be observed.

#### What the sixth step proves, and what it does not

From the same two related configurations: `xapply2` halts in three steps on each
side, both traces empty, returning the **same handle** and the **same counter**,
yet with different residual stores; the two runs are literally unequal. Under
`xapply` the two runs are literally **equal** and both reach `PDone`.

Stated at the strength established:

> The experiment proves that an administrative-insensitivity requirement is
> semantically load-bearing for the intended equivalence. It does not prove that
> `padx_apply_pres` is the unique or logically weakest possible formulation of
> that requirement.

What is settled is three things: without a condition there is a concrete
counterexample; the existing equivariance conditions cannot exclude it; and
`padx_apply_pres` admits the ordinary `xapply` while rejecting the `xapply2`
that produces it. Minimality, uniqueness and general sufficiency are unproved.

Step 5 likewise:

> One concrete `PPerform` pair is weakly compatible under the calibrated
> interpreter. This is evidence that the boundary condition has the intended
> operational use, not a general theorem for the `PPerform` arm.

```text
old equivariance ───────┐
                        ├─ xapply   passes
new equivariance ───────┤
                        └─ xapply2  passes

padx_apply_pres ────────── xapply   passes
                           xapply2  fails
                                      │
                                      ▼
                          concrete final-store difference
```

#### Necessity and sufficiency, kept apart

| | status |
|---|---|
| the condition discriminates as needed | PROVED, by `xapply2` |
| the condition is inhabited | PROVED, by `xapply` |
| sufficient for the general `perform` arm | NOT PROVED |
| sufficient for the dispatcher, finite runs, observation | NOT PROVED |

Also unproved: any claim about interpreters other than these two; and step 6's
observation is one concrete execution, not a general theorem.

#### A methodological note

F\* stops checking a module after its first error, so a negative ablation must
be **one assertion per file** or later assertions are silently unchecked. The gate
caught this mid-run, re-measured, and ran a positive control first to show the
harness itself was sound. Nine ablations then failed as required. (The mutation
guards run alongside these gates have observed the same rule: expected-to-fail
assertions always in their own module, expected-to-pass ones grouped.)

#### Position

> The candidate boundary condition is now inhabited and semantically
> discriminating: it admits an ordinary higher-order interpreter and rejects a
> renaming-invariant interpreter that observes administrative frame structure.
> What remains open is its sufficiency for the general perform transition and,
> beyond that, for weak simulation.

#### The next gate: a general `PPerform`-arm theorem, condition as hypothesis

Do **not** admit the condition into the boundary record yet. Take it as an
explicit hypothesis and see whether the general arm closes on it alone.

1. leave the state, the two stores, the two stacks and the prompt-search result
   as variables;
2. obtain the captured segments' and `pkont_of`s' relation from
   `pakrel`/`padx_stack`;
3. consume `padx_apply_pres` exactly **once**, where the apply outputs are
   related;
4. carry trace, store, counter and allocation state in the conclusion together;
5. re-prove the concrete `xapply` fixture as a corollary of the general theorem;
6. show that dropping the condition specialises to the concrete `xapply2`
   counterexample and contradicts;
7. only if no further condition appears, admit it into the administrative
   boundary record;
8. then widen to the whole dispatcher.

Stop conditions: the general arm does not close on `padx_apply_pres` alone;
`xapply` cannot satisfy whatever extra condition appears; or the relation's
direction disagrees with the direction of the segments the machine hands over.

#### The parameterised diagonal `PPerform` arm

> For the diagonal prompt-search case, the `PPerform` arm closes with
> `padx_apply_pres` as the only additional interpreter-side assumption. The
> condition is consumed exactly once, at the point where the two `apply` outputs
> must be related; all other premises are existing relational, lookup and
> boundary obligations.

The word "only" is doing limited work:

> "Only" means no further condition on `apply`. It does not mean the theorem has
> no other premises: the relational hypotheses needed to discharge
> `padx_apply_pres` itself, together with the existing `pcl_down` and
> `plookup_equivariant` boundary conditions, remain necessary.

Two of the premises were not predicted, and both turn out to be the *remaining
conjuncts of `padx_apply_pres`'s own antecedent* — the clause and the payload
side, where only the continuation side had been discharged in advance. Going the
other way, `pakrel r s below below` was predicted and is **not** needed by the
arm: in the packaged form it is derived from one diagonal call of
`lemma_pafind_prompt_rel`, not assumed.

The single consumption point was checked directly: `padx_apply_pres_inst` occurs
five times in the appended region, of which **one** is a call and four are
comments. The condition is not in the boundary record.

#### Load-bearing in two distinct senses

- **Proof dependency** — dropping the condition from the general theorem, with
  the proof body otherwise unchanged, fails. Re-run independently.
- **Semantic dependency** — the condition-free statement, specialised to
  `xapply2`, yields the concrete counterexample and contradicts.

The first alone would only show the current proof uses it. The second is what
makes it more than a proof convenience. As before, no claim is made that
`padx_apply_pres` is the unique or weakest such formulation.

Eleven ablations were run, one assertion per file, including **two positive
controls**, so every one of the eight premises is shown non-redundant.

#### Dispatch changes the phase of the difference

```text
before PPerform
  extra PBindF PVar lives in the stack
             │
             │ capture + pkont_of + apply
             ▼
after PPerform
  administrative difference lives in the returned computation
```

> Capture changes the representation phase of the administrative difference.
> Before dispatch it is a removable stack frame; after dispatch it is
> computation data returned by the interpreter. `padxg_cf` records that
> generated phase, while `padx_cf` records the pre-capture stack phase.

So a new successor relation was not a convenience. Stated relative to the
present design:

> Under the current definitions, the successor cannot in general be recovered as
> `padx_cf`; the available conclusion is `padx_comp` inside the newly introduced
> `padxg_cf`.

Not that no other design could use a single relation.

#### The diagonal restriction, first among the open items

> `guard_padxg_one_search_serves_both` makes the restriction explicit: both
> sides use one prompt-search result. The theorem is general in its remaining
> parameters, but it is not yet the relational `PPerform` arm for two distinct,
> related searches and clauses.

Everything else is a variable — state, both stores, both counters, both
payloads, the ambient stack, the captured and remaining segments, the clause.
But the captured segment is literally the same list on both sides, with the left
carrying one extra frame on top; the found clause and the remainder are
**identical**, not related.

That restriction is why admitting the condition into the boundary record still
waits.

#### Also not proved

- other transition rules under `padxg_cf`;
- any statement about interpreters other than `xapply` and `xapply2`;
- admission into the administrative boundary record, or the whole dispatcher.

#### Position

> The candidate boundary condition is sufficient and load-bearing for the
> parameterised diagonal `PPerform` arm. Dispatch does not preserve the
> pre-capture configuration relation; it moves the simulation into a
> generated-computation phase, which must now be related operationally and
> generalised beyond the diagonal search.

#### Two gates before the record, not one

```text
padx_cf  ── PPerform ──▶  padxg_cf
   ▲                         │
   └──── reconvergence ──────┘
```

**Non-diagonal search.** Take each side's own `pfind_prompt` result; get the
correspondence of responder, payload and captured segment from
`plookup_equivariant` and the clause relation; join the two `pkont_of`s by
`padx_fn_at`; consume `padx_apply_pres` at the same single place; and re-derive
the diagonal theorem as a corollary.

**The generated phase.** State a one-step weak simulation for `padxg_cf`;
separate `padx_comp`'s plain branch from its strip branch; send the plain branch
to the existing allocation-aware step theorem; handle the strip branch's extra
bind push and pop as the weak step difference; couple allocation to the same
`paalloc` and the same actual store growth; and settle the condition under which
reconvergence returns from `padxg_cf` to `pacfrel` or `padx_cf`.

Only when both close is the simulation relation genuinely phase-indexed.

Stop conditions: the relation's direction inverts under a non-diagonal search; a
new interpreter-side condition beyond `padx_apply_pres` becomes necessary; or
the generated phase never reconverges and remains permanently in a separate phase.

#### The non-diagonal `PPerform` arm

> The allocation-aware administrative `PPerform` arm is now proved for two
> distinct, related prompt searches. The two searches agree on success versus
> failure; when they succeed, their clauses, payloads, captured segments and
> residual stacks provide exactly the premises needed to invoke
> `padx_apply_pres` once. No additional condition on the interpreter appears,
> and the earlier diagonal theorem is recovered as a corollary.

The hypothesis set went from eight to ten, and the difference is exactly: one
search became two, one `KScoped` exclusion became two, and the two diagonal
premises became non-diagonal. Nothing else. `padx_apply_pres_inst` occurs once
in non-comment code — checked directly.

#### Search agreement is derived, not assumed

> Search agreement is derived, not assumed: related source configurations cannot
> make one side find a prompt while the other fails. The theorem does not
> require the two successful search results to be equal; it transports their required
> relational components.

That answers the concern that assuming both searches succeed would smuggle in
their agreement. It does not.

#### The diagonal theorem is a specialisation, not a look-alike

> The diagonal theorem is a genuine specialisation of the non-diagonal theorem:
> its corollary has the same argument list and the same eight-premise `requires`
> block as the previous theorem, with no strengthened side condition.

Compared directly. The proof is one instantiation at `k,k` / `cap,cap` /
`below,below` / `fc,fc`.

#### The fixture is substantially non-diagonal

Four properties, verified independently of the gate:

- the world is `[(0,1)]` — an **aliasing** world, not the identity;
- the payload handles are `PCtxKey 0` and `PCtxKey 1`, different as values;
- the two source stacks are different as values;
- the left stack is **not** the right with one `PBindF PVar` pushed on top.

The last is what places it outside the previous gate's shape. `PParamF` is not a
prompt, so the search captures it, and the two captured segments differ while
having the same length. This is not the diagonal theorem with more variable
names.

#### What remains unmeasured, and what remains conditional

Two different kinds of gap, kept apart.

> The theorem itself allows distinct residual stacks and returns
> `pakrel r s b1 b2`. The concrete non-diagonal fixture uses the same residual
> list on both sides, so non-vacuity of that relational conclusion on unequal
> residuals remains unmeasured.

What is missing there is evidence, not quantification: the theorem is already
general in the residuals.

On interpreters, the position is:

- the theorem takes an arbitrary `apply` and holds under `padx_apply_pres`;
- the only interpreter proved to satisfy that condition is `xapply`;
- `xapply2` is concretely refused;
- no other concrete interpreter has been examined.

> No additional concrete interpreter is shown to inhabit the condition; the arm
> theorem itself remains conditional and interpreter-parametric.

Ablations: ten premises of the arm, five of the search lemma, and one on the
fixture's own `pakrel`, each in its own file, with three positive controls. No
premise is redundant.

#### Position

> The perform transition is no longer the missing relational arm: it is proved
> for genuinely non-diagonal searches under the calibrated boundary condition.
> The remaining gap is temporal — showing that the generated-computation phase
> weakly steps back into the stack-administrative phase.

#### The next gate: the generated phase

The decisive first move is translating `padx_comp`'s two branches into
execution form.

```text
padxg_cf
  ├─ plain pacrel branch
  │      one left step / one right step
  │      existing allocation-aware compatibility
  │
  └─ administrative strip branch
         one silent left decomposition / zero right steps
         extra PBindF PVar moves back into the stack
         successor should become padx_cf
```

If that closes, the phase transition becomes a cycle rather than a one-way move:

```text
padx_cf
   │ PPerform: capture turns frame into computation data
   ▼
padxg_cf
   │ administrative decomposition: computation data becomes frame
   ▼
padx_cf
```

1. an inversion lemma splitting `padx_comp` into plain and strip branches;
2. send the plain branch to the existing allocation-aware one-step theorem;
3. for the strip branch, one left step against zero right steps, empty trace,
   store and counter unchanged;
4. show that successor really is `padx_cf`;
5. on the plain branch, carry allocation through the same `paalloc` and the same
   actual store growth;
6. bundle both branches as a weak one-step theorem for `padxg_cf`;
7. connect to the non-diagonal perform theorem and run a concrete
   `padx_cf → padxg_cf → padx_cf` instance;
8. only then decide on admission into the boundary record.

Stop conditions: the strip branch's successor is not `padx_cf`; on the plain
branch `padma_srel` cannot be connected to ordinary store realization; or
representing zero steps on one side requires discarding trace or state
information.

#### The generated phase: one-step closure, and a witnessed cycle

> The generated-computation relation is closed under synchronized one-step
> execution: every `padxg_cf` pair takes one step on each side into either
> `padxg_cf`, `padx_cf`, or ordinary `pacfrel`, while preserving the appropriate
> trace, store, counter and allocation-state obligations. A concrete execution
> traverses `padx_cf → padxg_cf → padxg_cf → padx_cf`.

And immediately:

> This is phase-sensitive one-step closure, not yet a weak simulation in the
> usual zero-or-more-step sense. No multi-step theorem proves that every
> generated spine eventually exits, and the unequal-step identity-frame
> discharge is not included in this gate.

#### The `PSplice` correction

The gate was originally sketched with the strip branch as one left step against
zero right steps. That is wrong:

```text
PSplice left   ──1 step──▶ body under left frames
PSplice right  ──1 step──▶ body under right frames
```

The asymmetry is not in the number of transitions but in the **contents of the
spliced frame list**, and that is exactly why the successor lands back in
`padx_cf`: the surplus identity frame rides inside `fs1` and reappears on top of
the left's new stack. Verified generically before the gate ran — arbitrary
interpreter, frame lists, bodies, stacks, store and counter, proof body `()`.

A second correction, of attribution rather than of a proof. The 1:0 stutter that
does exist later is the **bind-pop half**:

> The later 1:0 stutter is the bind-pop half proved by `lemma_arx_step2`;
> `lemma_arx_reconverges` packages that step together with the earlier bind push
> into the complete 2:0 minimal-redex theorem.

The prototype's own ledger comments said `lemma_arx_reconverges` in both places;
both have been corrected in the file. No proof body was touched.

#### The ambient assumption was already there

The cycle's closing step needs `pakrel r s k1 k2` on the ambient remainder.
It is **not** an added hypothesis: `padxg_cf`'s state clause is literally

```fstar
| PStep c1 k1, PStep c2 k2 -> padx_comp r s c1 c2 /\ pakrel r s k1 k2
```

so the generated-phase relation already carries the conjunct its own closure
needs. The other side, `pakrel r s t1 fs2`, is derived from the `padx_ktop`
erasure in `padx_comp`'s `PSplice` clause, not assumed either.

The transparent wrappers folded into the bundled theorem for a clear reason:
they land at the **same** state with store and counter unchanged, so they are a
disjunct the bundled conclusion can carry. Only the plain branch needs the state
to move, and that is the only branch where it does.

#### The cycle's status, in three layers

- **general theorem** — one step from `padxg_cf` lands in one of the three
  relations;
- **general entry** — the non-diagonal `PPerform` arm gives
  `padx_cf → padxg_cf`;
- **concrete witness** — one `xapply` execution passes through a wrapper and a
  splice and returns to `padx_cf`.

"Every generated phase returns" is **not** proved. That the wrapper spine is
syntactically finite and that a finite-run theorem iterates over it are
different statements, and only the first is available.

The witness is not degenerate. Its middle step is a real wrapper traversal —
`xapply` returns `PEnterCtx xplan (kk …)`, so the spine is walked before the
erasure is reached — which means both disjuncts of the bundled theorem are
exercised.

And the cycle does not collapse:

> The cycle does not collapse into the ordinary relation: at the concrete exit
> the stacks differ by exactly one frame, so `pakrel` fails while `padx_cf`
> holds.

Verified independently by computing the two lengths. That is a fact about this
exit, not a general strictness claim about `padx_cf` against `pacfrel`.

#### `padma_srel` was not exercised

> The plain branch enters through `pacfrel`, whose `pasrel` realization is
> already sufficient. Consequently no `padma_srel` bridge is exercised in this
> gate. This is neither a failure nor a proof of such a bridge.

#### Also not proved

- the non-diagonal fixture was **not** lifted into `padxg_cf` — its store does
  not satisfy `pasrel` at that world. Non-diagonality is carried by the general
  theorem; the concrete cycle runs on the diagonal fixture;
- admission into the boundary record;
- any statement about interpreters other than `xapply`.

#### Position

> The generated phase is now locally closed and its entry-to-exit cycle is
> witnessed without collapsing to the ordinary relation. What remains is to turn
> this one-step phase graph into a finite closure theorem and then discharge the
> surviving identity frame with the first genuinely unequal-step transition.

#### The next gate: finite closure and the real stutter, kept apart

1. define the wrapper spine's height;
2. show `PEmit` and `PEnterCtx` each decrease it in one step;
3. show the spine's terminus gives `padx_cf` when it is a `PSplice` and
   `pacfrel` on the plain branch;
4. preserve the trace's order and multiplicity across the synchronized finite
   prefix;
5. re-prove the concrete cycle as a corollary of the finite closure theorem;
6. prove the genuine weak stutter at `padx_cf`'s value case — one left step
   against zero, via `lemma_arx_step2`;
7. compose generated closure with the identity-frame discharge;
8. only then decide admission into the administrative boundary record.

Stop conditions: the wrapper height does not decrease in one step; the trace
concatenation of `PEmit` puts the two sides out of step; or moving from the
post-`PSplice` `padx_cf` to the identity-frame discharge needs a new interpreter
condition.

#### Finite spine closure, and the first genuine 1:0 stutter

> The generated wrapper spine now has a finite closure theorem: from a spine of
> height *h*, both sides take exactly *h* synchronized steps, preserve store
> and counter, emit exactly the ordered event list computed by `gwv_evs`, and
> reach a height-zero terminal phase. This closes the previous "one-step
> closure does not imply eventual exit" gap.

The trace claim is about **order and multiplicity**, not length: `gwv_prefix`
gives list equality, and `gwv_prefix_evs` fixes *which* list — the one computed
from the spine's syntax, `PEmit` contributing a cons and `PEnterCtx` nothing. A
guard on a three-`PEmit` spine emits `["a"; "a"; "b"]` and refutes both a
reordering and a multiplicity change.

The two terminal cases went into **one** closure statement, and not merely as a
disjunction: the left computation's `PSplice?` discriminates them, so a caller
knows which exit was taken. The base case is not one-sided either — that a left
terminus forces a right terminus is proved separately.

#### The stutter, stated exactly

> `gwv_padx_value_stutter` is the first genuine 1:0 transition in the
> phase-sensitive development. Its only premise is the administrative
> configuration relation itself; value relatedness, the surplus `PBindF PVar`,
> and the relation between the remaining stacks are derived rather than assumed.

So it is **no additional premise**, not "no premise": `padx_cf r s cf1 cf2` is
needed and does the work. The two values may be unequal and need not be `PV`;
the ambient stacks are arbitrary and the right one may be empty. No interpreter
condition is required — the transition is `pstep_tr`'s `PBindF` rule, which
consults neither `apply` nor `lk`.

And it is the first genuine **1:0** in this line, not the first unequal-step
result: the 2:0 minimal-redex theorem came earlier. What is new is a stutter
inside the phase-sensitive development, landing in `pacfrel`.

Non-vacuity is carried by a refutation: before the step the pair is **not**
`pacfrel`, so 0:0 would discharge nothing, and the two configurations differ, so
the left really moves.

#### A correction to the gate's own account

> The concrete cycle uses `gwv_prefix` / `gwv_prefix_evs` not because `xapply`
> lacks allocation-aware equivariance — it has `lemma_xapply_paequivariant` —
> but because the prefix theorem deliberately requires less. The stronger
> hypotheses of `gwv_finite_closure` belong to its plain-terminal dispatcher
> branch.

`gwv_prefix`'s premises are `pcl_down`, the relation, and the height.
The routing choice was the better one; only the stated reason was wrong.

Step 5 is therefore met in substance: the cycle's two generated-phase
transitions now come from the prefix theorems rather than from hand-written step
calls. The entry `PPerform` transition still comes from the non-diagonal arm,
which is correct — that transition enters the generated phase rather than being
part of it.

#### Not proved

- the general composition of finite spine closure with the 1:0 value stutter;
- that an arbitrary `padx_cf` pair reaches the value-stutter point — shown
  on one concrete instance only;
- admission into the boundary record;
- any concrete inhabitant of the conditions other than `xapply`.

#### Position

The generated phase's temporal finiteness is settled. A weak simulation bundling
all phases is not: what remains is to determine under which conditions a finite
closure's terminus connects to the 1:0 stutter, and to compose the two.

#### The deep administrative phase: what composition actually needs

This gate did not compose the two halves. It found the shape of the invariant
that has to sit between them.

> `padx_cf` is not closed under machine steps. A genuine `POp` transition can
> move the surplus identity-bind frame below ordinary control frames, where the
> head-only `padx_ktop` relation no longer applies. The successor is not
> unrelated, but it requires a deep administrative phase relation.

The refutation runs on a working transition: the source pair is in `padx_cf`,
each side takes one `POp` step with an empty trace, and the successor pair is
proved **not** to be in `padx_cf`, with the failing conjunct named. The same
guard shows the successor **is** in the deep form, so what broke is the
head-only shape, not the phase. Checked independently and structurally: pushing
**any** non-identity bind frame on both sides makes `padx_top` fail at index 0.

#### A separate finding, about logical shape

> `padx_k` has the pointwise shape `forall n. A n \/ B n`; a step proof needs
> one stable phase choice outside the index quantifier. `gwy_k` supplies that
> stronger shape and is proved to refine `padx_k`.

Only the refinement `gwy_k ⟹ padx_k` is proved; no biconditional, so this is a
**strengthening**, not a reformulation and not an equivalence. The reason a new
relation was needed at all is that the index quantifier and the disjunction do
not commute, and the inversion would require an index-downward-closure lemma for
the `paframes_rel` family which does not exist in the development.

`gwy_dichotomy` names the two exits at a value — surplus on top, or two related
head frames with the surplus still buried. Both horns have a lemma and a worked
instance, so the dichotomy is non-vacuous rather than a definitional flourish:
"a value always stutters" is false, and the guard exhibits a value pair where
the top-frame form is refuted and the step is lockstep instead.

#### The one-step theorem's status

> The resulting one-step theorem is a theorem over a proper subset of transition
> forms, not a dispatcher theorem and not yet a weak simulation.

Proved:

- lockstep for exactly five node kinds — `gwy_lockstep_node` is
  `PEmit? || POp? || PSplice? || PHandle? || PNewP?`;
- the value case with the surplus **on top** — the 1:0 stutter into `pacfrel`;
- `PPerform` with the surplus **on top** — into `padxg_cf`, reusing the
  non-diagonal arm.

Not attempted:

- **`PPerform` at depth.** This is not a to-do item: it is the gate's first stop
  condition actually firing. When the surplus is buried, `pfind_prompt` puts it
  either into the captured segment or into the remainder below, and no arm in
  the development covers either;
- `PVar` meeting `PScopeF`, `PBoundaryF`, `PSiteF`, `PParamF`, `PModeF` or
  `PPromptF` — the first two **allocate**, so the state must move to
  `paalloc s`; the next two search the very tail the surplus sits in;
- `PReadP`, `PWriteP`, `PWeave`, `PEnterCtx`, `PExtendC`, `PExtendCtxC`,
  `PResumeC`;
- the index-downward-closure lemma itself.

#### Why the dispatcher theorem could not be reused

That is a result, not a shortfall of proof engineering. `lemma_pastep_tr_compat`
concludes through `pacfrel`, whose stack conjunct is `pakrel` — exactly what
the deep form does not supply. No substitute was invented; the lockstep case was
closed directly from the `pacrel` inversion lemmas plus new cons and append
lemmas for the deep relation. That is the right handling.

#### Position

The simple picture — finite closure exits, then the frame is immediately
discharged — is refuted. What sits between them is a deep administrative phase
relation, and this gate fixed both its necessity and its logical form.

#### The order from here

Not straight back to composition:

1. the index-downward-closure lemma for the `paframes_rel` family;
2. `PPerform` at depth;
3. the allocating `PVar` cases — floor, boundary, site;
4. the tail-searching cases — mode and prompt;
5. the remaining computation constructors;
6. an exhaustive one-step theorem for the whole dispatcher at the deep phase;
7. only then compose finite closure, the deep phase and the 1:0 stutter.

#### Index-downward closure, and the inversion it pays for

This updates the previous section's account of `gwy_k`.

> Under `pcl_down r`, `padx_k` and `gwy_k` are equivalent. The earlier
> unconditional refinement `gwy_k ==> padx_k` remains valid; this gate adds the
> converse only under the load-bearing downward-closure premise.

So "the same relation, differently presented" holds **under `pcl_down r`**,
not unconditionally. The premise is load-bearing in the equivalence itself,
not only in the closure lemmas it is assembled from: restating the equivalence
without it, with the proof body unchanged, fails. Checked independently.

The stop condition that would have mattered — that the two are genuinely
different relations, leaving the one-way refinement as the best available — did
not fire.

#### The closure, and where its premise enters

Downward closure from index `n + 1` to `n`, for the seven members of the
allocation-indexed family, needs **only `pcl_down r`**: no `pawf`, no
`pcl_mono`, no `plookup_equivariant`. And it enters at exactly five sites, all
of them `ptable_rel` occurrences — `PHandle`, `POwner`, `PPromptF`,
`PITransparent`, `PIReenter` — because `ptable_rel` is the family's only member
that is not trivial at index 0. An ablation confirms it: without `pcl_down`,
exactly the four table-touching lemmas fail and the other five still
verify.

One member had to be added: `gwd_pafn_down`, measure `%[n; 0; 1]`, carrying
the index drop under a closure's future quantifier. It slots between the
computation level and the owner/frame/item levels, so the lexicographic order
is undisturbed.

The **world-indexed** family `pcomp_rel` / `pframes_rel` still has no downward
closure. None was added; `padx_stack` uses the allocation-indexed family, so it
was not needed.

#### What the classical step costs

> The proof uses the ambient classical reasoning available to SMT through
> `eliminate (p \/ ~p)`, but adds no new trusted axiom, `assume`, explicit
> excluded-middle dependency, or module import.

`FStar.StrongExcludedMiddle` is neither opened nor used — the appended region
contains no occurrence. So the trust surface does not grow. But the proof is not
thereby constructive, and it is **not** an algorithm computing the stable horn:
it establishes that one exists.

#### Reading the varying-horn guard

The worked stack — `[PBindF PVar; PScopeF; PBindF PVar]` against
`[PScopeF; PBindF PVar]` — has its second disjunct hold at index 0 and fail at
index 1, while the first holds throughout.

> Pointwise witnesses may switch horns with the index, even though downward
> closure guarantees that some stable global horn exists. The stronger
> crossing-failure specimen cannot exist; that diagnosis is stated from the
> proved closure facts but is not packaged as a separate theorem.

That non-existence keeps its **STATED** status: each horn's failure persists
upwards, so two failures would collide at the maximum — an argument read off
the closure results, not a theorem in the file.

#### Position

The previous gate's logical obstruction is cleared. For the deep `PPerform`
work, `gwy_k` can now be used not as a new semantic relation but as `padx_k`'s
invertible normal form — under `pcl_down`.

#### Deep `PPerform`: the capture position splits the discipline

> Deep `PPerform` splits into two exhaustive capture cases. When the surplus
> identity frame enters the captured continuation, the generated computation
> requires a deep administrative relation and the new condition
> `gwe_apply_pres`. When the surplus remains in the residual stack, the
> successor stays in the deep stack phase and no administrative apply
> condition is consumed.

`pfind_prompt` conses every non-prompt frame onto the captured segment and stops
at a matching prompt, so a buried surplus goes to exactly one of two places:

| | surplus lands in | relations obtained | condition consumed |
|---|---|---|---|
| A | the captured segment | `gwy_k cap1 cap2` and `pakrel bel1 bel2` | the deep administrative one |
| B | the residual | `pakrel cap1 cap2` and `gwy_k bel1 bel2` | ordinary equivariance only |

Case B's statement contains **no** occurrence of `padx_apply_pres` — checked
directly. That is the localisation: the administrative discipline is needed only
where the frame is actually captured.

#### What the paired ablations do and do not show

> The paired ablations establish dependency of the present proof paths: the
> top-only condition cannot replace `gwe_apply_pres` in case A, and adding an
> administrative condition does not repair the wrong treatment of case B. They
> do not yet prove logical independence or minimality of the conditions.

Eighteen ablations fired, one assertion per file, with positive controls.

#### Case A needed a deeper relation, and got one without damage

The prediction held: `padx_comp`'s `PSplice` clause is head-only, so a surplus
buried *inside* the captured segment escapes it — refuted on the shipping
fixture. `gwe_comp` changes **that one clause** (`padx_ktop` → `gwy_k`) and
nothing else, and the containments `padx_comp ==> gwe_comp` and
`padxg_cf ==> gwe_cfg` show it is a genuine coarsening, so nothing already
proved is disturbed.

#### Three roles, not a final count of three

The candidate interface has divided into three roles, which is not the same as
having established that three are needed:

- `paapply_equivariant` — ordinary name- and allocation-aware preservation;
- `padx_apply_pres` — capture of a surplus identity frame **at the head**;
- `gwe_apply_pres` — capture of one **buried at depth**.

> `xapply` inhabits all three, while `xapply2` inhabits only ordinary
> allocation-aware equivariance. Thus the deep condition is not a restatement of
> ordinary equivariance. No implication between the two administrative
> conditions has been proved in either direction.

The separation by `xapply2` was reproduced independently.

#### The successor disjunction

> The theorem ends in `gwe_cfg \/ gwy_cf`. This is not yet one simulation
> invariant: the capture-inside case moves the administrative difference into
> generated computation, while the capture-below case leaves it in the stack. No
> closure theorem for their union is proved.

The disjunction is a limitation and an honest reading of the machine's phase
structure at once.

#### Not proved

- the case where both searches fail;
- deep transitions other than `PPerform`;
- closure or unification of `gwe_cfg` and `gwy_cf`;
- any implication between the two administrative conditions;
- admission into the boundary record;
- composition with finite runs or observation.

#### Position

The stop condition that fired here was not a breakdown. It was the discovery
that a single deep relation cannot express the difference in capture position,
and the gate closed by refining into two exhaustive cases. The next step is not
to collapse the successor disjunction into one definition, but to adjudicate
one-step closure on the `gwe_cfg` side first.

#### The deep generated phase closes, and returns to `gwy_cf`

> The deep generated-computation phase has the same finite wrapper-spine
> discipline as the head-only phase. Its wrappers advance in synchronized
> lockstep, preserve store and counter, preserve the complete event list, and
> its `PSplice` terminus returns the pair to `gwy_cf`.

Only one thing had to be newly proved. The wrappers lifted unchanged: `PEmit`
reproduces the two stacks verbatim, so the ordinary half of the relation carries
over; `PEnterCtx` pushes frames that are all ordinarily related, so the ordinary
append suffices; and the fallthrough is literally `pacrel`, so the existing
one-step compatibility applies directly.

```text
gwe_cfg ──generated wrappers* / PSplice──▶ gwy_cf
```

That is a finite phase transition from one to the other, **not** a
unification of `gwe_cfg` and `gwy_cf`. The new edge is not a restatement of
the existing `padxg_cf -> padx_cf`: on the shipping fixture with the surplus
genuinely at depth, the successor is refuted for `padx_cf`.

#### The append lemma's asymmetry is about the frame's position

> The append proof is not the mirror image of ordinary related-stack append.
> Recursion stops when it reaches the surplus identity-frame branch; from that
> point the remaining suffix is discharged by the ordinary relation.
> Reversing the two arguments would move the distinguished surplus to the
> wrong side, and is refuted by a pair satisfying `gwy_k` but not `pakrel`.

Checked independently: `[PBindF PVar]` against `[]` satisfies `gwy_k` and not
`pakrel`, so the existing `gwy_k_append` — ordinary prefix, deep suffix —
cannot do this job. The new lemma needs only its two hypotheses; no
`pcl_down`, no `pawf`.

This says the two orientations are not interchangeable **for the present
oriented relation**, not that a reversed lemma is impossible in general.

#### Trace agreement is unconditional

> `gwf_step_out` factors trace equality outside the three successor
> alternatives. Therefore trace agreement is unconditional across the step
> theorem; it is not recovered separately after learning which phase exit was
> taken.

Confirmed by reading the predicate: the equality is its first conjunct, and the
disjunction of the three exits follows it.

#### The finite closure, at its actual scope

The height machinery was **checked**, not assumed, to lift: `gwv_h` never
inspects a `PSplice`'s frames, and `gwe_comp` differs from `padx_comp` only
inside that clause, so the two induce the same spines: `gwe_comp` admits no
spine that `padx_comp` does not.

The finite closure came with it. Two properties are worth naming: the right
side's height being equal is **derived from the relation**, not assumed; and the
trace claim is list equality, so order and multiplicity, not length. Its scope
is the `gwe_cfg` wrapper spine — not a finite closure for any weak simulation.

#### Ablations

Two, of unequal strength, and the weaker one is recorded as such:

> `needs_deep_prefix` confirms a necessary shape invariant — `gwy_k` requires a
> nonempty left stack — but it does not independently exercise the semantic
> contents of the deep-prefix relation.

The other, dropping the ordinary suffix, is substantive: it walks past the
surplus and collapses on a shape mismatch.

#### Not proved

- the one-step theorem's three exits are not unified;
- no two-step composition — whether a `gwy_cf` successor can be stepped again
  is not shown;
- deep `PPerform` is not handled by this closure theorem; it is reached only
  through the fallthrough where `gwe_comp` degenerates to `pacrel`, so nothing
  here depends on the previous gate's unclaimed mutual
  exclusivity;
- other deep transition forms, the boundary record, and observation.

#### Position

The next step is not to generalise `gwe_cfg` further. It is to complete
dispatcher coverage for `gwy_cf`, the phase this one returns to. The first
substantive test there is the allocating `PVar` branch, which measures whether
the deep relation and `paalloc` are preserved together.

#### Deep `PVar`: the difference reaches a stored residual

Most of the `PVar` branch closed. The result that matters is narrower and worse:
this is the first path on which the administrative difference leaves the stack
and lands in a **stored residual context**.

A prediction of this gate's brief was wrong and is corrected here:

> The `PScopeF` branch did require Kripke transport, but not a new monotonicity
> theorem: `gwe_k_mono` already supplied exactly the needed result. The correct
> action was reuse through a thin wrapper.

#### `PScopeF` carries the deep relation across an allocation

Three things together, so the state change is not a formal re-indexing:

- the **actual** `palloc` result is used, not a reconstructed key;
- `paprov_step_at` retains the allocation's provenance;
- the pair lands in `gwy_cf r (paalloc s)`, and the reverse `paext` is refuted.

Beyond `gwy_cf` itself the only premise is `pcl_mono r`.

#### The asymmetry is about persistence, not about seeing

> Both `pfind_mode` and `pcut_scope` traverse `PBindF` without branching on it.
> The difference is in their outputs: `pfind_mode` discards that traversal
> detail, whereas `pcut_scope` accumulates the traversed frame into `above`,
> which is subsequently stored as a residual context.

So `pfind_mode` lifts with **no case split at all** — its hypothesis is `gwy_k`
alone and its conclusion is the existing lemma verbatim, a clean contrast with
the perform arm. The problem is not that `pcut_scope` distinguishes the frame;
it is that it **persists** what it traversed.

```text
deep stack difference
        │ pcut_scope
        ▼
stored residual-context difference
```

That is the same shape as `PPerform` moving a stack difference into a generated
computation, but the landing site is different — and this one has no landing
site at all:

> Within the current relation architecture, the cut-inside horn has no target
> phase: ordinary `pactx_rel` rejects the residual-length difference, and
> neither a deep context relation nor its store-realisation lifting currently
> exists.

Verified independently, and the failure is robust: at index 1, `pactx_rel`
rejects `PCtxRequests u [PBoundaryF; PBindF PVar] PVar` against
`PCtxRequests u [PBoundaryF] PVar` for **any** state. No choice of world or
allocation frontier repairs it. The obstruction is in the residual's frame
structure, not in names.

#### The covered branch is conditional

> `gwp_cut_below` is assumed positively. No exclusivity theorem proves that it
> is the negation of the cut-inside horn, so the covered branch is conditional
> and the complete cut dichotomy remains STATED.

#### `gwp_cf` is a local widening, not a unification

The landing relation was widened once, by a `PPaused` clause, because `PPaused`
is a real terminal form that `gwy_cf`'s `PStep`-only state clause cannot admit.
That is accommodation of an existing shape, not a step toward one dispatcher
invariant.

#### What did close

Eleven head-frame exits, tabulated in the file. `PParamF` and `PModeF` pop with
no premise beyond the relation; `PSiteF`'s `MExtend` exit and the responder exit
of `PBoundaryF` likewise leave the state alone; `PPromptF` needs `pcl_down`;
`PScopeF` is the one that moves the state. The bundled theorem **cites** the
stutter horn and the `PBindF` horn rather than re-proving them.

Seven ablations, one premise per file, all fired, after a positive control.

#### Not proved

- the cut-inside horn — it lands in no phase in the development;
- exclusivity of the two cut horns;
- the remaining computation forms — `PReadP`, `PWriteP`, `PWeave`, `PEnterCtx`,
  `PExtendC`, `PExtendCtxC`, `PResumeC`;
- unification of the phases, composition, the boundary record.

#### The order from here

Not the remaining constructors — the stored-residual phase first:

1. a context relation deepened in the **residual** only;
2. today's specimen related by it;
3. the existing semantically-different residual negatives still refused;
4. the lifting to a store relation;
5. preservation of allocation and store realisation;
6. a landing site for the cut-inside horn;
7. only then resume dispatcher coverage.

The gate's finding is that the deep `PVar` obstruction is not in the search but
at the boundary where a cut result is persisted.

#### The stored-residual phase exists, and is not yet wired to the machine

> A residual-deepened context and store relation now admits exactly the
> administrative residual specimen that ordinary `pactx_rel` / `pasrel` reject,
> while preserving the existing negative specimens. The missing semantic landing
> phase has been constructed; its operational connection to `pstep_tr` has not.

The horn that the previous gate recorded as landing in **no phase** now has one.

#### The change is local

> The context relation is changed only at the residual-frame component of
> `PCtxRequests`; payload, stored post, and all other context structure remain
> under the existing relations.

```fstar
let gwr_resid r n s rs1 rs2 = paframes_rel r n s rs1 rs2 \/ gwy_k r s rs1 rs2
```

Keeping the matching disjunct intact makes the layer a genuine **coarsening** of
`pactx_rel`, so every pair the shipped relation accepted is still accepted and
the existing positive fixtures transport for free. That locality is also why all
three residual negatives could be re-proved **without changing a character** of
their proofs.

The alternative — replacing the matching conjunct with `pakrel` — was rejected
with a reason worth keeping: `pakrel` is *stronger* than what it would replace,
so the layer would become **incomparable** with `pactx_rel` and would lose
positive instances for reasons unrelated to the hole being filled.

#### The bound on the coarsening, credited in two parts

> The equal-length biconditional proves that no new equal-length residual pair
> is admitted. The one-frame bound on unequal pairs is a separate shape fact
> and should be credited separately.

Both halves are in the file, and they are different theorems:

- at equal lengths the layer **coincides** with the shipped relation —
  `gwr_resid <==> paframes_rel`, verified independently here;
- the deep disjunct forces the left to be longer by exactly one —
  `gwr_gwy_k_length`.

Their conjunction — "equal, or the left exactly one longer" — is **not packaged
as a single lemma**, and one caveat belongs with it: at index 0 the matching
conjunct is vacuously true, so nothing is forced there. That is inherited from
`pactx_rel`, which is also `True` at index 0, so it is not new coarsening; but
the bound should be read as applying from index 1.

#### Store lifting and allocation

The store relation copies `pasrel` verbatim with only `paxrel` replaced, keeping
the `{:pattern}` discipline, and the allocation lemma matches
`lemma_pasrel_alloc`'s conclusion structure — the actual `palloc` result, the
`pwextend`, the frontier increment.

Identical structure is **not** a regression to `pasrel`. The concrete horn is
exactly where they differ: the guard proves the new store relation holds at
`paalloc pabot` where `pasrel` does not.

#### Where this leaves the phase graph

```text
cut-inside residual
        │
        ▼
gwr context/store relation     PROVED
        │
        ▼
pstep_tr / gwp_step_at         NOT CONNECTED
```

#### Not proved

- a configuration relation carrying `gwr_srel`;
- identification of `gwr_cut_inside_lands` with an actual `pstep_tr`
  successor — it speaks about `pyield`'s result;
- a one-step theorem bundling the two cut horns;
- removal or derivation of `gwp_cut_below`, which remains a positive assumption;
- connection to `prun` and to observation.

#### Next

Not widening the new relation. A minimal `gwr_cf`, and landing the cut-inside
horn's actual `pyield` / `pstep_tr` successor in it. After that, whether the two
horns together let `gwp_cut_below` be demoted from an assumption to a
consequence of the dichotomy.

#### Widening the target, not sharpening the horns

> `gwp_cut_below` was needed because the old target relation admitted only one
> cut horn. After widening the target to `gwr_cf`, both horns establish the same
> conclusion, so the proof can eliminate the exhaustive disjunction without
> deciding which horn holds and without proving exclusivity.

```text
A ──▶ gwr_cf
B ──▶ gwr_cf
────────────
A ∨ B ──▶ gwr_cf
```

What is needed is exhaustiveness plus a common landing site — **not** the
impossibility of `A ∧ B`. Exclusivity remains unproved, and remains unneeded.

Confirmed by reading the statement: `gwr_cut_below_demoted`'s `requires`
contains neither `gwp_cut_below` nor any horn selector. And the demoted premise
is not one that was harmlessly true anyway — it is refuted on the shipping
fixture.

#### What `gwr_cf` changes, and at what scope

> `gwr_cf` copies `gwp_cf` and weakens exactly the two components crossed by the
> cut: the live stack relation and store realisation. Values, computations,
> worlds, counters, and terminal shapes are unchanged.

That is the shape actually taken, not a claim that it is the unique minimal
repair. The reverse refutation shows the widening is strict **as a whole**; with
no external ablation, the individual necessity of each of the two weakenings is
not credited.

#### The union is a genuine carrier

> Ordinary `pakrel` accepts the equal-length horn and rejects the one-frame-deep
> horn; `gwy_k` accepts the latter and rejects the former. Their union is
> therefore a genuine common carrier rather than a renaming of either input
> phase.

Verified independently, and read off the two length facts — `pakrel` forces
equal length, `gwy_k` forces a difference of exactly one — rather than from
any exclusivity theorem.

#### The `pyield` identification, at its actual strength

`fst (pstep_tr …)` is identified with `pyield …` **under the branch premises
`pstep` already reaches `pyield` at**, needing no additional semantic
hypothesis — not unconditionally for all configurations. `pstep_tr` intercepts
only `PEmit`, so the trace is `[]` here by computation.

#### The demotion is juxtaposed, not adopted

> The side condition is eliminated in the new parallel theorem only. The
> existing `gwp_var_deep_step` and its callers remain unchanged and continue to
> require `gwp_cut_below`.

So this is a proof that the side condition **can** be removed, not a codebase in
which it has been.

#### Ablations, this time in a different form

- relation strictness and each horn's discrimination: proved as **in-file
  refutation lemmas**;
- an exhaustive per-premise load-bearing check: **not performed** this gate, for
  cost reasons — each would need a full-file copy and run.

The in-file refutations are stronger statements than an ablation, but they do
not substitute for the exhaustive check, and are not counted as one.

#### Next

Juxtapose a `gwr_cf`-based `PVar` bundle and repackage every head-frame branch
into the same conclusion. That is where a complete deep-`PVar` theorem free of
`gwp_cut_below` first exists. Deleting or replacing the old bundle is a decision
to take afterwards, on the comparison.

#### The old conclusion was false, not merely unproved

> The cut-inside fixture does not merely escape the old proof: it refutes the
> old bundle's conclusion. Therefore no strengthening of that proof can cover
> the fixture while retaining the same target relation. The wider `gwr_cf`
> conclusion is a semantic change forced by the machine state.

The refutation names why: `gwp_step_at` admits only two allocation states, and
both fail — at one the successor's counters have left the frontier, at the
other the residual pair's lengths differ and `pasrel` refuses. That
retrospectively justifies the previous gate's decision to widen the target
rather than sharpen the horns.

#### The two bundles are not comparable as propositions

> The new bundle has a strictly weaker antecedent — `gwp_cut_below` and every
> horn selector are absent — but a coarser consequent, replacing `gwp_cf` by
> `gwr_cf` and forgetting part of the old phase information. Hence the complete
> propositions are not classified as stronger or weaker.

Confirmed by reading: `gwb_var_deep`'s premises are `gwy_cf`, `pcl_mono`,
`pcl_down` — three, with no horn selector. What is given up is concrete: the
stutter branch's shape information — the decomposition of `k1`, the
`padx_ktop`, and the successor being `pacfrel` rather than the coarser
`gwr_cf`.

#### The count split is structural, in one branch

> The explicit `1:0 \/ 1:1` count split is necessary for the successor shapes
> admitted by the theorem. In the terminating branch, the right-hand step
> reaches `PDone`, while `gwr_st` has no clause relating a running left `PStep`
> to a right `PDone`; a synchronized `1:1` target is therefore unavailable.

Verified independently at the definition:
`~(gwr_st r s (PStep c1 k1) (PDone x2))` holds for any relation, state,
computation, stack and value. This is a claim
about that terminating branch, not that `1:0` is needed at arbitrary
configurations.

> Trace equality is carried inside each count alternative rather than factored
> outside the disjunction. Both alternatives preserve it, but the theorem
> records it together with the corresponding step-count witness.

That is weaker than the generated phase's arrangement, where trace equality sits
outside the exits; here the count witness and the trace travel together.

#### The phase confluence, at its actual scope

> All successor shapes produced by this `PVar` bundle embed into the common
> `gwr_cf` target. No general inclusion or unification theorem for the
> surrounding phase relations is proved.

The general `pacfrel ==> gwr_cf` is **false** — `gwr_st` has no `PDone`,
`PStuck` or `PRejected` clause — and was deliberately not written. Only the
`PStep`/`PStep`-restricted version exists.

#### Where the new semantics was actually needed

Seven non-yield branches transported through two existing bridges with no new
proof. So the place that required new semantics is localised to the **cut and
yield boundary** — which is a sign the surrounding design is stable, not that
the work was small.

#### Not proved

- an independent exhaustiveness theorem — the head-frame case analysis reuses
  the old bundle's argument;
- strictness of `gwr_cf` over `gwp_cf` beyond a single fixture;
- any complete implication between the old and new bundles, in either direction;
- concrete runs through the new bundle for the `PModeF`, `PPromptF` and
  `PSiteF` branches;
- the old bundle and its callers are untouched and still require
  `gwp_cut_below`.

#### Next

Not deleting the old bundle. Decide the phase-sensitive dispatcher carrier that
has `gwr_cf` among its successors, and only then move `PReadP`, `PWriteP`,
`PWeave` and the context-extension forms — so that which of `gwy_cf` and
`gwr_cf` each constructor departs from and lands in never has to be guessed.

#### A phase carrier for the dispatcher

An interface gate: it adds no coverage. Its deliverable is a phase tag, a
relation indexed by it, and proofs that the interface **is** the existing
relations.

All seven configuration relations sit at seven tags, as two-way implications,
with **nothing changed**: `pacfrel`, `padx_cf`, `gwy_cf`, `gwp_cf`, `gwr_cf` in
the stack family, `padxg_cf` and `gwe_cfg` in the generated one. The carrier
is a tag plus four component selectors, and the one genuinely non-uniform datum
is the reachable-shape selector: only `pacfrel` admits `PDone`, `PStuck` and
`PRejected`; `gwp_cf` and `gwr_cf` reach `PPaused`; the other four are
`PStep`-only. That could not be folded into the stack component, which is why
it is a selector of its own.

#### The transition shape parameterises only the landing

`gwc_lands` is `gwb_run_at` with the landing relation abstracted and everything
else verbatim, and the two are proved equivalent at `GWCGwr`. So the existing
`gwb_*` family enters the interface **by citation**, with no proof restated —
and the count pair survives, so `1:1` and `1:0` are expressible in one
statement.

#### The lattice

Four uniform inclusions and one conditional:

```text
GWCPadx ──▶ GWCGwy ──▶ GWCGwp ──▶ GWCGwr        (no hypotheses)
GWCPadxg ──▶ GWCGwe                              (no hypotheses)
GWCPacf ──▶ GWCGwr        requires pawf s and PStep?/PStep?
```

All five pairs are **unequal as relations** — none of the edges degenerates
to an equality. But the fifth edge's strictness and the unconditional
inclusions should not be conflated: `GWCPacf ==> GWCGwr` is a conditional edge,
and both of its premises were separately refuted as load-bearing — the `pawf`
one on a pair where every other conjunct of `gwr_cf` holds and only `pawf`
fails.

The `gwp_cf`/`gwr_cf` edge's strictness has a structural reason, checked
independently: `gwy_k` forces a length difference of exactly one, so a pair with
**equal** stacks cannot sit at the narrower tags while `gwr_kd` admits it.

#### The two families are joined

`PPerform` fits as `GWCGwy → GWCGwe` and `PSplice` as `GWCGwe → GWCGwy`,
both by citation. So the round trip between the stack and generated families is
expressed in the carrier rather than in prose.

#### The set-of-tags form, at its actual status

> `gwc_lands_set` is inhabited extensionally by weakening a definite landing.
> No branch has yet been proved only through a genuinely multi-tag landing set
> whose selected tag depends on the operational horn.

The `.fst`'s own heading said "inhabited by a real branch"; it now says
"inhabited by weakening a definite landing", with the distinction spelled out.

#### Not proved

- dispatcher coverage — five branches were fitted, not all of them;
- transitive inclusions, e.g. `GWCPadx ==> GWCGwr`, stated explicitly;
- the departure tag as a first-class predicate — it appears only in each
  fitting lemma's `requires`;
- separation of tag pairs not joined by a lattice edge, such as `GWCPadx`
  against `GWCPadxg`;
- a genuinely multi-tag landing.

#### A methodological correction

This gate's brief claimed `padx_cf ==> gwy_cf` was missing. It was not:
`gwy_padx_cf_is_cf` already existed, and needs no `pcl_down`. The claim came
from a name-pattern grep that did not match the lemma's naming. Absence claims
from name searches are unreliable and will not be made again — the same error
had already occurred once, over `gwe_k_mono`.

#### The dispatcher reaches the surplus phase, and the set becomes necessary

This gate was planned as coverage: carry `PReadP`, `PWriteP`, `PWeave` and the
context-production form into the surplus phase, so that which relation each
constructor departs from and lands in is never guessed. It delivered that, and
it also settled a question the previous gate had left open in the other
direction.

#### The cell operations are blind to the surplus, and the write keeps it

Two lemmas, each the ordinary one with `pakrel` weakened to `gwy_k` in the
hypothesis and **nothing weakened in the conclusion**. The read still agrees on
both sides; the values are still related. The reason it survives is small and
worth naming: the surplus frame is a `PBindF`, and `pfind_param` skips it.

The write's conclusion is `gwy_k`, not `pakrel` — `pset_param` rebuilds the
frames above the cell it writes, so the skipped frame is put back. No horn of
that lemma lands in the ordinary relation: **the write cannot delete the
surplus**, and the statement records that as a negative rather than leaving it
to be inferred.

#### Four branches

`PReadP`, `PWriteP` and `PWeave` depart from `GWCGwy`; `PEnterCtx` departs from
`GWCGwy` and lands there definitely. `PWeave` and `PEnterCtx` need `pcl_down`
and nothing else; the two cell operations need no hypothesis beyond the
departure. `PEnterCtx` needed no new lemma at all — the existing append lemma
for the deep stack relation already covers a related prefix pushed onto a
surplus-carrying tail.

#### The unplanned result: no tag at all covers `PReadP`

Each of the three cell/plan constructors has **two horns, and one of them
halts** — `PStuck` for a missed cell, `PRejected` for an unbuildable plan. A
halted pair is relatable only where the reachable-shape selector is `GWCRAll`,
and that is `GWCPacf` alone. The successful horn keeps the surplus in the stack,
which the plain relation refuses on length. So the two horns are relatable in
disjoint places.

That makes the landing set of the previous gate **necessary rather than
weakening**. The record now carries the refutation in the strong form:

- the miss horn admits `GWCPacf` and no other phase, uniformly in the allocation
  state the landing predicate hides;
- the miss horn **does** land there, so the refutation is not about an empty
  situation;
- the hit horn refuses `GWCPacf`;
- therefore, quantified over **all seven phases** in one statement, no phase
  covers both horns.

There is a generic form too, and its hypotheses turned out **asymmetric** in a
way worth recording: the miss departure needs `None?` on the cell search and
**nothing else** — no relation, no well-formedness, nothing about the right-hand
side. Only the hit departure needs to be a departure at `GWCGwy`. A separate
lemma instantiates the generic form at the two fixtures, so it is not a theorem
about an empty class.

#### What the result actually rests on

Checked independently, by counterexample rather than by a failed proof attempt:
drop the surplus from the hit departure — take both stacks to be a bare
parameter cell — and the successor pair is ordinary, lands at `GWCPacf`, and
`GWCPacf` then covers **both** horns. The quantified conclusion is false there.

So the theorem does not rest on `PReadP` having two horns. It rests on the
surplus surviving one of them. The hit-side hypothesis is load-bearing and now
has a witness saying why.

#### Irreducibility, not maximality

What is proved is that the two-element landing set **cannot be reduced to a
single tag**. It is not proved, and not claimed, that the set is maximal in the
inclusion order: a larger landing set would also be true, and nothing here rules
one out.

#### Not proved

- **the necessity packaging exists for `PReadP` only.** `PWriteP` and `PWeave`
  are proved to *fit* the two-tag set — an upper bound. Their necessity is not
  proved, and the similarity of their shapes is not a proof;
- the context-consuming forms are untouched. They have a stuck horn of their
  own, from a handle that does not resolve, so the same shape is expected —
  expected, not shown;
- dispatcher coverage is still partial;
- the departure tag remains absent as a first-class predicate.

#### A note on what verification does not check

Two claims in this gate's prose were false while every F\* proposition in the
file was discharged. One said the two-tag set was the only pair of tags the
three constructors could reach — the successful horn lands at `gwy_cf`, so three
phases admit it. The other announced necessity in the heading of two branches
where only fitting had been proved.

Neither was reachable by re-running the checker, because neither was a
proposition. The correction was to limit the prose and then to raise the
proposition to the strength the prose had claimed — the second half being the
better outcome, and the one that produced the seven-phase statement above.

#### The consuming forms, and necessity with no constructor in it

Three more branches carried into the surplus phase — `PExtendC`, `PResumeC`,
`PExtendCtxC` — and then the result of the previous gate detached from the
clause it was discovered on.

All three depart from `GWCGwy` and fit the two-tag set. Each needs `pcl_mono`
and the departure, and nothing else; `pcl_down` turned out unnecessary for all
three. Their halting horn is cheaper than `PReadP`'s: the stuck state's two
components are constants of the module rather than data read off the redex, so
the two halted sides are equal with no inversion at all.

#### Two existentials, doing two different jobs

`PExtendCtxC` allocates on its resolved horn and does not on its unresolved one.
That makes it the first branch whose **two horns land at different allocation
states**, and it is worth separating which quantifier absorbs which split.

- The **state** existential inside `gwc_lands` absorbs the `s` / `paalloc s`
  split. It was already there — the landing predicate has always hidden its
  allocation state behind `exists s'` with the two-way disjunct `s' == s \/ s'
  == paalloc s` — and this branch is the first computation node to exercise the
  second disjunct.
- The **tag** existential inside `gwc_lands_set` absorbs the `GWCGwr` /
  `GWCPacf` split. That one is about which phase the pair is related at, not
  about how much has been allocated.

The two are independent: this branch exercises both at once, and neither
substitutes for the other.

#### Necessity, abstracted

The previous gate's necessity result named `PReadP` in its statement. Nothing in
its argument did. It uses two facts only — the left side halts, and the two
successors are `PStep`s whose stacks still carry the surplus — and both were
already generic. So the statement is now generic too: no constructor appears in
it, and the four step counts are independent rather than pinned to one apiece.

The clause it was generalised from is re-derived through it, under the original
hypotheses verbatim, with the original left untouched and uncited.

**The abstract lemma does not, and cannot, guarantee non-vacuity.** It is an
implication about departures whose horns have a given shape; nothing in it says
such departures exist. Non-vacuity is carried entirely by the instantiations —
`PReadP` and `PWriteP` — and by their firing fixtures, which exhibit concrete
departures at `GWCGwy` with the same redex, differing only by whether the stack
carries the cell.

#### Where necessity stands

Settled for **`PReadP` and `PWriteP`**. The other four multi-horn branches —
`PWeave`, `PExtendC`, `PResumeC`, `PExtendCtxC` — are proved to **fit** the
two-tag set and nothing more. Their horns have the same shape, but shape is not
proof, and no instantiation has been carried out for them.

As before: this is irreducibility to a single tag, not maximality in the
inclusion order. A larger landing set is also true and nothing rules one out.

#### One concrete independent confirmation

Checked separately from the branch, at the fixture stacks: the surplus pair
survives the move to `paalloc pabot`, the move is not a no-op, and — the point —
the pair is **still not ordinary** at the moved state.

This is recorded as a concrete confirmation and **not as a general theorem**.
The general preservation is `gwp_k_mono_alloc`'s, and the non-collapse to the
ordinary relation is the existing length argument's; the check adds neither. Its
value is that it puts both together at a witness, on the one branch where the
allocation state moves, which is where a gap would have hidden.

#### Not proved

- necessity for the four remaining multi-horn branches;
- dispatcher coverage of the value rules;
- the departure tag as a first-class predicate.

#### A composition primitive for the surplus phase

Every branch so far concludes a single landing, and single landings are **not
closed under unrestricted composition**. That is weaker than saying no two legs
compose — two legs that both stand still plainly do. What fails is the general
case: the landing predicate's allocation state is existential but bounded to at
most one allocation, and `paalloc (paalloc s)` is neither `s` nor `paalloc s`,
so the bound is false of a composite that allocates twice while true of each
leg. That is why no composition lemma was stated or cited anywhere in the
branch development.

#### The multi-step shape differs in three ways, not one

The ordinary phase already showed what to put in the bound's place: `paext`
together with the **frontier equation** `s'.an1 + s.an2 == s'.an2 + s.an1` —
the two runs allocated the same number of times, however many that was. But it
would be wrong to describe the multi-step predicate as the single landing with
one conjunct swapped. Relative to it, the reach predicate

1. **strengthens** the trace condition, from the two traces being equal to both
   being empty;
2. **generalises** the state condition, from the one-allocation bound to `paext`
   plus the frontier equation;
3. **drops** the exact single-step provenance entirely — not a weaker version of
   it, none.

(1) is a strengthening and (2)–(3) are weakenings, so **these syntactic
differences alone do not order the two shapes, and no unguarded implication in
either direction is proved**. That is a statement about what has been proved,
not a proof of incomparability: a mixture of strengthenings and weakenings does
not by itself refute either implication, and no separating instance is
exhibited. What is proved is one **guarded** implication from landing to reach,
and it needs (1) as an added premise precisely because a landing cannot supply
it.

The trace strengthening is not a technicality. An empty trace *is* the statement
that the run passed through no `PEmit`, so **any run through an emit is outside
this composition**. Every branch proved so far happens to deliver emptiness, but
that is a property of those branches, not of the machine.

#### What composes, and in which form

- **The silent reach composes.** Counts add side by side, accessibility is
  transitive, and the two frontier equations add to give the third — over `nat`,
  with no subtraction anywhere, so nothing truncates.
- **With the intermediate state explicit, composition is ordinary.** This is the
  form the proof is done in.
- **With the state hidden, what holds is a dependent composition, not
  transitivity.** An ordinary transitivity would take two independent premises.
  Here the second premise must be **universally quantified over the middle
  state**: what has to be supplied is a second leg available at *every* state
  the first leg could have landed in, not at one named state. The reach
  predicate hides where the first leg arrived, and the second leg's hypotheses
  live at that state; a premise naming one particular state would be about a
  state the first leg is not known to reach. The premise is correspondingly
  harder to discharge than a transitivity's.

#### Fuel indices are not transition counts

The composed statement carries counts `2 1`. That is a pair of **fuel bounds**,
not a pair of step counts: the run function's numeric argument is an upper
bound, and a run that reaches a terminal state returns without consuming what
remains.

Two consequences, both recorded:

- The generic composition exhibits a reach at **unequal fuel indices**. It does
  not establish that one side performed two operational transitions and the
  other one; that would need the extra unit of fuel shown to drive a real step,
  which is a separate fact about the configuration reached.
- The closed instance performs **one operational transition on each side**. Its
  `1:0` leg departs from a state that has already halted, so the extra fuel
  drives nothing — terminal padding, not a stutter transition. What the instance
  witnesses is exactly that an unequal fuel-indexed reach is inhabited.

A related correction: it is **not** true that the single landing can only speak
of one transition per side. It is stated at arbitrary counts; every branch
happens to instantiate it at `1:1` or `1:0`. What it cannot do is compose, and
that — not the count pair — is the gap this closes.

#### The genuine unequal-transition stutter, and where it is not

The carrier's own stutter is real: the left pops a frame and the right does not
move, and that is an unequal transition step, proved generically along with its
composition to counts `2 1`.

But **no closed instance of it is built**. Building one needs a deep-stack pair
whose right stack is empty and whose left is not, together with the node the pop
uncovers, and that fixture is not constructed.

The outstanding item is exactly that and no wider: **no closed instance of the
carrier's `gwc_fit_var_deep` 1:0 pop is connected to the reach predicate**. It
would be wrong to state this as an absence claim about the file. A closed
instance of a genuinely unequal transition count already exists elsewhere in it
— two left transitions against zero on the right, computed at closed terms, with
a companion guard showing one step does not suffice and the three
configurations are pairwise distinct.

#### An independent check, and exactly what it separates

The reach predicate was deliberately **not** claimed to be strictly weaker than
the single landing: no instance separating them as predicates has been
exhibited, so what is asserted is only that the bound is absent and that nothing
recovers it.

Checked separately, at the existing two-allocation fixture: a state two
allocations out satisfies accessibility, well-formedness and the frontier
equation, while the one-allocation bound **rejects** it. That is the reason
single landings could not compose, as a closed instance rather than an
observation.

Its scope is exactly the state conditions. No run is exhibited, so it is **not**
a separation of the two predicates on configurations, and none is claimed.

#### Not proved

- no finite-run theorem and no observation theorem — this is a composition
  primitive; nothing is stated about a run driven to exhaustion, and no branch
  is shown to hand its landing to another branch's departure;
- no converse from reach back to landing;
- no closed instance of the carrier's `gwc_fit_var_deep` 1:0 pop connected to
  the reach predicate (an unequal-transition instance does exist elsewhere in
  the file);
- no separation of the two predicates on configurations.

#### The carrier's own stutter, at closed terms

The previous gate left exactly one item standing: the carrier's `1:0` pop had
only ever been used generically, and the one closed composite in the file
performed a single operational transition on each side — its `1:0` leg was fuel
padding past a state that had already halted. This gate closes that.

The fixture is small: a left stack carrying one surplus bind frame, an empty
right stack, the same value on both sides, an empty store, and the bottom
allocation state. The left pops the surplus and lands on the configuration the
right is already sitting at; both then step to `PDone`. Composed, the counts are
`2 1`, and this time they are transition counts, not only fuel indices.

Two things had to be true for this to close the item, and both were checked
rather than assumed.

- **The `1:0` comes through the carrier.** The lemma establishing it cites the
  carrier's stutter and nothing else — no computation on the run function
  appears in its proof. Had it been recomputed, the pop would not have been
  connected to anything.
- **The landing state is extracted, not re-established.** The landing predicate
  offers its state existentially with a one-allocation disjunct. Here the
  allocating arm is impossible — it would force a successor counter of one while
  both successors sit at zero — so the state is *forced* to be the bottom one.
  The explicit-state form is then introduced from the eliminated witness, with
  the arrival relation carried over rather than re-proved. Only the empty-trace
  conjuncts are supplied by computation, because the landing predicate speaks of
  trace equality and not emptiness.

#### Genuine, and mechanically distinguished from padding

Distinctness of endpoints alone would not separate a real step from padding, so
the check was done at the transition function rather than at the run function,
and comparatively: both departures of this instance **move** under one
transition, while the earlier instance's second-leg departure **does not**. The
two kinds of `1:0` now sit in the same file and are told apart by a computed
fact rather than by prose.

#### What this is, exactly

The first closed witness **in the carrier development** — not the first in the
file. A closed instance of an unequal transition count already existed
elsewhere, computed directly on the run function with a companion guard showing
one step insufficient. What is new is that the carrier's pop now has one too.

The fixture is not claimed to be canonical, minimal, or the only one.

#### A claim from the previous gate, narrowed

The earlier ledger said no branch had been shown to hand its landing to another
branch's departure. That was true of the sections it was stated at, and it is no
longer the right way to describe the position: here leg one arrives at a pair
and leg two departs from exactly that pair. What remains open is the general
fact — **no general theorem shows that arbitrary branch landings satisfy the
next branch's departure premises**.

#### A residual, restated correctly

It would be wrong to record "a closed carrier-pop instance that allocates" as
outstanding: the carrier pop *cannot* allocate. It is a value node popping an
identity bind frame, and it rewrites neither the store nor the counter, so no
such instance could exist.

The two residuals that are real, and neither is built:

- a closed carrier pop taken at a **non-trivial already-allocated state** rather
  than at the bottom one;
- a closed **composite containing the carrier pop in which some other leg
  allocates**, so that the allocating arm is exercised somewhere in the chain.

#### Not proved

- no finite-run theorem and no observation theorem; nothing is stated about a
  run driven to exhaustion;
- no general chaining of branches;
- no converse from reach back to landing — the state is pinned at one fixture by
  computation, which is not a recovery of the bound in general;
- runs through an emit remain outside every statement.

#### The obstruction to chaining is the lattice, not the machine

The standing residual was that no general theorem showed a branch's landing
satisfying the next branch's departure premises. This gate found why, and the
answer turned out to be structural rather than operational.

Every stack-phase branch **departs** from the surplus tag but is **stated** as
landing at the weakened one, because the run predicate the branch family was
built on hard-codes that weakened relation as its landing. And a landing there
cannot be fed back into a surplus departure: the weakened stack relation is a
disjunction admitting the ordinary pair, which the surplus relation refuses on
length.

That is refuted at a closed pair, and the refutation's proof mentions no
transition, no step function and no run — which is the evidence that the
obstruction sits in the phase lattice and not in the machine.

#### The weakening was never necessary

The underlying exit lemmas for the three non-allocating value exits already
conclude the **surplus** relation at the successor, at the same allocation state,
with nothing allocated. The wrapper layer threw that away. Restating those three
branches at the tag they actually land at costs no new proof — the existing
lemmas are cited, not redone — and the earlier statements remain correct
weakenings that nothing here replaces.

#### A companion shape, and its logical status stated carefully

For branches whose allocation state does not move, a landing form that fixes the
state outright and carries no existential.

It would be wrong to call this a restriction of the general landing. Read as
propositions the two are a **mixture**: the companion strengthens (traces pinned
to empty rather than merely equal; state fixed rather than existential and
bounded) and weakens (well-formedness, accessibility and the single-step
provenance are all absent — no provenance conjunct at all, so not a weaker
version of one either).

So these differences alone do not order the two shapes, and **no unconditional
implication in either direction is proved**. That is a statement about what has
been proved, not a proof of incomparability — no separating instance is
exhibited either. A conditional bridge is the honest shape for one: add
well-formedness and a stationary-provenance premise and the two can be related.
That bridge is not stated. The one implication proved goes to the multi-step
reach predicate and takes well-formedness as an explicit hypothesis for exactly
this reason.

Because the state is fixed, composing two of these is **ordinary composition** —
no existential to eliminate, so none of the dependent, Kleisli-shaped premise
the hidden multi-step form needed. That is bought by fixing the state and by
nothing else: the composition is unavailable wherever a leg allocates, which is
the case the general one exists to handle.

#### The chain, with the second departure discharged

The chain lemma takes two hypotheses: a surplus departure, and a **shape
premise** on the landed pair. The second branch's departure premise is *not*
among them — it is read off the first branch's landing. That is what the
residual asked for.

A closed instance runs it: two parameter frames popped in sequence, with both
shape premises discharged by computation, and with the second departure included
explicitly in the guard's conclusion as the conjunct that the weakened landing
could not have supplied.

#### What was removed, and what was not

Checked independently at the closed fixture, and this is the gate's central
distinction:

- after the chain the landed pair **is at the departure tag** — the tag feeds
  back, which is precisely what the weakened landing was refuted for;
- but its left stack is headed by a bind frame, not a parameter frame, so the
  chain lemma's own shape premise is **false** there and a third link is
  unavailable.

The lattice obstruction is removed. The shape obligation is not: a phase tag
does not determine a redex, and removing that premise would need a statement of
a different kind, which is not made.

#### Not proved

- **not general chaining.** Three branches have sharp landings; the rest keep
  the weakened one and the refutation applies to them. One chain is built. No
  statement quantifies over branches, chain length, or run length;
- allocating branches are outside the companion shape entirely;
- runs through an emit remain outside;
- the counts are fuel indices; they are shown to be transition counts only at
  the closed fixture.

#### Chains that cross an allocation, and a ledger sentence corrected

The previous gate's ledger said allocating branches were outside the
standing-still machinery entirely. That was an overclaim, and correcting it is
where this gate started.

The standing-still form's state argument is the **target** state; the departure
state does not occur in the definition. So an allocating branch is expressible
in it — one states it at the post-allocation state — and the allocating value
exit now has a sharp landing exactly that way, by citing the exit lemma that
already delivered the surplus tag there. Four branches now have sharp landings
rather than three. The previous section's proofs are untouched and correct; what
was overstated was the scope of an exclusion.

#### What the single-state composition actually excluded

Not allocating branches. The composition fixed one state and required both legs
to be stated at it, so what it excluded is a chain whose two legs carry
**different landing-state indices**.

A chain that allocates can still satisfy it. Taking the scope exit first and the
parameter exit second, the first leg allocates — yet **both** legs land at the
post-allocation state, so the single-state lemma closes it. The chain that
genuinely needs two states is the other order: parameter exit then scope exit,
whose legs land at `s` and at the allocation of `s`.

Both chains are proved, and the two-state composition is proved with the states
independent, with the single-state lemma derived as its diagonal case rather
than asserted to be one. The restriction was not load-bearing: in the proof the
first leg's state never enters the conclusion, whose relational conjunct comes
from the second leg's landing while the first contributes only its traces.

#### What a landing forgets — four things, not all of one kind

The honest counterpart of "allocating branches fit" is that the form cannot
distinguish an allocating branch from a non-allocating one. That is now a
proposition, not a remark: the forgetful map from the reach predicate is proved,
and it drops

- the **departure state** itself, which has no argument position in the landing
  form;
- **accessibility**, which relates the two states;
- **frontier balance**, which also relates the two states;
- **landing well-formedness**, which does **not** mention the departure state —
  it is a condition on the landing state alone, dropped for a different reason
  entirely: the landing form carries only the phase's own well-formedness
  selector, which is trivially true at the plain tag.

Describing all of these as "the conjuncts that mention the departure state"
would be wrong; only the middle two do.

So "allocating branches fit" means their **landing is expressible**. It does not
mean the allocation is **recorded**. Where the allocation must be recorded, the
reach predicate is what says so, and the recovery lemma from a post-allocation
landing back to a reach is proved.

#### The state parameter is not inert

Checked independently, so that the point above is not over-read. At the closed
allocation-crossing chain the landing holds at the post-allocation state and
**fails** at the departure state — the landed counters have advanced past the
departure frontiers.

Two different facts, both true: the allocation *is* visible in the landing
statement, and the departure state is *not* recorded by it.

#### Not proved

- the shape obligation remains, in both chains, for the reason the previous gate
  gave;
- not general chaining: four branches have sharp landings, two chains of two
  branches are built, and nothing quantifies over branches, chain length, or run
  length;
- no equivalence between the landing and reach forms — the two implications go
  in opposite directions under different hypotheses, and neither is proved to
  invert the other;
- runs through an emit remain outside;
- the counts are fuel indices; they are shown to be transition counts only at
  the closed fixture.

#### Every redex has a branch, and what that does not buy

The principal obstruction is the shape obligation: a phase tag does not
determine a redex, so a chain lemma has to be told which redex the landed pair
presents. This gate attacked it from the coverage side.

Four of the machine's fourteen computation constructors had no carrier branch at
the surplus phase — the operation bind, the handler install, the parameter
introduction, and the emit. A fifth had one only from the *generated* phase. All
five now have branches departing from the surplus tag.

The machine facts underneath were not new: an existing lockstep lemma already
had them for exactly these five nodes, and it is untouched and uncited. What is
new is the carrier packaging — the departure at a tag, the run equations at fuel
index one that name the landed pair, and the landing in the fixed shape.

#### The dispatch, and its exact reach

For a departure at the surplus tag whose left state is a step configuration,
**some** landing exists — for thirteen of the fourteen constructors.

The exception is the perform node, and it is a real one: its branch covers only
the horn where the prompt search succeeds and the clause is not scoped. The
other two horns — search failure, and the scoped-clause rejection — have no
lemma cited and none assumed. So the accurate statement is that **the dispatch
is closed for thirteen constructors**, not that coverage is complete: every
constructor has *a* carrier-level lemma, but the perform node's is conditional
and covers one horn of three.

The value node was expected to need a second case analysis on the stack head. It
did not: its branch is already stated over an arbitrary deep-stack pair, and the
head split happens inside that lemma's own proof. The cost of folding it in is
visible elsewhere and is recorded — its count pair is `1:1` or `1:0`, the second
being the stutter, and the dispatch's conclusion forgets both, so the two horns
collapse into one. That collapse loses exactly the information earlier gates
were built to expose.

#### Where trace equality and empty trace come apart

Four of the five new branches land in the sharp form, whose traces are pinned to
empty. The emit does not, and that is proved rather than remarked: at **left
fuel index one** its trace is a one-element list, which the sharp form's first
conjunct forbids. The refutation is universal in the landing phase, the right
count and the right configuration, and it is *not* claimed at any other left
count — extending it would be a statement about the run function at arbitrary
fuel, which is not made.

So among the five one-step branches at count one, the one that refuses the sharp
form is exactly the emit. That is the difference between requiring the two
traces to be *equal* and requiring them to be *empty*, and it is now load-bearing
rather than stipulated.

#### The existential over counts is not idle

Checked independently. At the stutter fixture from an earlier gate the
dispatch's conclusion holds, while a landing at counts `1:1` is false at every
tag — the right side has already reached a terminal state while the left is
still stepping. What holds there is `1:0`.

What that shows, exactly: **the existential count pair cannot be replaced
uniformly by `1:1`**. It does not show that no fixed pair would do; ruling out
`1:0` as well would need a second fixture, of the lockstep kind, that refuses
it. Only the `1:1` substitution is refuted here.

#### Not proved

- **the shape obligation is untouched.** Exhaustiveness of a case analysis is
  not selection of a case. Both dispatch statements are existential in the phase
  and in both counts, so neither names the landed configuration, and a chain
  needs that;
- the perform node's two uncovered horns;
- nothing quantifies over run length, over chains, or over the branch family;
- non-vacuity is shown at one fixture for the dispatch and one for the emit
  split; nothing is claimed about which programs produce these departures.

#### A fragment that re-departs, and quantification over a fuel index

Every statement so far has been at fixed counts. This gate produces the first
one quantified over an arbitrary common fuel index.

The opening is a fragment of seven shapes whose branches land at the tag they
departed from, at the same allocation state, at counts one and one: the
operation bind, the handler install, the parameter introduction, the splice, and
the value node over a parameter, mode or prompt frame. Because the tag and state
return, the single-state composition applies to any two of them in sequence, and
that is what makes an induction possible.

What the fragment leaves out is listed with a reason for each: the value node
over a bind frame (the deep stutter — it lands at the weakened tag and cannot
re-depart, which is the refutation from an earlier gate showing up as a
concrete exclusion), over a scope frame (allocates), over a boundary or site
frame (can yield), over the empty stack (terminates), the emit (not sharp), the
perform node, and every halting horn.

#### The one-step closure is definite, and needs less

The dispatch of the previous gate concludes an existential — some tag, some
counts. An induction cannot use that. The closure here concludes a **definite**
tag and **definite** counts, which is exactly what the step case needs.

It also needs less: only the downward-closure condition on the clause relation,
required by one of the seven arms. The monotonicity condition that the
existential dispatch carries is not needed at all.

A small lemma was required to drive the case analysis from the left
configuration alone: under the deep stack relation, a left head that is not a
bind frame forces the same constructor on the right. The three value-exit
lemmas take both stacks' heads as arguments, so the right one has to be
recovered.

#### The theorem, and what it does not do

For any `n`, if the departure is in the relation and the fragment predicate
holds of the left configuration at every index below `n`, the landing is at the
departure tag, at the departure state, at counts `n n`.

**This does not discharge the shape obligation — it iterates it.** The premise
asserts the shape at every index, and nothing here proves that premise for any
program. What it shows is that the shape obligation is the *only* thing between
one step and `n` steps for this fragment: no further lattice premise, no
allocation premise, no side condition on the interpreter accumulates as `n`
grows. The single condition is the same one at every `n`.

**And `n` is a fuel index, not a transition count.** It indexes the run
function's fuel on both sides. The premise does force each of the first `n` left
configurations to be a step configuration, so no unit of the left's fuel is
returned unspent — but that the successor *differs* at each index is a separate
fact, and it is established only at fixtures, never for the theorem.

#### A hypothesis the statement was carrying without using

The gate's own report flagged that the monotonicity condition appeared in the
theorem's interface but was used by nothing it cites. Checked independently by
restating the theorem without it and proving it: the remark is correct and the
hypothesis is genuinely droppable, so the statement was weaker than its proof.

It has been removed from the theorem rather than recorded as an observation, and
the two closed instances no longer establish it. The theorem's hypothesis set is
now strictly smaller than the existential dispatch's. That does not show the two
conditions are independent, nor that the monotonicity condition is unnecessary
elsewhere; neither is investigated.

#### Two closed instances, and where the run leaves the fragment

At `n` two on an earlier fixture, and at `n` three on a new one, with the shape
premise discharged by computation.

The three-frame instance also shows where the premise *fails*: at index three
the left configuration is a value node over the surplus bind frame, and the
fragment predicate is false there. So it is not a fixture where the premise
happens to hold forever — the run leaves the fragment exactly at the deep
stutter, which is the concrete face of the lattice refutation.

For both fixtures the successive configurations are proved pairwise distinct, so
for *those two runs* the fuel indices are transition counts. The three-frame
case needed its own lemma: the earlier one covers only the last two of its three
transitions, because the two-frame fixture is what the three-frame one steps
into, and the first transition was not covered by anything.

#### Not proved

- the shape obligation, which is iterated rather than discharged;
- that the successor differs at each index, for the theorem at any `n`;
- that a sharp landing is impossible for the excluded branches — their exclusion
  is a statement about the form their landings were stated in, and no refutation
  is proved or attempted;
- anything about which programs produce departures in the fragment.

#### Iterating through an allocation

The previous gate's iteration theorem was fixed-state: the landing sat at the
same allocation state the departure did. That is why its fragment excluded the
one value exit that allocates. This gate widens the fragment to eight shapes and
threads the state.

Two pieces already in place made it available. The allocating exit lands at the
tag it departed from, at the advanced state. And the two-state composition —
proved an earlier gate, and used there only in a single hand-built chain — puts
the composite at the *second* leg's state, with the first leg's state never
entering the conclusion. So threading is all the induction needs.

#### The index is constructed, not observed

The state the theorem's landing is indexed at is computed by walking the indices
below `n` and applying one allocation at those where the left configuration
carries the allocating shape.

It is worth being exact about what that function is. It is **total** — defined
at every input, presupposing nothing about the run being in the fragment, the
pair being related, or anything being well-formed. It is **not** "the state the
run reaches": these states are not components of the machine, and the run
function does not compute one. The function constructs an index out of the
shapes along the left prefix. That the constructed index is the one the landing
relation actually holds at is *proved*, under the theorem's premises — it is not
an unconditional operational fact.

#### A hypothesis, and the difference between where it is spent and why

The narrow theorem does not need the monotonicity condition on the clause
relation; that was checked last gate and the hypothesis removed. This one does
carry it, and its only consumer along the present derivation is the allocating
arm — established by deleting the hypothesis and observing exactly one error, at
exactly that call site, with a control experiment for the other condition
landing at a different one.

That experiment locates where the condition is **consumed**. It does not show
the condition is semantically necessary for the allocating branch: the exit
lemma requires it because the lemma beneath it does, and no counterexample
showing the exit fails without it is exhibited anywhere. A proof-path fact, not
a fact about the boundary condition.

#### What relates the two theorems, and what does not

Proved: the fragment predicates are **ordered** — the narrow implies the widened
— and the allocating fixture leaves the narrow one, so the widening is not idle.
True by inspection: the new signature adds the monotonicity condition.

**Not proved, and not asserted: any ordering of the complete premise
conjunctions, in either direction.** Calling the two hypothesis sets
incomparable would need a witness meeting every premise of the narrow theorem
while failing the added condition, and none is exhibited; the independence of
the two conditions is not investigated. The companion lemma restating the narrow
conclusion under the narrow fragment premise plus the added condition is an
**agreement on common ground**, and agreement is not evidence of
incomparability.

Checked independently: on a run that takes no allocating step the widened
theorem degenerates correctly — the premise lifts, the threaded index stays put,
the allocation count is zero, and the landing is the one the narrow theorem
already gives at that fixture. The generalisation does not disagree with the
theorem it generalises where both apply.

#### Not proved

- the shape obligation, still assumed at every index and discharged for no
  program — this gate iterates it exactly as the last one did;
- the counts remain fuel indices; `n n` does not say either side performed `n`
  transitions;
- the semantic necessity of the monotonicity condition for the allocating
  branch;
- any ordering of the two theorems' full premise sets.

#### Discharging the shape obligation, for one family

Two gates produced iteration theorems whose premise asserts, at every index
below `n`, that the left configuration lies in a fragment. Both said plainly
that this *iterates* the obligation rather than discharging it: the premise was
proved for no program, only computed index by index at individual fixtures.

This gate discharges it — for one family, from a condition on the departure
alone, at arbitrary `n`.

The machine fact that makes it possible is small. The value node over a
parameter frame keeps the value, keeps the store, keeps the counter, and drops
exactly one frame. So a value node over a stack whose top `n` frames are all
parameter frames steps to one whose top `n-1` are. The condition is *preserved*,
and preservation is one induction rather than `n` computations.

The combined theorem then has **no per-index premise in its statement**: the
per-index assertion is replaced by a condition on the departure's stack, not
supplemented by one.

#### Three layers, and they are not the same

This is where care is needed, and the file now separates them mechanically.

1. **At any `n`, the structural condition yields the per-index premise.** That
   is the discharge, and its only hypothesis is the structural condition —
   nothing about the interpreter, nothing about the relation, nothing about the
   right side.
2. **The left structural family is inhabited at every `n`.** A conditional
   theorem says nothing on its own about whether its hypothesis is ever met, and
   every closed member in the file has exactly three frames — so without this
   the section could in principle have been about a class empty past three.
   Constructing the stacks settles it: the condition holds at every `n` and the
   discharge fires there, with store, counter and tail all arbitrary. (Checked
   independently first, then promoted into the file rather than left as an
   outside observation.)
3. **The combined theorem's concrete non-vacuity is at `n` three, and nowhere
   else.** It additionally requires a *related right configuration*, and the
   construction in layer 2 produces no such thing at any `n`. "Infinite family"
   is correct of the left structural condition and of the discharge; it is not
   established for the related-pair theorem.

Reachability is in neither layer. The tail of the constructed stacks is
arbitrary — nothing says it carries a surplus, or is related to anything, or is
reachable — and which surface programs produce such stacks is not addressed.

#### Fuel indices become transition counts, off a fixture for the first time

Every earlier statement is careful that `n n` is a pair of fuel bounds, and the
identification with transition counts had only ever been proved at named closed
configurations — four such lemmas, each by computing stack lengths, all of them
checked individually rather than asserted away.

For this family it holds at a symbolic departure and arbitrary `n`: the left
stack loses exactly one frame per step, so its length strictly decreases, so the
configurations at distinct indices differ.

Scoped twice: **this family**, and the **left** index only. The iteration
theorems still do not identify the two, and nothing here changes that.

#### A hypothesis inherited from the proof route

The combined theorem carries the downward-closure condition on the clause
relation. It adds nothing relative to the narrow iteration theorem — that
theorem carries it too, because its one-step closure passes it to the prompt
arm.

But a run in this family never reaches a prompt frame: the top `n` are all
parameter frames, so that arm is never taken. The condition is present because
the theorem *cites* the general iteration theorem, which covers all seven
shapes, rather than doing its own induction over the one arm it needs. Whether
it is semantically necessary for a parameter-only theorem, or would fall away
under a direct induction, is not investigated, and no experiment is offered
either way.

That is the same distinction the previous gate drew about the monotonicity
condition: where a hypothesis is *consumed* along a derivation is not where it
is *needed*.

#### Not proved

- the shape obligation in general — one of seven shapes, one stack shape;
- non-vacuity of the related-pair theorem beyond `n` three;
- that any program produces such stacks, or that such stacks are reachable;
- the right index as a transition count;
- the necessity of the inherited hypothesis for this family.

#### Pointing the machinery at the law, and finding the gap

Nine gates of reach, composition and iteration machinery. This one asks whether
any of it can be aimed at right identity, and the answer is sharp in a way that
is worth recording exactly.

The **reconvergence was already proved**, generically, long before the carrier
existed: the bind of a value with the identity continuation and the value alone
land on *literally the same configuration*, at fuel index two against zero, with
the trace empty and the store and counter untouched. That is a fact about the
machine and this gate adds nothing to it.

That the left side performs two ACTUAL TRANSITIONS is a separate fact, and it is
also already proved generically, by the two step lemmas that the reconvergence
is assembled from. The counts in this gate's landings are fuel indices, and
**this gate adds no count-pinning of its own** — it neither re-derives those
step lemmas nor borrows the earlier fixture's pinning.

#### No tag admits the departure

The two departing redexes have different head constructors. Checked against the
definitions rather than the prose: the carrier's computation component is one of
two administrative relations at two tags and the ordinary relation at the other
five — and **both administrative relations special-case exactly three heads and
fall through to the ordinary one everywhere else.** The bind head is not among
the three. So at this departure all seven tags reduce to the same obligation,
and that obligation fails at index one, in the ordinary relation's final
catch-all clause. One clause is the whole refutation.

Checked independently — as an outside check, not as a theorem in the file: the
refutation does not depend on the fixture. At **any** value types, clause
relation, state, value, stack and store, no tag relates the pair. What the file
states at one named pair appears to hold at every instance; the file itself
still states only the named-pair version.

A companion guard rules out the obvious alternative reading — each side *is*
related to itself at the plain tag, so it is the crossing that is refused, not
the empty stack or the bottom state.

#### The landing side needs no concession

After the detour the two configurations are equal, so the landed pair is
related. And not only in the standing-still form: the other,
provenance-retaining landing form holds too, at counts two and zero, with the
non-allocating disjunct and the bottom state — at arbitrary interpreter
parameters, with no hypothesis.

The two forms are **not ordered**, and neither is the stronger. One retains
provenance, accessibility and well-formedness, which the other drops; the other
pins both traces to empty and fixes the state, where the first asks only that
the traces agree. An earlier gate recorded that mixture and recorded that no
unconditional implication is proved in either direction. What is claimed here is
only that both hold at this pair.

So the machinery reaches this pair on the landing side and refuses it on the
departure side. **A landing with no departure.**

#### What that localises

A **departure relation** is the **first blocker exposed by the present
machinery** at this pair: every carrier theorem that could be pointed here
consumes a departure premise, and that premise is the first thing that fails.

**That is not the claim that it is the only blocker.** Nothing shows that
supplying such a relation would let the adjudication go through, or that no
further obstruction lies behind it — no attempt past the departure premise is
made anywhere.

It is not a run — that is supplied generically and has been for a long time.
Not a composition — every composition and iteration theorem built over the last
several gates *consumes* a departure. As to observation, the established point
is narrower than "observation is not the obstacle": the **exhibited run supplies
no separating trace, store or counter**, and **no observation theorem is
applied**, so nothing here settles what an observation would do at other runs or
other pairs.

#### The candidate, named and not adopted

A computation relation that relates the bind-with-identity to its body and
otherwise behaves like the ordinary one is defined, proved to be implied by the
ordinary relation, and proved **strictly** weaker — the separating witness being
the right-identity pair itself.

What is deliberately not done is longer than what is: no phase, no tag, no stack
or store component, no configuration relation, no transition compatibility, no
monotonicity, no equivariance, no composition, and no claim that this is the
shape to adopt. The file also records a concrete reason for doubt: the ordinary
relation's own clause at that head demands a relation on the *continuation*, and
this candidate discards it by testing the continuation syntactically.

It is a name for what is missing, at one component, and nothing more.

#### Not proved

- anything about the law itself — this is a localisation of what is missing, not
  progress on the statement;
- that the candidate relation is the right one, or usable, or extensible to a
  phase;
- any ordering between the candidate and the two existing administrative
  computation relations — and those two are not classified as weakenings of the
  ordinary relation either: they treat three heads *differently*, and at one of
  them can refuse a pair the ordinary relation accepts;
- the counts remain fuel indices.

#### The candidate relation, examined — the doubt moves rather than clears

The previous gate named a computation relation that admits the right-identity
departure, and recorded a concrete reason for doubt: it tests the continuation
*syntactically*, where the ordinary relation's own clause at that head demands a
Kripke-style relation on it — for every accessible state and every related pair
of values.

The obvious repair is to replace the equation by that relation: ask the
continuation to be *related to* the identity continuation rather than to *be*
it. That variant is defined, and it does relate the right-identity pair and is
implied by the ordinary relation.

#### It answers the recorded doubt, and does not satisfy the clause

The doubt as recorded was that the continuation obligation is *discarded*. The
semantic variant does not discard it — it states it, and a projection lemma
recovers it.

**But the clause is still not met, and the gap is now located rather than
suspected.** Two refutations pin it:

- the clause at that head asks for the two *bodies* to be related and the two
  *continuations* to be related **to each other**; the new disjunct supplies the
  left continuation related **to the identity** and the left body related **to
  the whole right-hand side**. Different things, and at a named instance the
  second is shown not to yield the first;
- from the new relation holding, **the Kripke relation between the two
  continuations cannot be derived** — refuted with a concrete witness that
  replaces the right continuation while the pair stays accepted. That is a
  refutation of the implication to the required relation, not a claim that the
  two continuations are unrelated in every sense.

A negative, stated exactly, is this gate's deliverable.

#### Where the syntactic and semantic versions come apart

The syntactic version implies the semantic one, generally: the equation
discharges the Kripke obligation outright.

The converse is **refuted at a concrete witness** — at the fixture types, the
fixture clause relation, and a state whose world is empty while both frontiers
stand at five. Accessibility from such a state can only speak about keys at or
above five, so the keys below it are *frozen*: the quantifier in the Kripke
relation never reaches them, and a continuation can be related to the identity
there without being it.

Scope, kept apart: the forward direction is general; the failure of the converse
is established at that witness, not shown for every instance of the two type
parameters.

Checked independently: that separating state is **well-formed**. Every
configuration relation in the file pins well-formedness, so a separation at an
ill-formed state would have carried much less force. This one does not.

And where the separation does *not* happen is also recorded: at the bottom state
the frontiers are zero, every key is reachable, and a continuation related to
the identity agrees with it at every argument. Separating there would need a
function pointwise equal to the identity without being equal to it — neither
exhibited nor refuted.

#### A correction to my own brief, made by machine

I briefed this gate claiming the reflexivity side condition was a real
difference between the two versions — that the syntactic one did not need it.

That was wrong, and the gate proved it wrong. Restating the syntactic version in
general form requires exactly the same hypothesis; it lands in the conjunct the
two versions share, while the conjunct they differ in discharges freely. The
earlier statement appeared not to need it only because it was made at a fixture,
where the condition reduces to an identity on a constructor. A refutation at a
value the empty world speaks for nothing about shows the hypothesis is needed by
**both**.

The precise form: the hypothesis cannot be removed uniformly from either
version's general statement over arbitrary values. That is not the claim that
reflexivity is necessary and sufficient at each individual instance.

This is the second consecutive gate where the error in the round was in the
*briefing* rather than in the work, which is the thing to watch.

#### Not proved

- the right-identity departure problem is not solved, and this candidate is not
  supported for adoption;
- of the components a phase would need, only monotonicity along accessibility is
  proved; the stack component, store component, configuration relation, tag,
  transition compatibility and equivariance are not supplied, and **no judgement
  is offered on whether the semantic variant makes any of them easier or
  harder** — nothing is proved either way;
- no ordering against the two existing administrative computation relations;
- the separation at the bottom state.

#### One step in, the pair is already inside the machinery

The two preceding gates both looked only at the departure, and both concluded
something about a missing relation there. One step in, the picture is different.

The left side steps to a value node over a stack carrying a **surplus identity
bind frame**. That is exactly what the `administrative` stack relations describe
— the ones the whole development from the administrative sections onward was
built for. Proved at arbitrary arguments, under four hypotheses
(well-formedness, reflexivity of the value relation at that value, the two
stacks related, the two stores related): the once-stepped pair is a genuine
carrier pair, at two tags.

#### The run factors, and the whole of it is one reach

The reconvergence's `2:0` factors as `1:0` then `1:0`, through that midpoint, at
**arbitrary `pakrel`-related ambient stacks** — and the composite is a single
reach statement at the plain tag. The four premises above are carried
throughout; the theorem does not hold of an arbitrary raw pair of stacks.

The first leg cites the existing step lemma and **does not re-prove the
transition fact**; what is added is a reading of that same transition through
the run function at fuel one, which the composition consumes.

**The indices are fuel indices.** The `2:0` of the reach and the two `1:0`s of
its legs index the run function's fuel. That the left performs two actual
transitions and the right none is a separate, operational fact, and it comes
from the two step lemmas over the transition function — not from anything in
this gate.

#### Where the second leg loses definiteness, exactly

The anticipated difficulty was real and is now located.

The stutter lemma from the surplus-phase sections is stated with its right-hand
stack *literally* empty. At the right-identity midpoint the right stack is the
ambient one, so that citation covers the case where the ambient stack is empty
and no more.

At arbitrary ambient stack the carrier's own fitting lemma still applies, but
its **count pair stays existential** — that is precisely what dropping emptiness
costs. A definite `1:0` at arbitrary ambient stack is available, from the
underlying stutter lemma that the carrier fitting is derived from: the carrier
version reaches it only after the surplus horn has been forgotten, and that
forgetting is where the count goes existential.

#### What this does to the earlier localisation

Not a retraction. The departure refutation stands, and is re-exhibited.

The accurate statement is that **the existing carrier's proof coverage does not
include the departing pair; it begins at the midpoint, one transition in.** What
is missing is still a departure relation — what this gate does is locate *where*
that gap sits, not narrow it to something whose repair would suffice. Nothing
here shows that supplying a relation for that transition would close the law, or
that no further obstruction lies behind it.

#### Checked independently

The earlier gate exhibited a landing whose departure is refused at one fixture.
With the reach now generic, the two halves can be put together: at arbitrary
value types, clause relation, state, value, both stacks and both stores —
**those parameters satisfying the four premises**, namely well-formedness, the
value related to itself, the stacks `pakrel`-related and the stores
`pasrel`-related — the `2:0` reach holds **and** the departure is refused at all
seven tags, in one statement. It is not an unconditional statement: without the
four premises the reach half does not follow. (The refutation half needs none of
them, which is why it is stated separately in the file.)

So the asymmetry found at a fixture is generic throughout these admissible
related starts, rather than a property of that one pair. This is an independent
check and **not a theorem in the file** — the file still carries the
fixture-level version.

#### Not proved

- **no law is proved anywhere.** A factorisation is not an adjudication, and the
  file says so in its own section heading and ledger;
- no relation for the transition that installs the identity frame;
- the previous gate's negative result about the candidate computation relation
  stands, and nothing here supports adopting it;
- of the components a phase would need, still only monotonicity along
  accessibility;
- the definite count at arbitrary `pakrel`-related ambient stack comes at the
  plain tag; the surplus-phase tag gives only the existential pair there;
- nothing about starts that do not satisfy the four premises.

#### The law's actual shape, and where the run stops being carried

The previous gate factored the right-identity run only where the bound
computation is a **value**. The law's actual shape binds an arbitrary
computation. This gate moves to that shape.

At a body satisfying the four premises — well-formedness, the body **related to
itself**, the two stacks `pakrel`-related, the two stores `pasrel`-related — one
left step installs the surplus identity frame and the midpoint is a carrier
pair, at two tags. For a value body the self-relatedness premise reduces to the
earlier gate's condition on the value; that direction is proved, and no converse
is claimed.

#### The iteration machinery enters in the middle

Because the midpoint sits at the surplus tag, the iteration theorem applies
there. Composing the first leg with it gives the whole prefix in one statement,
at `1+n` against `n`.

**Those are fuel indices**, as everywhere in this development; nothing here says
either side performs that many transitions.

The composition used the **single-state** form. That is a fact about this proof
route — neither leg moves the allocation state, so the two legs' states coincide
— and not a claim that the single-state form is what such a composition needs in
general.

#### It does not complete the law, and the reason is structural

The iteration premise carries the run **while the body is still executing**. It
says nothing about the body reaching a value, and nothing about what happens
when it does. The popping stutter — the previous gate's second leg — is stated
at a value redex, so at an arbitrary body it is not reached at all.

What exists is a factorisation into three parts of which the middle is
conditional and the last is out of reach at arbitrary body.

No departure relation is supplied for the arbitrary-body pair. The
all-seven-tag refutation remains the earlier value fixture result; it is not
generalized here.

#### The parameter-prefix family misses this line entirely

Worth recording as a negative, and it was found rather than assumed: the family
for which the previous gate discharged the shape obligation **never meets this
midpoint at a positive budget**. The midpoint's left stack is headed by a bind
frame, and that family's condition demands a parameter frame at every position
it covers.

So the one discharge achieved so far contributes nothing here. The premise had
to be discharged by computation instead, at a non-value body, and at budget one
— with that instance proved to stop there.

#### Checked independently: the budget is not pinned at one

That single instance leaves open whether the premise is dischargeable at any
larger budget. It is. Nesting the bind-with-identity keeps the midpoint's run
inside the fragment while the nesting lasts: checked at a body with **two**
nested layers, where the run stays in the fragment at indices zero and one and
leaves it at index two.

Scope, exactly: this is a **concrete instance at depth two**, establishing that
the budget is not fixed at one. The general correspondence between nesting depth
and budget is **not proved** — neither here nor in the file — and this is an
independent check rather than a theorem in the file.

(My first attempt at this miscounted the layers by one and failed; the body has
two bind nodes, not three, so the run stays in the fragment for two steps.)

#### Not proved

- no law is proved anywhere;
- no departure relation is supplied for the arbitrary-body pair, and the
  all-seven-tag refutation is not generalized to it;
- the fragment premise is assumed, not discharged, except by computation at one
  instance;
- termination of the body is neither proved nor assumed;
- the general nesting-depth-to-budget correspondence;
- the counts are fuel indices throughout.

#### The third leg attaches, and the run is factored end to end

Until now the popping leg had never been composed onto the other two. It is now.

For a body satisfying the base premises — including the body **related to
itself** — together with the fragment premise and the value-at-`n` premise, and
at `pakrel`-related stacks and `pasrel`-related stores, the whole run is one
landing at `n+2` against `n`. These remain **fuel indices**.

The composition is still the single-state one, and for the same reason as
before: the third leg's source lemma pins both counters, so **the allocation
state** does not move across any of the three legs. That is about the allocation
state only — it is not a claim that the machine configuration or the store are
unchanged, and they are not.

#### It degenerates to the earlier case, with one hypothesis more

At `n` zero the statement becomes the earlier gate's `2:0`, and that is proved
as a corollary rather than asserted.

Honest difference, recorded in the file: the corollary carries one hypothesis
the earlier result does not — the downward-closure condition. It **enters
through the iteration theorem and is not removed along this proof route, even at
zero**; that it is semantically necessary here is not shown, and no experiment
either way is offered. So this is a **consistency check between two routes**,
not a subsumption of the earlier one.

#### Two premises, and what the second one really says

Both are assumed.

The value-at-`n` premise is **stronger than the body's evaluation reaching the
designated value redex**: it also fixes the residual stacks, the stores, and the
relation between the two sides' values. And because a residual stack remains, it
is not termination of the machine configuration in any sense — the run has more
to do after it.

So what changed in this gate's bookkeeping is that **body-to-value became an
explicit premise** where before it was simply absent. That is a change in what
the statement says out loud, not in what has been proved.

The file also records why the premise is not derivable from what precedes it:
the middle leg's conclusion does not *name* the pair it lands on, and the
fragment premise is false exactly when a value is reached, so it cannot imply
reaching one.

#### The two sides' values need not agree

Found while doing the work, not assumed: the popping lemma underneath was
already stated at two separate values, so the composition needs only that the
two values be *related*, not identical. The earlier statements are the diagonal
case of this, and are unchanged.

#### Checked independently, at the closed instance

The file treats `n+2 : n` as fuel indices throughout and does not settle whether
they are transition counts at the one closed instance. That is decidable by
computation, so it was decided.

At that instance — a **non-value** body, at the file's fixture stacks and stores
— the `3 : 1` are transition counts: the left moves at each of its three units,
the right at its one, all four left configurations are pairwise distinct, and
**the two sides finish on the same configuration**. A reconvergence at a
non-value body, witnessed by computation.

Scope: that closed instance only. This is an independent check and not a theorem
in the file, and nothing here makes the general statement's indices transition
counts.

#### Not proved

- no law is proved;
- **no departure relation is supplied for the arbitrary-body pair**, and the
  all-seven-tag refutation remains the earlier value-fixture result — there is
  no lemma refuting a non-value body's departing pair;
- the two premises are **not discharged uniformly over arbitrary bodies**; that
  one closed body at `n` one is the only joint discharge exhibited in the file;
- the parameter-prefix family from an earlier gate does not reach this midpoint
  at any positive budget, so that discharge contributes nothing here;
- the counts in the general statement are fuel indices.

#### Both assumed premises discharged, for an unbounded family

The three-leg factorisation stood on two assumed premises. For one family of
bodies — the bind-with-identity nested `n` deep around a value — **both are now
discharged at arbitrary `n`**, and the main statement's hypothesis list is
exactly the base one from the previous gate:

well-formedness, downward-closure on the clause relation, the value related to
itself, the two stacks `pakrel`-related, the two stores `pasrel`-related.

Those five remain. What left the statement is the *fragment* premise and the
*value-at-`n`* premise — for this syntactic family only. Even the body's
self-relatedness, which I expected to need as a hypothesis, came out by
induction from the value's.

#### The fragment premise cost nothing at all

It discharges with **no hypotheses**: below index `n` at least one nesting layer
remains, so the redex is a bind node, and the fragment predicate's first arm
admits that at any stack.

Worth recording against two gates ago: the parameter-prefix family, for which
the shape obligation was first discharged, was proved not to reach this midpoint
at any positive budget. It is not used here and was not needed — a different arm
of the same predicate was applicable from the start.

#### Both sides move through the middle

The middle leg advances both sides by the same index, so the right accrues bind
frames too. At the end each side carries `n` of them over its own ambient stack,
and the two residuals are `pakrel`-related.

The frame relation at an identity bind frame is available without extra
hypotheses **beyond the ambient tails being related** — it does not relate
arbitrary stack pairs, and nothing here says it does.

#### Why this still is not the law

The conclusion is a reach-and-factorisation statement: it constrains the
**landed pair and the two traces**. It is not a source or departure relation and
it is not an observation theorem, and those are what a law about the two
programs would have to be stated in terms of. No tag is added, no departure
relation is defined, and the gap located three gates ago is not closed.

The family is also a syntactic construction. Nothing in the file elaborates a
surface program into it, and nothing claims a program produces one.

#### Checked independently: the family reconverges

The file concludes that the landed pair is **related** at the plain tag.
Relation is not equality, and the file does not say the two sides meet.

At depth two — beyond any closed equality witness exhibited in the file — they
do: the left at fuel four and the right at fuel two land on **literally the same
configuration**, both traces empty, from two departures that are different
terms.

Scope: that closed instance at depth two only. Reconvergence to the same
configuration at arbitrary `n` is **not proved**, here or in the file, and this
is an independent check rather than a theorem in it.

#### Not proved

- no law is proved; what is proved is a factorisation of the run;
- no departure relation for the arbitrary-body pair, and the seven-tag
  refutation remains the earlier value-fixture result;
- the discharge is proved for one family; **no discharge for another body is
  established**, which is not a claim that no other body admits one;
- nothing about which surface programs produce such bodies;
- reconvergence at arbitrary `n`;
- the counts are fuel indices.

### A discriminating example: `catch` against a prompt-local `Var`

Can the recovery of a `catch` see the protected block's writes — global — or
the state as it stood before the block ran, transactional? It is a good test of
what the facility buys, and the answer is sharper than "higher-order effects
make it possible".

**The semantics is decided by handler composition order, and both are available
today.**

- **`Var` outside the scoped `catch`.** Its cell is reached through the real
  stack and is never copied. It is **live**, so the recovery — and everything
  after the scope — observes the block's writes. That is global semantics.
- **`Var` inside, so that the scope borrows its prompt and crosses it.** The
  cell travels in the borrowed segment as a by-value `ParamF`, so the block
  writes a **snapshot** and the write is gone when the scope's answer comes out.
  That is transactional semantics.

`test/Scoped.purs` already pins the underlying placement distinction. `stateH`
is installed inside and
`ctrH` outside, both at the one reserved scalar label; the block sets the inner
cell to `999` and bumps the outer to `42`, and the fixture asserts
`Right [ 200, 999, 200, 42 ]`. The third element is the borrowed cell reverting
to its snapshot; the fourth is the outer cell staying live. **Both semantics,
side by side, in one program, decided by where the handler was installed.**

**What the general facility would add** is not the choice itself but its
*range*: today the borrowed path requires the intervening prompts to be
all-fast, so the transactional reading is only available across handlers that
qualify. The general weave **is intended to extend** the same distinction to
intervening handlers that do not — a reference prototype at B2b.1, with the
laws and the simulation still open, so it is not a capability that exists yet.

**What a `catch` clause cannot do today is choose dynamically at a fixed
placement.** `runScope` at a `catch` yields roughly `Either e (ctx x)`, so on
`Left e` there is **no `ctx` at all** — the failure path carries no context
through which an intervening `Var`'s state could be passed on or dropped. The
clause is therefore not free to pick global or transactional per invocation;
what is choosable is where the handlers sit.

**The two static meanings can be represented by composition.** Beside handler
ordering, the state can be put into the answer: the `catch` owner's answer
former is `Either e`, so the distinction to write down is `(Either e a, s)` —
state survives the failure, global — against `Either e (a, s)` — state sits
inside the success branch and is discarded on failure, transactional. Both of
these fix the meaning **statically**, exactly as placement does. Neither gives
`catch` a new power.

**Dynamic choice at one fixed placement instead requires** one of:

- a **composite handler that takes the policy as an argument** — the choice is
  then data the handler is given, not a property of how the handlers were
  arranged;
- or a **state-aware machine capability**: checkpoint, commit, restore. This is
  **not** the finalizer-frame mechanism — a finalizer guarantees release on
  unwind, while a state transaction controls snapshot, commit and rollback. It
  is an independent capability and should be scoped as one.

*What is implemented where, since these are easy to conflate.* The shipping
runtime keeps `prepare_scope_fast`'s by-value `ParamF` snapshot; that is what
the fixture above exercises. `PICell` and `enter_layer_frames` belong to the
`GeneralWeave` prototype, and the shipped runtime has no general context plan.
The shipped `catch` clause does weave its recovery, but through the fast borrow.

*Status of the claims.* The snapshot behaviour and the live-cell behaviour are
both **checked**, by the fixture cited. What is **not** checked is the
`catch`-specific sequence — write inside the protected block, throw, and read
in the recovery — for either placement. Two fixtures in a pair, one per
placement, would fix the distinction at the point where it is most likely to
be assumed rather than verified.

### What is not decided

- The classification stays three-way, and B1.5 and B1.6 are reasons to expect it
  to stay that way: the machine built the general path from provenance alone,
  with no capability supplied from the surface, B1.6 made production live and
  effectful with no hypothesis left on it, and B1.7 gave the context a
  first-class identity the surface can select. It is not yet settled, because
  the five laws are FALSE as stated — the observation relation exposes
  allocator names — and B2b.1 has to repair it. Only if that fails does
  `Reinstantiable ≠ ContextWeavable` become a shipping fact. (The name for
  that contingent fourth class appears in the exchange that proposed it as
  `ContextThreadable`; recorded here as `ContextWeavable` to keep the vocabulary
  note above true of the code as well as the prose.)
- The residual-context representation and its identity discipline are settled
  **for the reference semantics** — a shipping store and the shallow `pval`
  model's boundary both remain. B2a, the trace-aware step, B2b.1 and B2b.2
  are all done: B2b refuted the laws as stated, B2b.1 repaired the relation,
  and B2b.2 made that repair a semantics rather than a set of instances. What
  is left is B2b redux — relating the two sides of each law as computations,
  which is what "proving a law" now means.

The order, revised after B2b:

| gate | what it settles |
|---|---|
| ~~B1.6~~ | ~~effectful production, exact-once as an observation~~ — **done** |
| ~~B1.7~~ | ~~a first-class context handle, selected by identity~~ — **done** |
| ~~B2a-1~~ | ~~the `pcut_scope` / `pfind_mode` association discipline~~ — **done**: proximity is a semantic requirement |
| ~~B2a-2~~ | ~~`pconf_wf` over the whole configuration, preserved by every transition~~ — **done** |
| ~~trace~~ | ~~make the observation relation trace-aware~~ — **done**: five laws retargeted at `pobs_tr_eq` |
| ~~B2b~~ | ~~the five laws~~ — **all six propositions refuted**: the relation exposed allocator names |
| ~~B2b.1~~ | ~~nominal observation relation and boundary discipline~~ — **done**: the former counterexamples repaired at concrete configurations |
| ~~B2b.2~~ | ~~the nominal fundamental theorem~~ — **done**: transition and finite-run compatibility, and `pcrel` ⟹ `pnobs_tr_le`, all universally quantified |
| ~~B2b redux~~ | ~~the five laws, re-proved using B2b.2~~ — **refuted again**: the laws are stated across two projections of one plan |
| ~~B2b.3a~~ | ~~the administrative relation: granularity and reach~~ — **done**: discriminating on both sides; produce/enter is a real difference |
| B2b.3b | its soundness — `pfind_prompt`, `pfind_param`, `pcut_scope`, `pset_param`, dispatch, finite runs, and `pnobs_tr_eq` |
| B2b.4 | the laws that remain candidates, over the administrative relation |
| ~~—~~ | ~~the design decision on right identity and transparency~~ — **taken**: keep the protocol, restate right identity, move transparency to B3 |
| B3 | equivalence with the fast borrow — now including transparency as a simulation obligation; a shipping store; and the shipping interpreter proved to meet the boundary discipline |

The trace step sits between B2a and B2b deliberately, and is not optional
polish: while `pobs_eq` observes values only, a prefix-replaying implementation
satisfies every law, and B1.6's exact-once result stays disconnected from any
proof obligation.

One fact about the TCB that constrains the fallback: implementing library-side
`Either` / `Array` / `Maybe` weave capabilities as PureScript callbacks and
pinning them with fixtures does **not** leave the TCB at zero — a fixture
observes behaviour at chosen points, it does not prove the callback. The TCB
stays flat only if F\* interprets the residual protocol, or if the
descriptor/capability is extracted from F\*. That was a second reason for
running B1.5 before the later gates.

Verifying rather than scratch-building is the point: the risk in a new machine
is not whether it runs but whether preservation and simulation close over the
representation it chose, and deferring that is what leaves a representation in
place that cannot be proved about. The TypeScript-backed project is kept as a
*mirror* for implementability and performance once the transitions are fixed —
not as a gate, since it has already made different choices (shared-cell
semantics among them) that would pull the representation the wrong way.

## Agenda — decisions still open

1. ~~**The surface type discipline in detail.**~~ **Settled** — see "Shipped"
   above. `ScopedClause` turned out not to need threading through `MkHandlers` /
   `CanonicalizeHandlers` / `BuildHandler` at all: `ClauseFor` keyed on the
   operation is enough, and the permission travels as a separate predicate on
   `handler` rather than down the builder chain. The `catch` question is
   answered by the shipped clause, which **weaves the recovery** and gets
   non-re-capture from its own logic by returning `Left e'` outward — the same
   resolution the TypeScript-backed project reached (`weave (recover e)` in
   `test/Test/Scoped.purs:268`), and pinned here by "a recovery that throws is
   not recaptured". "Outside the protection of this `catch`" and "not restored
   to the perform-site context" remain different things.
2. ~~The FFI side of Decision 6.~~ **Settled** — `performScopedImpl` and
   `mkScopedClauseImpl` are exported, the third interpreter is `apply_scoped`,
   and the `magic` on the way *into* `weave` is where the new trusted item of
   Decision 3 physically lives. The surface obligation that pays for it is the
   rank-2 quantifier on `ScopedClause`.
3. Latent/deferred operations, which `2026-08-06` puts next and which will test
   whether a snapshot segment can outlive the dispatch that produced it.
4. Suspension and `Aff`, which is a separate milestone and has its own note:
   `2026-08-11-async-suspend-roadmap.md`. It is ordered *after* the borrowable
   scoped milestone on purpose — a suspension inside a scope saves a
   configuration containing borrowed prompts, cells and the evidence
   environment, so fixing what those mean first decides which handler view a
   callback resumes into. Note also that `Suspended` and Decision 7's
   `Rejected` land in the same match sites and are different in kind (one
   resumable, one terminal); they should be looked at together even if they do
   not share a type.
5. **The representation of the context value.** Two candidates are excluded
   (replaying suspension, precomputed leaf list). **Settled**: the residual
   protocol works, without any capability supplied from the surface (B1.5), and
   its production is a live effectful transition with no hypothesis left on it
   (B1.6), and the context is a first-class persistent identity — a handle the
   surface can hold, select between and extend, resolved by identity and not by
   nearness (B1.7). **Settled as a reference semantics.** What a shipping form
   needs is separate: reclamation, lookup cost, and a bounded id representation.
   See the four limits recorded under B1.7.
