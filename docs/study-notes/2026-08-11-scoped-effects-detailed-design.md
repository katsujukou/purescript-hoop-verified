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
| B2b.3 | a mode-indexed administrative equivalence, and its observational soundness — the missing middle layer |
| B2b.4 | the five laws, over the administrative relation |
| B3 | equivalence with the fast borrow; simulation with the optimised machine; a shipping store; and the shipping interpreter proved to meet the boundary discipline |

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
