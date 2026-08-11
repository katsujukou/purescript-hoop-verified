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

| Weave : prepared:stack v cl -> body:comp_tree v cl -> comp_tree v cl
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

### The plan must be normalized, not raw

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

### Withdrawn: "keep `ret` on the intermediates and it generalises"

Operationally the transition is definable — over F\*'s single value type `v`,
`PromptF hs ret` in a borrowed position steps perfectly well. It does not
generalise the *surface*, because a `PromptF` holds a table built at one
concrete answer type. Running an inner computation at an unknown `x` does not
need the existing table reused; it needs the **handler family re-instantiated at
`x`**, and polymorphising `ret` alone re-instantiates neither the `Cont` in a
full clause nor its answer type. So the general level needs one of

- prompts holding a polymorphic handler *factory* rather than a table;
- borrowed prompts rebuilt from a context-threading capability;
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
directly — hence a `bindT`-style context-threading capability is required, of
the Polysemy shape rather than a type parameter.

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
   borrowable, factory, context-threading, generalized forwarding — so nothing
   the gate decides can overturn it. Its stop rule (condition 5) is also the
   earliest available check on whether the existing laws and simulation really
   survive a generalised node, and that check is independent of everything else
   here.
3. **The types-only gate in the TypeScript-backed project**, condition 4 first,
   negative fixture before positive.
4. **Choose between table / factory / tactics** from what the gate shows.
5. **The surface API and the substance of Decisions 2–7.**

Steps 2 and 3 are independent and can run in parallel. Step 5 must not start
before step 4: `HandlerF`, `ScopedClause`, the prompt representation and the FFI
all depend on the answer, while `Splice` depends on none of it. What condition 4
moves is how `prepared` is built, whether a prompt holds a table or a factory,
and how the surface is typed — not the splice primitive underneath.

## Agenda — decisions still open

1. **The surface type discipline in detail**: the inner-computation marker in an
   operation signature; how `h (Hoop inner) b` is declared; how `ScopedClause`
   threads through `ClauseFor` / `MkHandlers` / `CanonicalizeHandlers` /
   `BuildHandler`, which currently do not carry the handled type `a` down to the
   clause level; and whether the recovery computation of `catch` is woven into
   the perform-site context, and if so how the clause ensures that failures
   raised by the recovery escape the current `catch`.

   *Not* to be assumed: that the recovery is left unwoven. The
   TypeScript-backed project weaves it (`weave (recover e)` in
   `test/Test/Scoped.purs:268`) and gets non-re-capture from the clause's own
   logic, by returning `Left e'` outward. "Outside the protection of this
   `catch`" and "not restored to the perform-site context" are different things.
3. The FFI side of Decision 6: `performScopedImpl`, `mkScopedClauseImpl` and its
   runtime shape (`{ fun }` is taken by `fast`), the third interpreter, and the
   `magic` on the way *into* `weave` — which is where the new trusted item of
   Decision 3 physically lives.
5. Latent/deferred operations, which `2026-08-06` puts next and which will test
   whether a snapshot segment can outlive the dispatch that produced it.
6. Suspension and `Aff`, which is a separate milestone and has its own note:
   `2026-08-11-async-suspend-roadmap.md`. It is ordered *after* the borrowable
   scoped milestone on purpose — a suspension inside a scope saves a
   configuration containing borrowed prompts, cells and the evidence
   environment, so fixing what those mean first decides which handler view a
   callback resumes into. Note also that `Suspended` and Decision 7's
   `Rejected` land in the same match sites and are different in kind (one
   resumable, one terminal); they should be looked at together even if they do
   not share a type.
