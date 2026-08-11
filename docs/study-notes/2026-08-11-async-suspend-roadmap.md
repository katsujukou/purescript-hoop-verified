# Async, `Suspend`, and what `MonadAff` would cost

Date: 2026-08-11
Status: Direction-setting. No design decision is taken here; what is settled is
the division of responsibility, the reference implementation, and the ordering
against the scoped-effects work of
`2026-08-11-scoped-effects-detailed-design.md`.

---

## A correction, first

An earlier reading of this had the TypeScript-backed runtime supporting async.
It does not: `purescript-hoop/docs/02-effectful-adventure.md` says "Async and
Parallel — Not supported yet", and `runtime/src/machine.ts`'s `run` assumes
`onDone` has already been called by the time it returns — it is synchronous by
construction.

The implementation that does exist is a **separate PoC**,
`~/Projects/purescript-effext`, and it is well ahead of a sketch. It is a third
reference point, distinct from the TypeScript-backed project, and worth naming
as such wherever these notes cite prior art.

---

## The division of responsibility

**The F\* machine does not run `Aff`, and should not be made to.**

An `Aff a` is an opaque PureScript/JavaScript value carrying a scheduler,
fibers, callbacks and a cancellation protocol. F\* can carry one as a `v`; it
cannot evaluate one. So:

```text
F* machine                        PureScript / JS driver
  reaches a suspension
  saves stack + environment
  hands out a request        →    starts the Aff (a real fiber)
                                  waits for the callback
                             ←    returns the value
  resumes from the saved
  configuration at `Var value`
```

What F\* would verify is the **park / save / resume protocol**. Running the
`Aff` stays with `purescript-aff`.

`purescript-effext` is built exactly this way, and its types say so out loud:

- `ASYNC` is a marker row entry and **deliberately not an `Op`** — it cannot be
  handled, and is discharged by `toAff` at the boundary
  (`src/Hoop/Comp.purs:279`);
- failure is **not** part of that capability. Embedding `Aff` honestly needs
  both, so the alias is
  `type AFF r = (async :: ASYNC | THROW Error r)` (`:292`), compared there to
  Koka's `io`;
- `liftAff` launches a real fiber and returns a canceler that kills it and
  signals completion only when that teardown is done; a killed fiber never
  calls `done` (`:338`);
- `toAff :: Comp (AFF ()) a -> Aff a` is the boundary (`:375`).

So the accurate statement is not "F\* runs `Aff`" but **"`Aff` drives a state
machine that F\* verified"**.

---

## Minimal `Suspend` is not `MonadAff`

These must be separated, because the first is a transition and the second is a
protocol.

**Minimal suspension**, plausibly a small addition:

```fstar
| Suspend   : request:v -> comp_tree v cl                       // AST
| Suspended : request:v -> k:stack v cl -> state v cl            // reference
| MSuspended: request:v -> w:menv v cl -> kk:mstack v cl -> mstate v cl
```

with a *pure* resume, `resume (MSuspended _ w kk) value = MStep (Var value) w kk`,
and the obvious per-segment statements: the machine reaches `MSuspended` exactly
when the reference machine reaches the corresponding `Suspended`, and a
configuration resumed from a callback value still satisfies `config_ok`.

**Full `Aff` compatibility** is a different size of thing. Reading
`purescript-effext/src/Hoop/Comp.js`, what it actually involves:

- a callback invoked *synchronously* during registration must resume the freshly
  suspended configuration immediately, without unsafe re-entry and without
  leaving the machine parked (`liftEffect` is exactly this case —
  `Comp.purs:335`). Stated that way on purpose: **F\* always returns
  `Suspended` once**, and the driver is free to resume it at once. "Does not go
  through `Suspended`" would be an implementation optimisation dressed as
  semantics, and would pull the design towards running an external register
  inside a machine transition;
- a second invocation of the callback must be rejected;
- a zombie callback arriving after a kill must be neutralised;
- a kill must propagate into the running `Aff` fiber;
- the canceler's own teardown must be waited for before the machine proceeds;
- finalizers must unwind innermost-first, each in its own context;
- `mask` must defer a kill that arrives mid-release, and unmasking-and-continuing
  must be a single instruction (`Comp.js:38`, `:199` — an unbalanced mask frame
  is an internal error);
- a captured segment that still holds finalizers and is never resumed must be
  treated as dead and unwound anyway, so those finalizers still run
  (`Comp.js:161`).

That last one is the sharpest: it is a property of *multi-shot continuations
interacting with resource release*, and it has no counterpart anywhere in the
current verified development. **It is its own verification milestone, not one
more machine state.**

---

## What stays outside the proof

The trusted base grows, and by more than one line:

- the JS **suspension driver and event-loop bridge** — named that way to keep it
  apart from `Conc`'s scheduler, which is not part of the core machine's TCB at
  all: it is an ordinary library handler. (Not *nothing* is trusted there
  either. Its `await` encodes a per-call result type through an opaque
  `foreign import data Opaque` recovered with `unsafeCoerce`, because a row
  entry is monomorphic — `Conc.purs:26`. That is a separate trusted *signature*
  obligation, of the same kind `liftAff` makes one level down, and it is the
  scheduler's own, not the machine's.);
- that **at most one callback is accepted by the driver**, and hence that no
  suspended configuration is resumed twice;
- cancellation races;
- the `purescript-aff` runtime itself.

These belong in the README's trusted list the day `Suspend` lands, phrased as
precisely as the existing entries. The verified claim would be about the
machine's park/resume protocol, not about the driver.

### Who owns "the callback fires once"

Worth decomposing, because it is easy to file the whole of it under either
"verified" or "trusted" and both are wrong:

| | |
|---|---|
| an external register | may invoke its callback any number of times — nothing constrains it |
| the driver | accepts the first invocation and rejects or ignores the rest |
| F\* | proves that resuming a *live* suspended configuration once preserves the correspondence with the reference machine |
| the boundary | assumes the same suspended configuration is never resumed twice |

That last line is an assumption for exactly as long as the driver is not
extracted from F\*. So the trusted item is **"at most one callback is accepted
by the driver"**, not "the callback fires at most once" — the latter states
something about the world that nobody is in a position to guarantee.

---

## Ordering

1. finish the type-level generalisation gate (scoped note, conditions 1–4 done,
   bind gate next);
2. finish the borrowable scoped milestone — Decisions 2–7 of the scoped note;
3. minimal `Suspend` and a single-fiber sequential `liftAff`, **without**
   cancellation;
4. verify: one resume per live suspended configuration, synchronous callback,
   delayed callback, simulation across a resume;
5. `THROW Error` and the `toAff` bridge;
6. cancellation, `mask`, `bracket`, stack unwind — as one milestone, not four;
7. `MonadAff` published only after 6;
8. a scheduler handler on top: `fork` / `race` / `par`.

**`Suspend` can come immediately after scoped effects. `MonadAff` may only be
claimed once cancellation and resource unwind are done.**

### Why scoped genuinely comes first

A suspension inside a scope saves a configuration containing borrowed prompts,
prompt-local cells and the evidence environment. Fixing what those *mean* first
decides, rather than leaves open, which handler view is restored when the
callback returns.

And `par` / `race` reintroduce the weaving question in a new place — whether
branches share or copy the surrounding state — which is the same question
Decision 2 answered for scopes by putting cells in frames by value. That is a
milestone of its own, after a single `liftAff` works.

### One structural decision to preserve

`purescript-effext/src/Hoop/Conc.purs` makes `fork`, `yield` and `await`
**ordinary operations**, and the round-robin scheduler an **ordinary handler**;
the machine knows only about suspension. That separation is worth keeping in the
verified version — it is what stops concurrency from becoming machine
semantics, and it is the reason the machine's obligation stays "park and
resume".

---

## Settled already

**Suspension inside a borrowed scope is fine at the minimal level.** The whole
machine parks and resumes the *exact* saved configuration — same `w`, same `kk`
— so borrowed prompts, prompt-local cells and the evidence view are all
preserved by construction, and there is no second execution agent that could
retire the owner first. So:

> Minimal suspension is valid inside a borrowed scope because it resumes the
> exact saved configuration. Cancellation and multi-task scheduling must
> re-establish this property separately.

It has to be revisited when cancellation and a scheduler arrive, and not before.

**The callback's value is not an `apply_ok`-shaped assumption.** In F\*'s
untyped core a `Var value` at an arbitrary `v` is structurally safe — nothing
about the machine's behaviour depends on what the value is. What has to be
trusted is narrower and of a different kind: **FFI type-representation
soundness**, i.e. that the callback hands back a representation of the type `x`
PureScript promised. That is the same trusted item the surface already relies
on, not a new obligation on a clause.

**`Suspended` sits beside `Rejected`, as a sibling constructor of `state`.** Not
folded with it into a common `outcome`:

```fstar
type state v cl =
  | Step      : ...
  | Done      : v -> state v cl
  | Stuck     : string -> string -> state v cl
  | Rejected  : rejection -> state v cl
  | Suspended : request v -> stack v cl -> state v cl
```

All they share is that `steps` halts on both. Everything else differs:

| | `Rejected` | `Suspended` |
|---|---|---|
| kind | terminal | quiescent, resumable |
| transition out | none | `resume`, defined only here, and external |
| `converges` | not observed (unchanged: only `Done` is) | not observed |
| `wf_state` | unconditionally `True` | requires the saved stack to be well formed |

Landing in the same match sites is not evidence of being the same concept. If
the sites ever want to be written once, add classification predicates —
`terminal`, `resumable` — rather than restructuring the state/outcome hierarchy;
the payoff for doing that up front is small.

**A callback arriving after cancellation is ignored — always.** Not an
exception, not a `Rejected`: a cancelled external API calling back late would
otherwise throw an asynchronous exception at an unrelated point in the program,
which is worse than doing nothing.

The driver's slot has a lifecycle, and whichever of callback and cancel reaches
`Live` first wins:

```text
Live(config)
   ├─ callback(value) → Claimed    → resume config value
   └─ cancel          → Cancelling → run canceler → Retired

Claimed / Cancelling / Retired
   └─ callback(_)     → no-op
```

- callback first: the suspension completes, and a subsequent kill is handled
  against the *resumed* machine;
- cancel first: the token is invalidated *before* the canceler runs, so a late
  callback is ignored;
- and if the canceler itself synchronously provokes a callback, the token is
  already invalid, so nothing resumes.

This is what `purescript-effext` implements with `token.canceled`, checked
before re-entry (`Comp.js:307`, `:309`, `:354`).

While the driver is handwritten JS, "this automaton is implemented correctly" is
a boundary assumption. But the automaton itself is small and F\*-shaped: over an
arbitrary sequence of external events, **at most one resume is accepted** is
provable of it, separately from the machine. Agreement between that model and
the JS is then differential-testing territory — and extracting the gate itself
later would narrow the trusted base by exactly this piece.

## Open questions

None of design consequence at this level. What is left is the shape of the
`resume` entry point at the FFI, which follows from Decision 6's whitelist work
and is better settled with the code in front of us.
