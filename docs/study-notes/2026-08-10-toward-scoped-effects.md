# Toward Scoped Effects: what prompt-local state taught us

Date: 2026-08-10
Status: Findings from the parameterized-clause work, written down for the scoped-effect work that follows

Prompt-local state landed in this period: `var init \s -> handler {...}` on the
PureScript side, `NewP` / `ReadP` / `WriteP` and a `ParamF` frame in the
reference semantics, `MParamF` and cells-in-the-environment in the machine, and
a weak simulation linking them. This note records what that work established
that the scoped-effect work will need, and what it got wrong on the way, because
several of the wrong turns were wrong for reasons that will recur.

---

## 1. The one thing most likely to break first

**Cell labels are not unique, and the reason that is currently harmless is a
property of `var`, not of the machine.**

Labels come from `reflectSymbol` — record field names, or the reserved
`%hoop.scalar` for a bare `var 0`. Two regions can therefore carry the same
runtime label. That is harmless today because of how `var` lays out frames:

```
var init k  =  Handler \comp -> installCells init (install comp)
```

`NewP` pushes `ParamF` first, `Handle` pushes `PromptF` on top, so the stack
(head = innermost) reads

```
[ … ; PromptF ; ParamF ; … ]
        ↑         ↑
        └─ a clause of this prompt runs at its cdr, so the first ParamF
           it meets is its own
```

A clause runs at its own prompt's `below` (the cdr), and `find_param` searches
from there, so the first matching frame is always the clause's own cell. No
other region can interpose. This survives capture and resumption: a clause
inside a captured segment finds its own `ParamF` inside the same segment.

**The enforcement is that `newCellImpl` is private to `Hoop.Engine`, so `var`
is the only thing that can emit a `NewP`.** That is a module boundary, and it is
checkable — but it is not a theorem, and F* cannot make it one: the machine
cannot see the *layout pattern* `var` produces.

### How `weave` breaks it

From `~/Projects/purescript-hoop/runtime/src/machine.ts:476-492`, `weave`
pushes a fresh **owning** prompt for the scoped handler and then reinstalls the
perform-site prompts as **borrowed** ones:

```
[ borrowed_n ; … ; borrowed_1 ; owning ; …original… ]
```

The owning prompt now sits **between a borrowed prompt and its cells**. So:

```purescript
stateH = var { count: 0 } \c  -> handler … { get: fast \_ -> read @"count" c , … }
excH   = var { count: 0 } \c2 -> handler … { catch: scoped … }   -- same field name

with stateH (with excH prog)
```

When `catch`'s clause runs the inner computation through `weave`, `stateH`'s
prompt is borrowed and reinstalled above `excH`'s owning prompt. A borrowed
`get` clause then does `read @"count" c` and walks down past `excH`'s
`ParamF "count"` — **the type says `stateH`'s region, the runtime finds
`excH`'s cell**. Type-safe-looking, wrong answer, which is the worse failure
mode.

The four conditions are all ordinary: scoped borrowing, two handlers each with
a `var`, the same field name (`count` is a natural one), one borrowing the
other.

**So the deadline for deciding about label freshness is not "when
`newCellImpl` becomes public" — it is when `weave` is designed.** Three options
at that point:

1. **Mint labels at run time.** Collisions vanish structurally. Cost: `Region`
   stops being `Region Unit` and must carry a prefix, so `read`/`write` do a
   string concatenation instead of recovering the label from the type — and the
   type-recovery is what currently makes `Region` carry nothing, which is what
   makes the rank-2 escape argument airtight. Measured read cost is
   ~99 ns + 3.8 ns/level, so a concat is a real fraction of it.
2. **Exclude cell-bearing prompts from borrowing.** TS's `borrowable` already
   demands every clause be `fun` or `st`; add a condition. Costs expressiveness.
3. **Put cells inside the prompt frame.** Borrowing then carries them along and
   the layout cannot be disturbed. Rejected once already, because a `ctl`
   clause runs below its own prompt and so could not reach a cell held *in* it.

### The tension underneath

TS's `borrowPrompt` gives the borrowed frame a fresh identity **but the same
cell object**, so writes inside the scope reach the original. Our per-branch
semantics comes from exactly the opposite: cells live in frames *by value*, so
capture copies them. An immutable frame cannot express "the same cell object".

**Borrowing wants sharing; capture wants copying.** Any scoped design has to
say which one wins where, and the two Koka figures in §2 are what will decide
whether the answer is right.

---

## 2. The measured Koka behaviour — use these as fixtures

Run with `nix shell nixpkgs#koka -c koka -e file.kk` (koka 3.2.2). No flake
change is needed; the sandbox that seemed necessary was not.

**Composition order selects the semantics.** Same body
(`b <- choice(); set(get()+1); (b, get())`), only the nesting swapped:

```
choice(state) = [(False,1),(True,1)]     state INSIDE choice  -> per-branch
state(choice) = [(False,1),(True,2)]     state OUTSIDE choice -> shared
```

Our frame-by-value model reproduces both with no extra machinery, because
whether a resumption gets a fresh copy is exactly whether the cell's frame is
inside the captured segment. Both are `assert_norm` fixtures 26–29, checked
non-vacuous by perturbing each expected value, and both are checked again from
JavaScript through the FFI in `test/js/engine-smoke.mjs`.

**These two figures are what discriminate this design from a cached-pointer
one.** A machine that gave `MParamF` a pointer to a shared heap cell passes
typing, passes `progress`, passes the monad laws, and is faster — and produces
`[(False,1),(True,2)]` for the first line. That is why the var-semantics
theorem earns its place (§5).

**Koka mixes clause kinds, and a `ctl` clause's write to `var` is durable:**

```koka
effect state<a>
  fun get() : a
  fun set( x : a ) : ()
  ctl esc() : ()
-- handler with `ctl esc() { st := 99; resume(()) }`
-- set(7); esc(); get()   ==>   99, not 7
```

The mechanism matters: `var st := init` is declared **outside** `with handler`,
so it sits below the capture line, and a `ctl` clause's body also runs below its
own prompt. The write persists because the cell is below both.

**And a `ctl` clause in the same handler as the `var`, resuming twice, shares
state across strands** — `[(1,1),(10,11)]`, not per-branch.

**Putting the state in an outer handler reproduces the same-handler behaviour
exactly:**

```
A  same handler, ctl writes var directly   = [(False,1),(True,1)]
B  state in a separate outer handler       = [(False,1),(True,1)]
```

So what our design cannot express in one handler, it can express in two, with
identical semantics. The limitation is syntactic, not semantic — and arguably
the two-handler form is the better one, because the nesting order *is* the
choice between shared and per-branch, and folding it into one handler hides it.

**Koka has no third clause kind.** Clause kinds are `fun` / `val` / `ctl` /
`raw ctl` / `return`; state is the orthogonal `var`. This is why the surface
became `var init \s -> handler {...}` rather than a `st` clause: it keeps
clause signatures unchanged, which the PureScript type-level machinery requires
(see §4).

---

## 3. What the machine side will demand, that a reference-only prototype hides

A prototype covering only `Hoop.Runtime.Semantics` verified cleanly and then
missed the two things that turned out to be the work.

**Masking.** While a tail-resumptive clause body is in flight, `erase_k`
absorbs every frame from the `MEnvF` down to its own prompt into a single
`BindF (kont_of captured)`. A `ParamF` among those frames is therefore **absent
from the erased reference stack**, so neither the read nor the write may see it
— both must jump over the masked region exactly as `msplit` does. This is not a
quirk of `MEnvF`; it is forced by the desugaring `Fast c ↦ fun args k -> Op
(afast c args) k`, which really does cut the reference stack there.

Reading over a masked region is cheap (re-run the split, recurse below).
**Writing is the hard half**, because it must come back *up* through a region
whose extent is delimited by a search rather than by a count, so it cannot be
consed back on. It took `mrepl` / `mrepl_agrees` plus `mset_param_agrees` plus
three supporting lemmas.

**Any new frame kind — a borrowed prompt, a scope marker — faces this same
obligation.**

**Environment staleness.** `MEnvF` caches the environment to restore on
completion. A fast clause body that writes a cell *below* its own prompt changes
a cell the perform site can see, so that cached environment goes stale. That is
**not a proof obstacle, it is a wrong answer**; `Hoop.Runtime.Test` fixture 30
is that program. The fix threads the environment through the rebuild so the
`MEnvF` takes its new saved environment from the walk that puts the region back.
The alternative — drop the cache and recompute on return — would make every
tail-resumptive return O(frames between perform site and handler), which is
precisely the walk fast clauses exist to avoid.

---

## 4. Constraints the surface imposes

**Clause signatures must keep the continuation last.** `Hoop.Engine`'s
type-level machinery computes a canonical clause type from the operation
signature and unifies the user's clause against it; the base case of
`FullSignature` appends `Cont b r o` last. Threading a parameter in as an extra
argument would mean carrying the region type through `ClauseFor`,
`MkHandlers`, `CanonicalizeHandlers` and `BuildHandler`. That is why cells are
reached through an opaque region token and type application rather than as a
clause argument.

TS's scoped clause is `(payload, weave, resume) => Computation<B>` — resume
last. Consistent; a scoped clause should fit the existing shape.

**Regions do not nest.** Two open regions put two `"%hoop.var"` entries in the
row, and row matching takes the leftmost, so reading the outer region's cell
from inside the inner one is a type error — *even when the labels do not
collide*. Verified. The workaround is one region with both cells, which
compiles. Worth documenting on the surface; a scoped design that wants nesting
will have to revisit the single reserved row label.

**Escape is prevented by the rank-2 `forall s`, not by row tracking, and it
works because `Region s inits = Region Unit` carries nothing.** There is no
per-cell handle whose type could forget the region. If a future design gives the
token runtime content (see §1 option 1), check this argument again.

---

## 5. The var-semantics theorem, and the test it has to pass

Stated in two parts, as a characterisation **of the reference semantics
itself** — not as a machine/reference property, where `execute_agrees` already
covers it and a reviewer would rightly say so:

- **Locality** — a write changes exactly the target cell: `set_param_local`,
  `set_param_hits`, plus `set_param_handled` / `set_param_param_in` showing no
  prompt and no cell appears, moves or vanishes.
- **Splice fidelity** — `set_param_splice` (a write whose cell is *not* in the
  captured segment passes through into `below`, which is why a `ctl` clause that
  writes then resumes sees the write) and `set_param_captured` (a write whose
  cell *is* in the segment stays there, which is the per-branch half).

The test that a statement of this kind is worth having: **can you describe an
implementation that satisfies everything else and violates it?** Here, yes — the
cached-pointer machine. If no such implementation exists, the statement is too
weak and is being proved by its own encoding. This project has already been
caught by a strong-looking property that held only vacuously (`private` blocking
`friend`, which was true only because nothing could `friend` an
interface-less module at all).

---

## 6. Method, from things that went wrong

Recorded because each cost real time and each will recur.

**Phases that split the reference from the machine do not exist.**
`Hoop.Runtime` pattern-matches `comp_tree` and `frame` exhaustively, so adding a
constructor to either breaks it immediately, and the new cases have content
because frames reach the machine through `Resumed`. A pass scoped as
"reference semantics only" produced 2000 lines of parallel `Hoop.Runtime.Param.*`
modules before the blocker surfaced. **Extend in place, in one pass.**

**Separate constructors beat extra fields**: measured 22 sites versus 94, and
the semantic reason agrees — a var prompt has no clauses and no return clause,
so an `option` field would force every plain prompt to carry `None`.

**"Unreachable code costs nothing" is false in F*.** Adding an inert `ParamF`
moved the bundle by 130 bytes, because F* requires exhaustive matches and four
*extracted* functions gained an arm. The acceptance criterion "the bundle must
not move" was arithmetically impossible and should not have been set.

**Measure before building, and be ready for the measurement to say no.**
Every performance intuition in this period was wrong at least once:

- the pure-body `MEnvF` shortcut, TS's one optimisation we had deferred, buys
  ~19 ns on a pure-body clause and **nothing** on State, because `fast \_ -> read c`
  has a `ReadP` body, not a `Var` one;
- `E.lookup`'s scan is 3.8 ns/level — half a fast perform's per-level cost and
  1/13 of a full one's. The O(1) environment the interface was designed to allow
  is not worth building on this evidence;
- the *write*'s 27 ns/level is not an optimisation target at all. It is the
  price of cells living in frames by value, which is what buys the two Koka
  figures. It cannot be reduced without changing the semantics.

**Benchmark traps, all of which were live:** build with `OPT=1` (Hoop's
`@inline` pragmas are `purs-backend-es`-only, so `OPT=0` measures a
configuration nobody ships); make the program **observe** its result, or
`purs-backend-es` deletes the loop and the series measures nothing; right-nested
binds only; min-of-N, not median; and keep a control series in the same session
— `purescript-run` drifting 7% between arms is what tells you the machine is too
loaded to conclude anything.

---

## 7. Where the performance stands, for context

Same machine, same session, `OPT=1`, whole-process slope:

| | ns/iter |
|---|---|
| TS Hoop, parameterized State | ~137 |
| this runtime, cell State | ~600 (after the string-equality fix) |
| `purescript-run` State | ~185 |
| `transformers` State | ~80 |

Profiling both machines on the same program: TS spends its time in `loop`
(39.5%) and `runMachine` (16.9%) with **no list-walking term at all**; ours
spends 25% in `mstep`, **27.6% walking frame lists**, 8.1% in GC and 6.1% at the
FFI boundary (`caml_call1`, `caml_js_from_array`). Total sampled time for the
same work: 495 ms versus 2873 ms.

So the gap is the representation and the `F* → OCaml → js_of_ocaml` path, not a
single hotspot — the same work in the same proportions, uniformly slower.
Removing the last polymorphic comparison (`FStar_List_Tot_Base.mem`, which was
reaching `caml_compare_val`, whose `caml_compare_val_tag` runs a regular
expression per operand) took 12% off the loop and **37% off the bundle**, and
that was the one genuine defect. The remaining 35.7% attributable to
representation would, if removed entirely, still leave ~3.7x.

**The decision taken: compete on what can be expressed, not on speed.** Deep
handlers, multi-shot continuations, the tail-resumptive fast path, general
higher-order effects and a proved metatheory are not in `Run`'s design space.
Runtime tuning continues opportunistically; it is not the goal.
