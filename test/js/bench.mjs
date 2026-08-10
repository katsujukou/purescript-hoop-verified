// Performance benchmark for src/Hoop/Engine.js.
//
// Run with: node test/js/bench.mjs   (after hoop-build-runtime)
//
// ---------------------------------------------------------------------------
// READ THIS BEFORE CHANGING THE SHAPE OF A PROGRAM HERE
// ---------------------------------------------------------------------------
//
// Bind associativity dominates every other variable in this runtime, and
// getting it wrong silently produces numbers that are wrong by two orders of
// magnitude in a way that still looks self-consistent across a sweep.
//
//   RIGHT-nested   bind(perform, \x -> bind(perform, \y -> ...))
//     is what PureScript's `do` desugars to. At each perform the stack holds
//     roughly one bind frame plus the enclosing prompts, so the captured
//     segment is O(nesting).
//
//   LEFT-nested    bind(bind(bind(pure, f), f), f)
//     pushes one frame per remaining bind before reaching the innermost
//     computation, so the captured segment is O(program length) and capture
//     swamps everything else. Measured at 471 us/perform against 1 us/perform
//     for the same work right-nested.
//
// A left-nested sweep was used once here by mistake. It reported a cost that
// was flat in every parameter -- which reads as "nothing matters" rather than
// as "the benchmark is broken". Build programs with `nest` below.
//
// ---------------------------------------------------------------------------
// The parameters, and what each one isolates
// ---------------------------------------------------------------------------
//
//   N  nesting: handlers between the perform site and the one that catches it.
//   E  effects declared by each of those handlers.
//   W  operations declared by each of those effects.
//
// Env.lookup walks N levels and, at each, tests membership. Since the two-level
// keyset landed, that test costs O(E) rather than O(E*W) -- so a sweep in W
// should be flat and a sweep in E should be linear. If a change makes the W
// sweep grow again, the effect-grouping has been lost somewhere.
//
// N drives BOTH the number of levels Env.lookup walks AND the length of the
// continuation segment the machine captures. Those two cannot be separated by
// varying N alone. The way to separate them is sweep (1b) below: the same
// N-sweep against a tail-resumptive (fast) clause. A fast clause body runs in
// place -- nothing is captured, the stack is not cut -- so capture, split and
// reinstall all disappear from the per-perform cost and what remains is
// Env.lookup plus ordinary machine steps. Whatever slope survives in (1b) is
// the lookup's; whatever (1a) has on top of it is the capture's.
//
//   D  depth: environment levels between a prompt-local cell access and the
//      cell itself. Sweep (5).
//
// D is the cell counterpart of N, and it exists because a cell IS a level of
// the same environment: `newCell` extends it exactly as a handler does, and a
// read is one `Env.lookup`. The shipped realisation of `lookup` is a scan of
// levels, so a read is linear in the prompts AND cells between the access and
// the cell -- not O(1). The Env interface admits an O(1) realisation with no
// proof changing, and sweep (5) is what says whether building one would be
// worth the trouble. Read against (1a) and (1b): if a read's slope is far
// below a full clause's, the scan is not what a program pays for.

import {
  pureImpl as pure, bindImpl as bind, performImpl, withImpl, runImpl,
  newCellImpl as newCell, readCellImpl as readCell, writeCellImpl as writeCell,
  undefinedReturnImpl as noRet, emptyHandlersImpl, insertClauseImpl, insertClausesImpl,
} from '../../src/Hoop/Engine.js'

const PERFORMS = 20000
const perform = (eff, op, ...args) => performImpl(eff, op, null, args)

function table(spec) {
  let hs = emptyHandlersImpl(null)
  for (const [eff, ops] of Object.entries(spec)) {
    let clauses = emptyHandlersImpl(null)
    for (const [op, cl] of Object.entries(ops)) clauses = insertClauseImpl(op, cl, clauses)
    hs = insertClausesImpl(eff, clauses, hs)
  }
  return hs
}

const resumeNull = (_payload, k) => k(null)

// A handler declaring E effects of W operations, none of them the target.
// Effect names are indexed by `i` so no two levels declare the same effect.
const filler = (E, W, i) => {
  const spec = {}
  for (let a = 0; a < E; a++) {
    const ops = {}
    for (let b = 0; b < W; b++) ops['nop' + b] = resumeNull
    spec[`e${i}_${a}`] = ops
  }
  return table(spec)
}

// The two shapes of the caught clause. A full (ctl) clause is a bare function
// taking the payload and the machine's resume; a tail-resumptive (fast) one is
// the object { fun }, whose body's value *is* the operation's result and which
// is therefore never handed a continuation. hoop_ffi.ml reads the tag off these
// shapes when the table is built.
const ctlOne = (_payload, k) => k(1)
const fastOne = { fun: (_payload) => pure(1) }

// The handler that catches: effect `reader`, operation `ask` at position `pos`
// among W-1 others, so the cost of a hit inside the matching effect is visible.
const target = (W, pos, ask = ctlOne) => {
  const ops = {}
  for (let b = 0; b < W - 1; b++) ops['nop' + b] = resumeNull
  const names = Object.keys(ops)
  const out = {}
  for (const n of names.slice(0, pos)) out[n] = ops[n]
  out['ask'] = ask
  for (const n of names.slice(pos)) out[n] = ops[n]
  return table({ reader: out })
}

// PERFORMS right-nested `ask`s summing their results. Built as a chain of
// closures so that no JS recursion is needed to construct it.
function nest(n) {
  let k = (acc) => pure(acc)
  for (let i = 0; i < n; i++) {
    const prev = k
    k = (acc) => bind(perform('reader', 'ask'), (v) => prev(acc + v))
  }
  return k(0)
}

// ns per perform.
function measure(N, E, W, tgt) {
  const fillers = []
  for (let i = 0; i < N; i++) fillers.push(filler(E, W, i))
  let prog = nest(PERFORMS)
  for (let i = 0; i < N; i++) prog = withImpl(noRet, fillers[i], prog)
  const t0 = performance.now()
  const result = runImpl(withImpl(noRet, tgt, prog))
  const ms = performance.now() - t0
  if (result !== PERFORMS) throw new Error(`wrong result ${result}, expected ${PERFORMS}`)
  return (ms * 1e6) / PERFORMS
}

// ---------------------------------------------------------------------------
// Statistics: report MIN, and print the median beside it so the spread is
// visible. Do not quote a single number from this benchmark without the spread.
//
// A capture at nesting N allocates N frames, so one measurement at N=50 churns
// about a million of them and the result depends on when the collector happens
// to run. Measured across independent processes, a median of 3 varies by a
// factor of two at N=10 and by four at N=50 -- enough to invent a slope that
// is not there. An earlier baseline of "700 + 81N ns" was quoted from exactly
// such a run; the slope survived re-measurement but the individual points did
// not, and the fit should never have been stated to that precision.
//
// Min is the right estimator here: every perturbation (GC, scheduling, another
// build running) adds time, so the fastest run is the one least perturbed.
// Even so, expect min to move by ~15% at N=50 and ~25% at N=10 between
// processes. Treat differences under ~1.5x as unresolved.
//
// Run under `node --expose-gc` to collect between repetitions, which tightens
// the spread noticeably. Without it the harness still works, just noisier.
const REPS = 9

function best(f) {
  const xs = []
  for (let i = 0; i < REPS; i++) {
    if (global.gc) { global.gc(); global.gc() }
    xs.push(f())
  }
  xs.sort((a, b) => a - b)
  return { min: xs[0], med: xs[REPS >> 1] }
}

const row = (label, r) =>
  console.log(`      ${label.padEnd(22)} ${r.min.toFixed(0).padStart(8)} ${('(med ' + r.med.toFixed(0) + ')').padStart(12)}`)

measure(5, 1, 1, target(1, 0)) // warm up

console.log(`\nns per perform: MIN of ${REPS}, median beside it. ${PERFORMS} right-nested performs.`)
console.log(global.gc ? '(--expose-gc active)' : '(no --expose-gc: rerun under `node --expose-gc` for a tighter spread)')
console.log()

// The pair of sweeps the parameter section above is about. E and W held at 1 so
// that only N -- levels walked, and segment captured -- varies. (1a) pays for
// both; (1b) pays for the lookup alone.
console.log('  (1a) N sweep, E=1 W=1, full (ctl) clause')
for (const N of [1, 2, 5, 10, 20, 50]) row(`N=${N}`, best(() => measure(N, 1, 1, target(1, 0))))

console.log('\n  (1b) N sweep, E=1 W=1, tail-resumptive (fast) clause')
for (const N of [1, 2, 5, 10, 20, 50])
  row(`N=${N}`, best(() => measure(N, 1, 1, target(1, 0, fastOne))))

console.log('\n  (2) W sweep at N=20, E=1 -- should be FLAT (effect-grouped keyset)')
for (const W of [1, 5, 10, 50, 200]) row(`W=${W}`, best(() => measure(20, 1, W, target(1, 0))))

console.log('\n  (3) E sweep at N=20, W=1 -- linear; E is the remaining per-level term')
for (const E of [1, 5, 10, 50]) row(`E=${E}`, best(() => measure(20, E, 1, target(1, 0))))

console.log('\n  (4) position of the caught operation within its own effect')
for (const W of [10, 50, 200]) {
  const at = (p) => best(() => measure(20, 1, 1, target(W, p))).min.toFixed(0).padStart(7)
  console.log(`      W=${String(W).padEnd(18)} head ${at(0)}  mid ${at(W >> 1)}  tail ${at(W - 1)}`)
}

// ---------------------------------------------------------------------------
// (5) Prompt-local cells
// ---------------------------------------------------------------------------
//
// The shape is the same as the perform sweeps: PERFORMS right-nested accesses,
// with D levels between them and the cell. Read the numbers against (1a) and
// (1b), which are the same harness on the same machine.
//
// Both a handler and a cell push exactly one environment level, so the sweep is
// run twice -- filler prompts, then filler cells. The walk is the same length
// either way; what differs is the per-level work, since a prompt's level tests
// membership against a keyset while a cell's holds one name. The gap between
// (5a) and (5b) is that difference, nothing else.
//
// A read is one Env.lookup and stops there: no capture, no split, no rebuild.
// A write is the expensive one BY CONSTRUCTION, and not incidentally: because
// the cell lives in a frame by value, a write has to rebuild the stack down to
// that frame and the environment down to that level -- twice O(D), allocating
// as it goes. That is the price of the read being one lookup, and of a captured
// continuation carrying its own copy. Expect the write's slope to dominate.

const CELL = '$bench'

// Right-nested accesses summing what they yield. A read yields the cell's value
// and a write yields the value written (the machine's WriteP rule steps to
// `Var y`), so both sum to PERFORMS with the cell holding 1.
function nestAccess(n, access) {
  let k = (acc) => pure(acc)
  for (let i = 0; i < n; i++) {
    const prev = k
    k = (acc) => bind(access(), (v) => prev(acc + v))
  }
  return k(0)
}

const readAccess = () => readCell(CELL)
const writeAccess = () => writeCell(CELL, 1)
// The floor: the same chain of binds with no cell operation in it at all, so
// that the intercepts below can be read as a cost over ordinary machine steps
// rather than as an absolute.
const noAccess = () => pure(1)

const promptsBetween = (prog, D) => {
  for (let i = 0; i < D; i++) prog = withImpl(noRet, filler(1, 1, i), prog)
  return prog
}
const cellsBetween = (prog, D) => {
  for (let i = 0; i < D; i++) prog = newCell('c' + i, 0, prog)
  return prog
}

// ns per access.
function measureCell(D, access, between) {
  const prog = newCell(CELL, 1, between(nestAccess(PERFORMS, access), D))
  const t0 = performance.now()
  const result = runImpl(prog)
  const ms = performance.now() - t0
  if (result !== PERFORMS) throw new Error(`wrong result ${result}, expected ${PERFORMS}`)
  return (ms * 1e6) / PERFORMS
}

const DS = [0, 1, 2, 5, 10, 20, 50]

console.log('\n  (5a) D sweep: cell READ, D filler PROMPTS between access and cell')
for (const D of DS) row(`D=${D}`, best(() => measureCell(D, readAccess, promptsBetween)))

console.log('\n  (5b) D sweep: cell READ, D filler CELLS between access and cell')
for (const D of DS) row(`D=${D}`, best(() => measureCell(D, readAccess, cellsBetween)))

console.log('\n  (5c) D sweep: cell WRITE, D filler PROMPTS -- rebuilds stack and env')
for (const D of DS) row(`D=${D}`, best(() => measureCell(D, writeAccess, promptsBetween)))

console.log('\n  (5d) D sweep: cell WRITE, D filler CELLS')
for (const D of DS) row(`D=${D}`, best(() => measureCell(D, writeAccess, cellsBetween)))

console.log('\n  (5e) floor: the same chain with no cell operation, D filler prompts')
for (const D of DS) row(`D=${D}`, best(() => measureCell(D, noAccess, promptsBetween)))

// Handler table construction: withImpl runs handlers_of_js and mk_handlers
// eagerly, so this is the whole per-installation cost. Needed to judge any
// proposal that moves work from lookup to installation.
console.log('\n  ns per handler installation (withImpl)')
for (const [E, W] of [[1, 1], [1, 10], [1, 200], [10, 10]]) {
  const hs = filler(E, W, 0)
  const body = pure(0)
  for (let i = 0; i < 2000; i++) withImpl(noRet, hs, body)
  row(`E=${E} W=${W}`, best(() => {
    const t0 = performance.now()
    for (let i = 0; i < PERFORMS; i++) withImpl(noRet, hs, body)
    return ((performance.now() - t0) * 1e6) / PERFORMS
  }))
}
console.log()
