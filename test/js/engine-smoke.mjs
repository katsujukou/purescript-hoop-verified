// Smoke tests for the FFI boundary in src/Hoop/Engine.js.
//
// These sit below the PureScript surface on purpose. test/Hoop.purs exercises
// the typed API and can only construct handler tables the type checker permits;
// what is checked here is the other half -- the handwritten boundary in
// runtime/ml/melange/hoop_ffi.ml and runtime/ml/melange/hoop_prim.js, which is
// part of the TCB and which no F* proof
// covers. Hence the awkward inputs: a `__proto__` effect label, a nullish
// return clause, a clause of neither recognised shape, an unhandled operation.
//
// The fast-clause section is here for the same reason. Whether a clause reaches
// the machine tagged Full or Fast is decided by the boundary alone, from the JS
// shape the builders produce; F* proves what each tag then means, but nothing
// proves the tag was read off correctly.
//
// The prompt-local cell section likewise. F* proves what NewP / ReadP / WriteP
// mean and runtime/Hoop.Runtime.Test.fst pins the answers by assert_norm, but
// nothing proves that the boundary builds those nodes rather than three others,
// and nothing there runs through Melange. The two Koka figures at the end of
// that section are the sharpest instrument in this file: a runtime that held a
// cell behind a shared mutable box would agree with every other test here and
// disagree with exactly those two.
//
// Run with: node test/js/engine-smoke.mjs   (after hoop-build-runtime)

import {
  pureImpl, bindImpl, performImpl, withImpl, runImpl,
  newCellImpl, readCellImpl, writeCellImpl,
  mkFullClauseImpl, mkFastClauseImpl, mkReturnImpl, undefinedReturnImpl,
  emptyClausesImpl, emptyHandlersImpl, insertClauseImpl, insertClausesImpl,
} from '../../src/Hoop/Engine.js'

let passed = 0
const failures = []

function check(name, fn) {
  try {
    fn()
    passed++
  } catch (e) {
    failures.push([name, e])
  }
}

function eq(actual, expected, what = '') {
  const a = JSON.stringify(actual), b = JSON.stringify(expected)
  if (a !== b) throw new Error(`${what}expected ${b}, got ${a}`)
}

function throws(fn, pattern, what = '') {
  let threw = null
  try { fn() } catch (e) { threw = e }
  if (threw === null) throw new Error(`${what}expected a throw, got none`)
  if (!pattern.test(String(threw.message ?? threw)))
    throw new Error(`${what}message ${JSON.stringify(String(threw.message ?? threw))} does not match ${pattern}`)
}

// --- helpers ---------------------------------------------------------------

const pure = pureImpl
const bind = (c, f) => bindImpl(c, f)
const perform = (eff, op, ...args) => performImpl(eff, op, null, args)

// Prompt-local cells. `label` is the string a PureScript `new` would mint; it
// names a binder, not a location, so these are spelled out at their arities
// rather than aliased, to keep the uncurried convention visible.
const newCell = (label, init, body) => newCellImpl(label, init, body)
const readCell = (label) => readCellImpl(label)
const writeCell = (label, value) => writeCellImpl(label, value)

// A handler table { [eff]: { [op]: clause } }, built through the same record
// builders PureScript uses rather than with object literals -- the builders are
// what ships, so they are what should be under test.
function table(spec) {
  let hs = emptyHandlersImpl(null)
  for (const [eff, ops] of Object.entries(spec)) {
    let clauses = emptyClausesImpl(null)
    for (const [op, cl] of Object.entries(ops)) clauses = insertClauseImpl(op, cl, clauses)
    hs = insertClausesImpl(eff, clauses, hs)
  }
  return hs
}

// The machine's own clause shape: (payloadArray, resume) => comp.
const ctl = (f) => f

// --- construction and running ----------------------------------------------

check('pure runs to its value', () => {
  eq(runImpl(pure(42)), 42)
})

check('bind sequences', () => {
  eq(runImpl(bind(pure(1), (x) => pure(x + 1))), 2)
})

check('bind is left-associative-safe over a chain', () => {
  let c = pure(0)
  for (let i = 0; i < 100; i++) c = bind(c, (x) => pure(x + 1))
  eq(runImpl(c), 100)
})

check('a value passes through unchanged, preserving identity', () => {
  const sentinel = { tag: 'sentinel' }
  if (runImpl(pure(sentinel)) !== sentinel) throw new Error('identity not preserved')
})

check('null and undefined survive as values', () => {
  eq(runImpl(pure(null)), null)
  if (runImpl(pure(undefined)) !== undefined) throw new Error('undefined not preserved')
})

// --- handlers --------------------------------------------------------------

check('perform reaches its clause', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(7)) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('reader', 'ask'))), 7)
})

check('a deep handler survives resumption', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(7)) } })
  const prog = bind(perform('reader', 'ask'), (a) =>
    bind(perform('reader', 'ask'), (b) => pure(a + b)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 14)
})

check('a discarded continuation abandons the rest', () => {
  const h = table({ exc: { throw: ctl(([msg], _k) => pure(`caught: ${msg}`)) } })
  const prog = bind(perform('exc', 'throw', 'boom'), () => pure('unreachable'))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 'caught: boom')
})

check('a continuation resumed twice really runs twice', () => {
  const h = table({
    amb: { flip: ctl((_p, k) => bind(k(true), (xs) => bind(k(false), (ys) => pure(xs.concat(ys))))) },
  })
  const ret = mkReturnImpl((v) => [v])
  eq(runImpl(withImpl(ret, h, bind(perform('amb', 'flip'), (b) => pure(b ? 1 : 2)))), [1, 2])
})

check('the payload arrives as an array of the operation arity', () => {
  const h = table({ st: { set: ctl((p, k) => k(p)) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'set', 1, 'two', null))), [1, 'two', null])
})

check('a zero-argument operation gets an empty payload', () => {
  const h = table({ st: { get: ctl((p, k) => k(p.length)) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'get'))), 0)
})

check('the return clause applies at the end', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  const ret = mkReturnImpl((v) => v * 10)
  eq(runImpl(withImpl(ret, h, perform('reader', 'ask'))), 10)
})

check('a nullish return clause means the identity', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  for (const r of [undefinedReturnImpl, null, undefined])
    eq(runImpl(withImpl(r, h, perform('reader', 'ask'))), 1)
})

check('an uncovered operation escapes to the outer handler', () => {
  const inner = table({ exc: { throw: ctl((_p, k) => k(0)) } })
  const outer = table({ reader: { ask: ctl((_p, k) => k(5)) } })
  const prog = withImpl(undefinedReturnImpl, inner, perform('reader', 'ask'))
  eq(runImpl(withImpl(undefinedReturnImpl, outer, prog)), 5)
})

check('the innermost handler of the same effect wins', () => {
  const outer = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  const inner = table({ reader: { ask: ctl((_p, k) => k(2)) } })
  const prog = withImpl(undefinedReturnImpl, inner, perform('reader', 'ask'))
  eq(runImpl(withImpl(undefinedReturnImpl, outer, prog)), 2)
})

check("a clause's own perform resolves outside its own prompt", () => {
  const outer = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  const inner = table({ reader: { ask: ctl((_p, k) => bind(perform('reader', 'ask'), (n) => k(n * 10))) } })
  const prog = withImpl(undefinedReturnImpl, inner, perform('reader', 'ask'))
  eq(runImpl(withImpl(undefinedReturnImpl, outer, prog)), 10)
})

// --- tail-resumptive (fast) clauses ----------------------------------------
//
// A fast clause is not handed the continuation. Its body runs *in place* --
// nothing is captured and the stack is not cut -- under the environment its own
// handler was installed in, and the body's value is the operation's result.
//
// These mirror fixtures 20-25 of runtime/Hoop.Runtime.Test.fst, which check the
// same situations against the reference machine inside F*. What is exercised
// here and not there is the FFI's half of the arrangement: `handlers_of_js`
// tagging each entry Full or Fast from its JS shape. Get that wrong and every
// one of these still type-checks on the PureScript side.

// The machine's own fast-clause shape, the analogue of `ctl` above: the object
// { fun }, with fun : (payload[]) => comp. `mkFastClauseImpl` builds one of
// these from a curried PureScript handler; it is tested with the builders.
const fast = (f) => ({ fun: f })

check('a fast clause dispatches and resumes in place', () => {
  const h = table({ reader: { ask: fast(() => pure(42)) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('reader', 'ask'))), 42)
})

check('a fast clause receives the payload as an array', () => {
  const h = table({ st: { set: fast((p) => pure(p)) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'set', 1, 'two', null))),
    [1, 'two', null])
})

check('deep semantics: a second perform after a fast clause resumes', () => {
  const h = table({ reader: { ask: fast(() => pure(7)) } })
  const prog = bind(perform('reader', 'ask'), (a) =>
    bind(perform('reader', 'ask'), (b) => pure(a + b)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 14)
})

check('the return clause still applies after a fast clause', () => {
  const h = table({ reader: { ask: fast(() => pure(1)) } })
  eq(runImpl(withImpl(mkReturnImpl((v) => v * 10), h, perform('reader', 'ask'))), 10)
})

// Masking, which is what the machine's MEnvF frame carries a saved environment
// for. `log.emit`'s fast body performs `reader.ask`. Between the perform site
// and the `log` prompt sits a NEARER `reader` handler, and the body must not see
// it: a tail-resumptive clause runs in the context its handler was installed in.
// 1005, not 1100.
check('a fast body sees its handler\'s context, not the perform site\'s', () => {
  const outerReader = table({ reader: { ask: fast(() => pure(5)) } })
  const log = table({
    log: { emit: fast(() => bind(perform('reader', 'ask'), (r) => pure(r + 1000))) },
  })
  const nearerReader = table({ reader: { ask: fast(() => pure(100)) } })
  const prog =
    withImpl(undefinedReturnImpl, outerReader,
      withImpl(undefinedReturnImpl, log,
        withImpl(undefinedReturnImpl, nearerReader, perform('log', 'emit'))))
  eq(runImpl(prog), 1005)
})

// Capture across a fast body, and multi-shot through it. `log.emit`'s fast body
// performs `amb.flip`, whose clause is FULL and resumes twice, so the split has
// to jump over the region the fast body masks and hand the clause a segment in
// which that region has become the single bind frame the reference machine has
// there. Nothing is reinstalled as a fast body on either resumption -- which is
// what makes the second one safe.
check('a full clause captures across a fast body, twice', () => {
  const amb = table({
    amb: { flip: ctl((_p, k) => bind(k(1), (x) => bind(k(2), (y) => pure(x + y)))) },
  })
  const log = table({ log: { emit: fast(() => perform('amb', 'flip')) } })
  const prog =
    withImpl(undefinedReturnImpl, amb,
      withImpl(undefinedReturnImpl, log,
        bind(perform('log', 'emit'), (r) => pure(r + 100))))
  eq(runImpl(prog), 203)
})

check('full and fast clauses mix in one handler table', () => {
  const h = table({
    st: { get: fast(() => pure(10)), set: ctl(([v], k) => k(v * 2)) },
  })
  const prog = bind(perform('st', 'get'), (a) =>
    bind(perform('st', 'set', 5), (b) => pure(a + b)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 20)
})

check('a full clause that drops the continuation does so from under a fast one', () => {
  const exc = table({ exc: { throw: ctl(([m], _k) => pure(`caught: ${m}`)) } })
  const echo = table({ echo: { say: fast(([s]) => pure(s)) } })
  const prog =
    withImpl(undefinedReturnImpl, exc,
      withImpl(mkReturnImpl(() => 'should not run'), echo,
        bind(perform('echo', 'say', 'hello'), (s) =>
          bind(perform('exc', 'throw', s), () => pure('unreachable')))))
  eq(runImpl(prog), 'caught: hello')
})

check('an unhandled operation inside a fast body still reports Stuck', () => {
  const h = table({
    log: { emit: fast(() => bind(perform('nope', 'missing'), (x) => pure(x))) },
  })
  throws(() => runImpl(withImpl(undefinedReturnImpl, h, perform('log', 'emit'))),
    /Unhandled effect operation 'nope\.missing'/)
})

// The same masking as above, in its negative form: an operation handled only
// between the perform site and the fast clause's own prompt is out of the body's
// reach entirely, not merely shadowed.
check('a fast body cannot reach a handler installed inside its own prompt', () => {
  const log = table({
    log: { emit: fast(() => bind(perform('reader', 'ask'), (r) => pure(r))) },
  })
  const nearerReader = table({ reader: { ask: fast(() => pure(1)) } })
  const prog =
    withImpl(undefinedReturnImpl, log,
      withImpl(undefinedReturnImpl, nearerReader, perform('log', 'emit')))
  throws(() => runImpl(prog), /Unhandled effect operation 'reader\.ask'/)
})

// --- prompt-local cells ----------------------------------------------------
//
// `newCell` installs a cell for the duration of a computation; `readCell` and
// `writeCell` reach the NEAREST enclosing cell of that label. There is no
// mutable box and no pointer: the cell lives in a stack frame BY VALUE, so a
// write rebuilds the frame and a captured continuation carries the value it was
// captured with. That is the whole design, and everything below is a
// consequence of it.
//
// These mirror fixtures 26-30 of runtime/Hoop.Runtime.Test.fst. What is checked
// here and not there is that the boundary builds the right node with the right
// arguments -- three `magic`-crossing constructors that no type checker on
// either side of the boundary can see through.

check('a cell installs, reads, writes and reads again', () => {
  // Also pins that a write EVALUATES TO the value written: the machine's
  // WriteP rule steps to `Var y`, not to unit.
  const prog = newCell('c', 1,
    bind(readCell('c'), (a) =>
      bind(writeCell('c', 5), (w) =>
        bind(readCell('c'), (b) => pure([a, w, b])))))
  eq(runImpl(prog), [1, 5, 5])
})

check('a cell holds an opaque value by identity', () => {
  const sentinel = { tag: 'sentinel' }
  if (runImpl(newCell('c', sentinel, readCell('c'))) !== sentinel)
    throw new Error('identity not preserved through a cell')
})

check('the value of a new is the value of its body', () => {
  eq(runImpl(newCell('c', 1, pure('body'))), 'body')
})

// The cell is installed INSIDE the handler's prompt, so the segment the clause
// captures contains its frame and the resumption reinstalls it. Nothing about
// the cell survives the perform by accident: it survives because the frame does.
check('a cell survives a perform that reaches an outer handler and resumes', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(7)) } })
  const prog = withImpl(undefinedReturnImpl, h,
    newCell('c', 1,
      bind(readCell('c'), (a) =>
        bind(perform('reader', 'ask'), (r) =>
          bind(writeCell('c', a + r), () =>
            bind(readCell('c'), (b) => pure([a, r, b])))))))
  eq(runImpl(prog), [1, 7, 8])
})

check('nested cells with distinct labels do not interfere', () => {
  const prog = newCell('a', 1, newCell('b', 2,
    bind(writeCell('a', 10), () =>
      bind(readCell('b'), (y) =>
        bind(readCell('a'), (x) => pure([x, y]))))))
  eq(runImpl(prog), [10, 2])
})

// The model's rule is innermost-wins, in `Hoop.Runtime.Semantics.find_param`
// (and, on the machine that ships, in the shadowing of one environment level by
// another). Pinned here so that a future change to either cannot alter it
// silently: the inner write must land on the inner cell and leave the outer one
// at the value it had.
check('the innermost cell of a repeated label wins, and shadowing is total', () => {
  const prog = newCell('c', 1,
    bind(readCell('c'), (before) =>
      bind(newCell('c', 2, bind(writeCell('c', 20), () => readCell('c'))), (inner) =>
        bind(readCell('c'), (after) => pure([before, inner, after])))))
  eq(runImpl(prog), [1, 20, 1])
})

// --- cells out of scope ------------------------------------------------------
//
// The machine reports a cell miss as MStuck under the reserved effect name
// `%hoop.var`, which the generic branch of run_impl would spell as
// "Unhandled effect operation '%hoop.var.c'" -- accurate and useless.
// the boundary special-cases it. The message may assert whose fault it is:
// `Hoop.Runtime.execute`'s postcondition is unconditional, so an MStuck means
// the reference machine is stuck on the same program.

const escaped = /prompt-local cell '(.*)' was read or written outside the scope/

check('reading a cell that was never installed reports an escape', () => {
  throws(() => runImpl(readCell('c')), escaped)
  throws(() => runImpl(bind(readCell('c'), (x) => pure(x))), escaped)
})

check('writing a cell that was never installed reports an escape', () => {
  throws(() => runImpl(writeCell('c', 1)), escaped)
})

check('the escape message names the cell, not the reserved effect', () => {
  throws(() => runImpl(readCell('someLabel')), /cell 'someLabel'/)
  // The generic wording must NOT be what surfaces.
  let msg = ''
  try { runImpl(readCell('someLabel')) } catch (e) { msg = String(e.message) }
  if (/Unhandled effect operation/.test(msg))
    throw new Error(`the generic message leaked: ${JSON.stringify(msg)}`)
  if (/%hoop\.var/.test(msg))
    throw new Error(`the reserved effect name leaked: ${JSON.stringify(msg)}`)
})

// A genuine escape, which is the failure mode the message is written for. The
// handler is installed OUTSIDE the cell, so the capture cuts below the cell's
// frame and hands the clause a segment that contains it; the clause body itself
// then runs beneath the `new`, where the cell no longer exists.
check('a clause body below the new cannot reach the cell above it', () => {
  const esc = table({ esc: { go: ctl((_p, _k) => readCell('c')) } })
  const prog = withImpl(undefinedReturnImpl, esc, newCell('c', 1, perform('esc', 'go')))
  throws(() => runImpl(prog), escaped)
})

// --- cells and tail-resumptive clauses ---------------------------------------
//
// The hard case the F* work identified. While a fast clause body is in flight
// the machine has an MEnvF frame caching the environment the handler was
// installed under, and the frames between it and its own prompt are masked. A
// cell BELOW the prompt is therefore reached only by jumping over that region --
// and a write to it has to come back up through the region and rebuild the
// cached environment on the way, or the cache goes stale. Not a proof obstacle;
// a wrong answer.

check('a fast body reaches a cell below its own prompt, and writes it', () => {
  // runtime/Hoop.Runtime.Test.fst fixture 30, through the FFI. The body reads
  // 10 and writes 11; the continuation reads 11 back through frames the machine
  // never took apart.
  const log = table({
    log: { emit: fast(() => bind(readCell('s'), (n) => bind(writeCell('s', n + 1), () => pure(n)))) },
  })
  const prog = newCell('s', 10,
    withImpl(undefinedReturnImpl, log,
      bind(perform('log', 'emit'), (r) =>
        bind(readCell('s'), (n) => pure([r, n])))))
  eq(runImpl(prog), [10, 11])
})

// The same, with a NEARER cell of the SAME label between the perform site and
// the fast clause's own prompt. A tail-resumptive body runs in the context its
// handler was installed in, so it must read and write the OUTER cell and leave
// the nearer one alone -- 10 and 11, not 100 and 101. This is the cell analogue
// of the masking test above, and it is where a cached-pointer cell would be
// caught: it would find the nearer one.
check('a fast body sees the cell its handler was installed under', () => {
  const log = table({
    log: { emit: fast(() => bind(readCell('s'), (n) => bind(writeCell('s', n + 1), () => pure(n)))) },
  })
  const prog = newCell('s', 10,
    bind(withImpl(undefinedReturnImpl, log,
      newCell('s', 100,
        bind(perform('log', 'emit'), (r) =>
          bind(readCell('s'), (inner) => pure([r, inner]))))),
      (pair) => bind(readCell('s'), (outer) => pure(pair.concat([outer])))))
  eq(runImpl(prog), [10, 100, 11])
})

// The negative form: a cell that exists only inside the fast clause's own
// prompt is out of the body's reach entirely, not merely shadowed.
check('a fast body cannot reach a cell installed inside its own prompt', () => {
  const log = table({ log: { emit: fast(() => readCell('s')) } })
  const prog = withImpl(undefinedReturnImpl, log, newCell('s', 5, perform('log', 'emit')))
  throws(() => runImpl(prog), escaped)
})

// --- the two Koka 3.2.2 figures ----------------------------------------------
//
// One program --
//
//     b <- flip; write (read + 1); (b, read)
//
// -- and only the nesting swapped. Measured against Koka 3.2.2:
//
//     choice(state) = [(False,1),(True,1)]   -- state installed INSIDE choice
//     state(choice) = [(False,1),(True,2)]   -- state installed OUTSIDE choice
//
// The mechanism is where the cell's frame ends up relative to the prompt the
// `choice` clause captures at. Installed inside, the cell is part of the
// captured segment, so every resumption reinstalls it at the value it was
// captured with and each branch counts from 0. Installed outside, it lies below
// the cut, the capture does not carry it, and the first branch's write is still
// there when the second runs.
//
// A runtime holding the cell behind a shared mutable box would give
// [(False,1),(True,2)] for BOTH, and pass every other test in this file while
// doing so. These are fixtures 26-29 in runtime/Hoop.Runtime.Test.fst; the point
// of running them here is that this is the independent path -- through the
// handwritten FFI, the extracted machine and Melange, none of which the
// assert_norms exercise.

// `choice.flip` resumes once with false and once with true and pairs the two
// results, exactly as CBoth does in the F* fixtures. No return clause, so a
// branch's raw value is what the clause collects.
const choice = table({
  choice: { flip: ctl((_p, k) => bind(k(false), (r1) => bind(k(true), (r2) => pure([r1, r2])))) },
})

const sbody =
  bind(perform('choice', 'flip'), (b) =>
    bind(readCell('s'), (n) =>
      bind(writeCell('s', n + 1), () =>
        bind(readCell('s'), (n2) => pure([b, n2])))))

check('choice(state): a cell inside the choice handler is per-branch', () => {
  const prog = withImpl(undefinedReturnImpl, choice, newCell('s', 0, sbody))
  eq(runImpl(prog), [[false, 1], [true, 1]])
})

check('state(choice): a cell outside the choice handler is shared', () => {
  const prog = newCell('s', 0, withImpl(undefinedReturnImpl, choice, sbody))
  eq(runImpl(prog), [[false, 1], [true, 2]])
})

// --- awkward cell labels -----------------------------------------------------

// A cell key and an operation key are different constructors of
// Hoop.Runtime.Handlers.key, so a cell labelled `s` and an effect labelled `s`
// bind different keys in the same environment and cannot shadow one another.
check('a cell label cannot collide with an effect label', () => {
  const h = table({ s: { ask: ctl((_p, k) => k(99)) } })
  const prog = withImpl(undefinedReturnImpl, h,
    newCell('s', 1, bind(perform('s', 'ask'), (v) => bind(readCell('s'), (c) => pure([v, c])))))
  eq(runImpl(prog), [99, 1])
})

// Nothing keys a JS object by a cell label -- every table a VarKey reaches is an
// association list -- so `__proto__` is an ordinary label here. Checked anyway,
// because the label crosses the boundary as a JS string and the guarantee is a
// property of the extracted code rather than of this file.
check('__proto__, unicode and empty strings work as cell labels', () => {
  eq(runImpl(newCell('__proto__', 1, bind(writeCell('__proto__', 2), () => readCell('__proto__')))), 2)
  const prog = newCell('状態', 1, newCell('', 2,
    bind(readCell('状態'), (a) => bind(readCell(''), (b) => pure([a, b])))))
  eq(runImpl(prog), [1, 2])
})

// --- dispatch --------------------------------------------------------------

check('dispatch distinguishes operations within one effect', () => {
  const h = table({ st: { get: ctl((_p, k) => k(5)), set: ctl((_p, k) => k(null)) } })
  const prog = bind(perform('st', 'set', 99), () => bind(perform('st', 'get'), (n) => pure(n * 2)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 10)
})

check('dispatch distinguishes effects sharing an operation name', () => {
  const h = table({ a: { run: ctl((_p, k) => k('a')) }, b: { run: ctl((_p, k) => k('b')) } })
  const prog = bind(perform('a', 'run'), (x) => bind(perform('b', 'run'), (y) => pure(x + y)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 'ab')
})

// --- the awkward inputs ----------------------------------------------------

check('an unhandled operation throws, naming it', () => {
  throws(() => runImpl(perform('reader', 'ask')), /Unhandled effect operation 'reader\.ask'/)
})

check('an effect handled at the wrong operation is still unhandled', () => {
  const h = table({ st: { get: ctl((_p, k) => k(1)) } })
  throws(() => runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'put', 1))),
    /Unhandled effect operation 'st\.put'/)
})

// A clause is tagged Full or Fast from its JS shape when the table is built, so
// anything that is neither shape is caught at `with` -- by name, and before the
// machine could fail on it as an opaque "is not a function" from inside a call.
check('a clause that is neither shape is rejected, naming it', () => {
  for (const bad of [42, null, undefined, {}, { fun: 7 }, 'nope', []]) {
    const h = table({ reader: { ask: bad } })
    throws(() => runImpl(withImpl(undefinedReturnImpl, h, perform('reader', 'ask'))),
      /clause for 'reader\.ask' is neither/,
      `${JSON.stringify(bad) ?? String(bad)}: `)
  }
})

// The reason emptyHandlersImpl uses Object.create(null): on an ordinary {},
// `rec["__proto__"] = v` invokes the inherited setter and reassigns the
// prototype instead of storing an own property, so a handler for an effect
// named __proto__ would silently vanish from the table.
// Note the computed keys. `{ __proto__: x }` written literally is a syntax
// special-case that sets the prototype; `{ ['__proto__']: x }` is an ordinary
// own property, which is what PureScript's record builders produce.
check('__proto__ works as an effect label', () => {
  const h = table({ ['__proto__']: { ask: ctl((_p, k) => k('proto-eff')) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('__proto__', 'ask'))), 'proto-eff')
})

check('__proto__ works as an operation name', () => {
  const h = table({ reader: { ['__proto__']: ctl((_p, k) => k('proto-op')) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('reader', '__proto__'))), 'proto-op')
})

// Object.keys reports own enumerable properties only, so nothing inherited can
// be mistaken for a clause -- including names that exist on Object.prototype.
check('inherited property names are not clauses', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  throws(() => runImpl(withImpl(undefinedReturnImpl, h, perform('reader', 'toString'))),
    /Unhandled effect operation 'reader\.toString'/)
  throws(() => runImpl(withImpl(undefinedReturnImpl, h, perform('constructor', 'ask'))),
    /Unhandled effect operation 'constructor\.ask'/)
})

check('an empty handler table handles nothing', () => {
  throws(() => runImpl(withImpl(undefinedReturnImpl, emptyHandlersImpl(null), perform('a', 'b'))),
    /Unhandled effect operation 'a\.b'/)
})

check('each empty is a fresh object, so tables do not alias', () => {
  const h1 = table({ a: { op: ctl((_p, k) => k(1)) } })
  const h2 = table({ b: { op: ctl((_p, k) => k(2)) } })
  throws(() => runImpl(withImpl(undefinedReturnImpl, h1, perform('b', 'op'))), /Unhandled/)
  eq(runImpl(withImpl(undefinedReturnImpl, h2, perform('b', 'op'))), 2)
})

check('unicode and empty-string labels round-trip', () => {
  const h = table({ '効果': { '操作': ctl((_p, k) => k('ok')) }, '': { '': ctl((_p, k) => k('empty')) } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('効果', '操作'))), 'ok')
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('', ''))), 'empty')
})

// --- clause builders -------------------------------------------------------

check('mkFullClauseImpl uncurries the payload', () => {
  const clause = mkFullClauseImpl((a) => (b) => (k) => k(a + b))
  const h = table({ st: { add: clause } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'add', 3, 4))), 7)
})

check('mkFullClauseImpl with no arguments still receives the resume', () => {
  const clause = mkFullClauseImpl((k) => k('nullary'))
  const h = table({ st: { get: clause } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'get'))), 'nullary')
})

check('mkFastClauseImpl uncurries the payload', () => {
  const clause = mkFastClauseImpl((a) => (b) => pure(a + b))
  const h = table({ st: { add: clause } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'add', 3, 4))), 7)
})

// A fast clause takes no resume, so at arity zero there is nothing left to
// apply: the builder is handed the computation itself.
check('mkFastClauseImpl with no arguments takes the computation itself', () => {
  const clause = mkFastClauseImpl(pure('nullary'))
  const h = table({ st: { get: clause } })
  eq(runImpl(withImpl(undefinedReturnImpl, h, perform('st', 'get'))), 'nullary')
})

check('mkReturnImpl lifts a pure function', () => {
  eq(runImpl(withImpl(mkReturnImpl((v) => v + 1), emptyHandlersImpl(null), pure(1))), 2)
})

// --- depth -----------------------------------------------------------------
//
// Every prompt below is a separate level of the evidence environment, and the
// lookup walks it. This is the shape that regressed once: a per-perform
// recomputation of the stack length made the cost quadratic in the nesting.

check('a deeply nested stack of prompts resolves the outermost', () => {
  const depth = 2000
  const outer = table({ reader: { ask: ctl((_p, k) => k('bottom')) } })
  const filler = table({ other: { nop: ctl((_p, k) => k(null)) } })
  let prog = perform('reader', 'ask')
  for (let i = 0; i < depth; i++) prog = withImpl(undefinedReturnImpl, filler, prog)
  eq(runImpl(withImpl(undefinedReturnImpl, outer, prog)), 'bottom')
})

// A cell is a level of the same environment, so a read at depth walks the same
// list. Nothing here is a performance claim -- test/js/bench.mjs measures the
// slope -- but a read 2000 prompts from its cell must still find it, and must
// not recurse on the JS stack while doing so.
check('a deeply nested stack of prompts resolves the outermost cell', () => {
  const filler = table({ other: { nop: ctl((_p, k) => k(null)) } })
  let prog = readCell('s')
  for (let i = 0; i < 2000; i++) prog = withImpl(undefinedReturnImpl, filler, prog)
  eq(runImpl(newCell('s', 'bottom', prog)), 'bottom')
})

check('a deeply nested stack of cells resolves the outermost cell', () => {
  let prog = readCell('s')
  for (let i = 0; i < 2000; i++) prog = newCell('c' + i, i, prog)
  eq(runImpl(newCell('s', 'bottom', prog)), 'bottom')
})

check('a long bind chain under a handler does not blow up', () => {
  const h = table({ reader: { ask: ctl((_p, k) => k(1)) } })
  let prog = pure(0)
  for (let i = 0; i < 2000; i++) prog = bind(prog, (x) => bind(perform('reader', 'ask'), (n) => pure(x + n)))
  eq(runImpl(withImpl(undefinedReturnImpl, h, prog)), 2000)
})

// --- report ----------------------------------------------------------------

for (const [name, e] of failures) console.error(`\x1b[31m✗\x1b[0m ${name}\n    ${e.message ?? e}`)
console.log(`${passed}/${passed + failures.length} smoke tests passed`)
process.exit(failures.length === 0 ? 0 : 1)
