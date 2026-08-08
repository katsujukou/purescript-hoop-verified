// Smoke tests for the FFI boundary in src/Hoop/Engine.js.
//
// These sit below the PureScript surface on purpose. test/Hoop.purs exercises
// the typed API and can only construct handler tables the type checker permits;
// what is checked here is the other half -- the handwritten OCaml in
// runtime/ml/hoop_ffi.ml, which is part of the TCB and which no F* proof
// covers. Hence the awkward inputs: a `__proto__` effect label, a nullish
// return clause, a clause of neither recognised shape, an unhandled operation.
//
// The fast-clause section is here for the same reason. Whether a clause reaches
// the machine tagged Full or Fast is decided by hoop_ffi.ml alone, from the JS
// shape the builders produce; F* proves what each tag then means, but nothing
// proves the tag was read off correctly.
//
// Run with: node test/js/engine-smoke.mjs   (after hoop-build-runtime)

import {
  pureImpl, bindImpl, performImpl, withImpl, runImpl,
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
