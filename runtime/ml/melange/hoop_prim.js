// The JavaScript primitives the Melange boundary declares as externals.
//
// TCB, exactly as much as the jsoo `hoop_ffi.ml` is: nothing here is covered by
// an F* proof, and `test/js/engine-smoke.mjs` is what checks it.
//
// These are the same snippets the jsoo build embeds as `pure_js_expr` strings.
// Melange has no equivalent that keeps arity information, and an OCaml `let`
// bound to a raw function would be a *curried* OCaml value -- which is how a
// `Curry._2` gets onto the hot path. Declaring them as externals with
// `[@mel.module]` instead keeps every call a direct JS call, and has the side
// benefit of putting the trusted JavaScript somewhere a reader can find it.

export function call1(f, x) { return f(x) }
export function call2(f, a, b) { return f(a, b) }

export function isNullish(x) { return x == null }
export function isFunction(x) { return typeof x === 'function' }

export function throwError(msg) { throw new Error(msg) }

// Returns the *inner* function of a fast clause, or null if `x` is not one, so
// that a perform never reaches for `.fun`. See `tag_clause`.
export function fastFun(x) {
  return (x !== null && typeof x === 'object' && typeof x.fun === 'function')
    ? x.fun
    : null
}

// Own enumerable properties only: nothing inherited from Object.prototype can
// be mistaken for an effect label or an operation name.
export function objectKeys(o) { return Object.keys(o) }

// Feeds a curried PureScript handler each element of the payload array in turn.
// The array's length always equals the operation's arity, because the perform
// site built it with `mkAction` from the same operation signature.
export function applyPayload(f, payload) {
  var g = f
  for (var i = 0; i < payload.length; i++) { g = g(payload[i]) }
  return g
}

// Note the null prototype. On an ordinary `{}`, `rec["__proto__"] = v` invokes
// the inherited setter and reassigns the prototype -- a computed key does *not*
// make it an own property -- so an effect labelled `__proto__` would silently
// corrupt the table instead of being stored in it.
//
// The empties hand out a *fresh* object each time, so a table under
// construction is always private to one builder and `insert` may mutate it
// rather than copy.
export function emptyRecord(_unit) { return Object.create(null) }
export function insert(key, value, rec) { rec[key] = value; return rec }

// The three builders live here rather than in OCaml, and must stay here.
//
// Each of them RETURNS a function, and Melange flattens `let f a = fun b c ->`
// into a three-argument JS function -- so an OCaml definition would export the
// wrong arity and the clause would be called with its payload in the wrong
// place. (The jsoo boundary keeps them in JS for the mirror-image reason: its
// `caml_js_wrap_callback` double-wraps a returned function.) Two backends, two
// hazards, one conclusion: a curried boundary function is written in JS.

// A fully controllable clause from a curried PS handler
// `a1 -> ... -> an -> Cont b r o -> Hoop r o`. `Cont` is the machine's own
// resume function, so it is passed on unwrapped.
export function mkFullClause(f) {
  return function (payload, resume) { return applyPayload(f, payload)(resume) }
}

// A tail-resumptive clause from a curried PS handler
// `a1 -> ... -> an -> Hoop r b`. No resume parameter: the body's value is the
// operation's result. The object wrapper is the discriminator `tag_clause`
// tests -- the one shape a curried PureScript handler cannot be mistaken for.
export function mkFastClause(f) {
  return { fun: function (payload) { return applyPayload(f, payload) } }
}

// The return clause is a *pure* function `a -> o` on the PS side; the machine
// expects `(value) => comp`, so the result is lifted with `pure`.
export function mkReturn(pure, f) {
  return function (value) { return pure(f(value)) }
}
