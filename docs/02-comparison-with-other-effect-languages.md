# Comparison with Other Effect Languages

## purescript-run

[`purescript-run`](https://github.com/natefaubion/purescript-run) is the
established extensible-effects library in the PureScript ecosystem, built on
a free monad over `VariantF`. The two libraries share the surface idea —
effects tracked in a row, handled one label at a time — but differ in almost
every structural choice:

- **Effect encoding.** In `run`, an effect is a `Functor` and an operation is
  a constructor of that functor, with the continuation embedded as the
  functor's parameter (`Get (s -> a)`). In Hoop, an effect is an opaque
  `EffType` whose operations are declared as a row of *operation signatures*
  (`get :: Unit ->* s`); no functor instances, `Free`/`VariantF` plumbing, or
  smart constructors per operation are needed.
- **Handlers.** `run` handlers are folds you write with combinators like
  `interpret` and `runCont`, matching on the functor. Hoop handlers are
  records of clauses checked against the operation signatures, with
  controllability chosen per clause (`full`/`fast`) and an optional `pure`
  return clause.
- **Runtime.** `run` interprets a reified free-monad tree in PureScript;
  continuations are the functor's own fields. Hoop executes on a dedicated
  VM with evidence-passing dispatch, real multi-shot
  delimited continuations, and an effective tail-resumptive fast path.

## Koka

[Koka](https://koka-lang.github.io/koka/doc/index.html) is the reference
point for Hoop's semantics: deep handlers, `fun`/`ctl` clause distinction,
`return` clauses, and evidence passing all originate there. Hoop is best
understood as a monadic embedding of Koka's model:

- Koka is *direct style* — effects live in the typing judgment, so pure
  expressions slot into effectful contexts implicitly. Hoop programs live in
  the explicit monad `Hoop r`, so the lifting (`pure`) and sequencing
  (`>>=`/`do`) that Koka hides are visible. This is a deliberate fit with
  PureScript culture rather than a limitation.
- Clause controllability: Hoop's `fast`/`full` correspond to Koka's
  `fun`/`ctl`. One deliberate difference: Koka's `return` clause may perform
  effects, while Hoop's `pure` clause is restricted to a pure function
  `a -> o`; considering PureScript culture, it may seems somewhat confusing that a `pure`-called clause actually performs arbitrary Hoop-effect.
- Koka's declarations can also *commit* an operation to a controllability
  (`fun` in the effect declaration), enabling call-site optimizations. Hoop
  currently declares every operation with `->*` and leaves the choice
  entirely to handlers.

## OCaml

OCaml 5 ships effect handlers as a runtime facility
([manual](https://ocaml.org/manual/5.5/effects.html)) motivated primarily by
direct-style concurrency. Compared to Hoop:

- **No effect typing.** Performing an unhandled effect is a runtime
  exception; nothing in a function's type reveals the effects it performs.
  In Hoop the row does exactly that, and `run` statically requires the empty
  row.
- **One-shot continuations.** OCaml continuations are one-shot (resuming
  twice raises `Continuation_already_resumed`); the language itself offers
  no way to copy one — multi-shot use needs the third-party
  [`multicont`](https://opam.ocaml.org/packages/multicont/) library. Hoop
  continuations are values that may be resumed any number of times —
  nondeterminism-style handlers are ordinary code.
- **Deep vs shallow.** OCaml offers both `Effect.Deep` and `Effect.Shallow`;
  Hoop currently provides deep handlers only.

## Flix

[Flix](https://flix.dev/) integrates algebraic effects into a full
type-and-effect system with effect polymorphism and complete inference, in a
direct-style language — on the typing side it is the closest of the four to
what Hoop's row `r` approximates inside PureScript's type system. The main
contrasts are the host strategy: Flix is a language with a compiler that can
do effect-aware optimization (and restricts continuations similarly to
Koka's model), while Hoop retrofits effect tracking onto an existing
language as a library, using row types for the effect discipline and a
runtime machine for the control flow, with no compiler support.
