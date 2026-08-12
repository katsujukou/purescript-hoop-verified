# General Higher-Order Effects in Verified Hoop

Date: 2026-08-06  
Status: Direction-setting notes, not yet a specification

## Purpose

This note records the design discussion on extending verified Hoop from
first-order algebraic effects to scoped and, eventually, general higher-order
effects. It records not only the current direction, but also the alternatives
that were rejected and the reasons why. The TypeScript implementation remains
an important executable reference, but matching its representation is not a
goal in itself: the verified implementation should optimize for a clean
operational semantics and tractable proofs.

The intended long-term scope includes scoped effects, latent effects, and more
general operations that contain, defer, duplicate, or otherwise control
internal computations.

## Current baseline

The verified runtime currently has two machines:

1. `Hoop.Runtime`, a simple stack-searching reference machine; and
2. `Hoop.Runtime.Machine`, an evidence-passing implementation machine.

The implementation machine maintains an environment that maps handled
operation keys to evidence. Its ordinary steps agree exactly with the reference
machine's states. This exact agreement has been very effective for transporting
the existing progress, soundness, and law proofs.

Evidence lookup has also been optimized without changing downstream proofs. A
handler table and its key set now preserve the source nesting by effect and then
operation, rather than flattening all `(effect, operation)` pairs into one list.
The public ghost view remains a `list key`, while the runtime uses an abstract
`keyset`. This changed only `Handlers` and `Env`; `Env.Stack`, `Machine`,
`Properties`, `Laws`, and `Test` remained unchanged.

The resulting lookup cost is:

```text
before: O(N * W)
after:  O(N * E + W_hit)
```

where `N` is handler depth, `E` is the number of effects in each handler, and
`W_hit` is the position of the selected operation within the matching effect.
This removed the previous width-dependent hot path and established a clean
baseline for the tail-resumptive fast path.

## Near-term prerequisite: tail-resumptive fast path

A tail-resumptive clause runs its body in place. It does not capture the
continuation and resumes exactly once with the body's result. While the body is
running, the handler's prompt is still on the stack but must be absent from the
active evidence environment, so operations in the body resolve in the context
outside that handler.

The TypeScript runtime represents this with an `EnvF` frame carrying the saved
environment:

```text
push EnvF(saved environment)
E := evidence.below
C := clause body
```

When the body finishes, `EnvF` restores the saved environment. If a full
operation captures the stack while a fast body is running, `EnvF` may itself be
captured and must be reinstalled consistently on resumption.

### Rejected `FastF : nat` design

An early proposal stored a stack height in a `FastF` frame so that the reference
stack-searching machine could skip masked frames. Counting raw frames is
incorrect: the monad-law simulations replace no-prompt stack blocks of different
lengths, so an absolute frame count can cause the two sides of a law to dispatch
to different prompts. Counting prompts instead of frames avoids that immediate
counterexample, but introduces a mask/coverage invariant throughout stack
append, weakening, progress, `handled_in`, and law proofs.

The conclusion is that mask bookkeeping is not merely an extra constructor
case. It is evidence that exact per-step state equality is too strong for an
optimization whose purpose is to remove semantic steps and stack manipulation.

## Machine architecture decision

The preferred architecture is:

```text
reference semantics
    stack-searching Runtime
    fast clauses interpreted by semantic desugaring

optimized implementation
    evidence-based CEK machine
    EnvF and future scope/context frames exist only here

proof boundary
    weak operational simulation / refinement
    rather than equality after every individual step
```

The reference machine should remain independent. It is valuable as an
executable specification and as an oracle against which implementation bugs can
be detected. Conversely, the optimized machine should not force runtime-only
bookkeeping such as masks into the reference semantics merely to preserve
lockstep equality.

The intended theorem is observational execution agreement, conceptually:

```text
execute_cek p == execute_reference (desugar_optimizations p)
```

Locally, the proof should use a simulation of the form:

```text
q ~= s
step_cek q = q'
------------------------------------------
exists n s'. steps_reference n s = s' /\ q' ~= s'
```

If zero reference steps are permitted, the relation needs a well-founded rank
to rule out infinite stuttering. The implementation machine must separately
preserve an invariant strong enough to show that a well-scoped configuration
cannot take its error transition.

Existing monad and algebraicity laws should remain on the reference semantics
and be transported to the optimized machine through execution refinement,
rather than being restated wholesale over implementation configurations.

The abstract evidence environment should also remain abstract. Making it a
concrete list solely to recover propositional equality would throw away the
representation independence that made the keyset optimization local. Machine
relations should use the environment's observational equivalence.

## Feature order: scoped first, then latent, then generalize

Theoretical design should be informed by general higher-order frameworks, but
implementation and proof development should proceed through concrete vertical
slices:

1. establish CEK/reference refinement and the tail-resumptive fast path;
2. implement scoped operations;
3. implement latent/deferred operations;
4. use both instances to extract the genuinely common abstraction; and
5. only then freeze a general higher-order API and semantics.

Scoped operations are the smallest non-trivial case: they expose an internal
computation, distinguish the inside and outside of a scope, require context
restoration, and exercise forwarding through intervening handlers. Latent
operations then test a different lifetime: an internal computation is stored
and run later, possibly in another dynamic context. Designing the fully general
interface before these two cases risks fixing laws and representations whose
necessity has not yet been demonstrated.

## What the TypeScript scoped implementation taught us

The TypeScript design discussion initially followed the free-monad literature
and proposed an `HFunctor`-like structure for higher-order signatures. That
conclusion was later revised after separating fold-based handlers from Hoop's
prompt-based operational semantics.

### Why fold-based systems need `HFunctor`

In a higher-order free syntax, a node contains internal computations. A generic
fold cannot reach those computations unless the signature provides a structural
map such as:

```text
hmap : (forall x. m x -> n x) -> h m a -> h n a
```

This tells an interpreter where every embedded computation occurs and lets it
weave an outer handler and its functorial context through the node.

### Why TypeScript Hoop does not

Hoop handlers are live prompts, not folds over a syntax tree. The scoped clause
knows the operation-specific payload shape and destructures it itself. The
runtime supplies a rank-2 capability for running whichever internal computation
the clause selects:

```text
weave : forall x. Hoop inner x -> Hoop outer (f x)
```

The inner row is a rigid skolem. An embedded computation cannot be sequenced
into the clause result without passing through `weave`. Thus the type system
enforces the property actually needed by the operational design: every internal
computation that is executed must be executed through the supplied context
capability. It does not require every embedded computation to be transformed in
advance; for example, a recovery branch that is not selected need not be mapped
or run.

At runtime, `weave`:

1. installs a fresh owning prompt for the scoped handler itself; and
2. reinstalls the prompts that were active at the perform site as borrowed
   prompts.

Borrowed prompts are available for dispatch but are not new answer boundaries,
so their return clauses or generators do not run when the scope finishes.

This does not eliminate weaving; it moves weaving responsibility from the
higher-order signature to the dynamic handler context.

## Current scoped semantics and its limitation

The TypeScript implementation fixes the interaction with parameterized state to
global update. A borrowed state prompt shares the original prompt's cell. Writes
inside the scope are therefore observed by recovery and by the continuation.

Only prompts whose clauses resume in place can currently be borrowed. In
practice this means tail-resumptive `fun` clauses and parameterized `st`
transitions. A continuation-capturing intermediate prompt is rejected.

This restriction has two different aspects:

1. The exact syntactic criterion, "all clauses are `fun` or `st`", is a
   conservative sufficient condition and may be widened.
2. Transparently crossing an arbitrary full, answer-transforming handler is a
   semantic and typing problem, not a small implementation omission.

For an arbitrary intermediate handler, the scope result may be transformed by a
dynamic context such as:

```text
Ctx = f1 o f2 o ... o fn
```

where the `fi` are answer transformations of prompts lying between the perform
site and the scoped handler. This context is known only at runtime, while the
current `weave` result type does not expose it. Supporting it requires a typed
representation of dynamic context composition. This need not literally be an
`HFunctor`, but it must carry the information that functorial contexts carry in
fold-based systems.

Possible future levels are:

```text
Borrowable
  fast/st; dispatch-only reinstallation; global-update semantics

Transparent
  rank-2, answer-preserving full handlers; temporary owning boundary

General
  answer-transforming and continuation-capturing contexts composed in types
```

The first verified scoped milestone should formalize the existing Borrowable
semantics rather than silently promising the General level.

## Direction for general higher-order effects

The current research hypothesis is that Hoop can replace signature-specific
structural traversal with capabilities derived from the dynamic handler
context.

Potential capabilities include:

```text
scoped/immediate: weave and run now
latent/deferred:  seal or suspend for later
parallel:         clone/transfer into several branches
resource:         finalize on normal or abnormal exit
```

The generalization should distinguish three dimensions:

1. **Payload-shape genericity.** The runtime need not know the structure of
   `h`; the interpreting clause knows it and chooses the internal computations.
2. **Handler-context genericity.** Intervening handler states and answer
   transformations can be composed safely rather than being limited to borrowed
   in-place prompts.
3. **Lifetime genericity.** Internal computations may run immediately, later,
   multiple times, in parallel, or during finalization.

The first dimension is already largely present in the TypeScript scoped API.
The second and third are the principal research problems.

It is premature to claim that `HFunctor` can always be eliminated. A more
careful hypothesis is that the relevant structure can move:

```text
traditional design:
    structural action belongs to the higher-order signature

Hoop hypothesis:
    operational action belongs to the dynamically captured handler context
```

An optional `HFunctor` may still be useful for generic folds or source
transformations, but it should not be a prerequisite for defining an operation
whose clause explicitly controls its internal computations.

## Candidate research contribution

A potentially publishable claim is:

> Higher-order effect systems traditionally require each higher-order signature
> to expose an `HFunctor`-like traversal so handlers can be woven through
> embedded computations. In an evidence-passing prompt machine, this traversal
> can instead be represented by rank-2 execution capabilities derived from the
> dynamic handler context. We give a type-safe operational semantics, prove its
> correspondence with a reference higher-order semantics, and derive an
> efficient implementation.

Evidence-passing support for scoped effects already exists, so novelty cannot
rest on that fact alone. The strongest distinguishing combination would be:

- user-defined general higher-order signatures without mandatory structural
  traversal;
- prompt/evidence-based operational weaving;
- typed composition of arbitrary dynamic handler contexts;
- support beyond immediate scoped operations, especially latent computations;
- mechanized soundness and operational-correspondence proofs; and
- evidence that specialized borrowed-prompt paths implement the general
  semantics efficiently.

## Proof targets

The development should aim at the following results.

### CEK/reference operational correspondence

The optimized machine and the stack-searching reference semantics produce the
same observations, although their individual transitions need not match.

### Scoped weaving soundness

For a well-typed scoped clause, executing an internal computation through its
weave capability:

- restores the correct perform-site handler view;
- keeps the scoped handler deep inside the scope;
- preserves well-scopedness;
- cannot dispatch to a clause with an incompatible operation key;
- respects borrowed/owning prompt distinctions; and
- preserves these distinctions across capture and resumption.

### Global-update characterization

The borrowed-prompt implementation should be related to an explicit semantic
model of shared handler state, rather than described only operationally.

### General-context laws

If typed dynamic contexts are introduced, their identity, composition, and
interaction with installation, capture, resumption, and suspension should be
stated explicitly.

### Optimization correctness

The tail-resumptive and borrowed-prompt fast paths should refine the general
semantics rather than define separate behaviors.

## Immediate next steps

1. Keep the corrected right-associated benchmark as the performance baseline.
2. Prototype the CEK/reference simulation on a small fragment containing
   `Var`, `Bind`, `Handle`, fast `Perform`, and a full perform inside a fast
   body.
3. Add `EnvF` only to the optimized machine and verify capture/reinstallation.
4. Prove the tail-resumptive optimization against its ordinary full-clause
   desugaring.
5. Port the TypeScript scoped API and Borrowable/global-update semantics.
6. Use `once` and `catch`, including State interactions, as the first semantic
   tests.
7. Add a latent operation to test deferred context ownership.
8. Revisit the common capability only after scoped and latent instances are
   verified.

## Open questions

- What is the smallest simulation relation that handles `EnvF`, borrowed
  prompts, and future suspended contexts without restating all existing laws?
- Can answer-preserving full handlers be admitted as a distinct Transparent
  class without introducing a full functorial context?
- How should a dynamic answer-transforming context be represented in
  PureScript's type system: existential package, Church encoding, associated
  type constructor, or another capability interface?
- Which handler state policies should be primitive: share, clone, rollback,
  commit, or user-defined?
- Can latent and parallel contexts reuse the same context representation, or do
  their lifetime and multiplicity requirements demand separate capabilities?
- What is the exact correspondence between the prompt-based semantics and an
  existing higher-order free-monad, scoped-calculus, or hefty-algebra model?
- Which restrictions are semantic choices worth documenting, and which are
  temporary limitations that should be rejected statically or dynamically?

## Nearby work to compare in detail

- Wu, Schrijvers, and Hinze, *Effect Handlers in Scope*.
- Bosman et al., *A Calculus for Scoped Effects & Handlers*.
- van den Berg and Schrijvers, *A Framework for Higher-Order Effects &
  Handlers*.
- van der Rest, Reinders, and Poulsen, *Handling Higher-Order Effects*.
- van der Rest and Poulsen, *Hefty Algebras*.
- Ren, *Effect Handlers in Scope, Evidently* / SpEff.
- Xie and Leijen, work on generalized evidence passing and Koka's runtime.
- Polysemy's `Tactics` and fused-effects' higher-order carriers as practical
  functorial-context implementations.

The closest overlap is evidence-passing scoped effects. The intended research
gap is the combination of general higher-order operations, prompt-derived
capabilities rather than mandatory signature traversal, typed dynamic context
composition, and a verified executable machine.
