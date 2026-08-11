# PureScript Hoop

Hoop is an algebraic effects & handlers library based on a CEK-like effect runtime with verified soundness.

[![CI](https://github.com/katsujukou/purescript-hoop-verified/actions/workflows/ci.yaml/badge.svg)](https://github.com/katsujukou/purescript-hoop-verified/actions/workflows/ci.yaml)
[![purs - v0.15.16](https://img.shields.io/badge/purs-v0.15.16-blue?logo=purescript)](https://github.com/purescript/purescript/releases/tag/v0.15.16)

## Overview

Hoop is an algebraic effects and handlers library for PureScript.
While `purescript-run` serves as an excellent library with a similar objective, Hoop differs fundamentally in its core architectural design.

`purescript-run` represents effectful programs using the Free monad via `purescript-free`, where effect interpretation is achieved by folding over the free structure. In contrast, Hoop executes effectful programs directly on a dedicated runtime machine. This architecture is highly analogous to how `purescript-aff` runs its computations inside a trampolined interpreter loop implemented in JavaScript.

The most distinctive feature of Hoop is **the use of a theorem prover** in its runtime implementation: rather than being written directly in JavaScript, the Hoop runtime is fully **implemented and verified in F\*, a proof-oriented programming language**.

## Verified Correctness

[F\*](https://fstar-lang.org/) is a dependently typed language similar to Coq, Agda, and Lean. True to its nature as a proof-oriented language, it allows developers to write proofs directly alongside their programs.

For instance, the following snippet showcases a typical F\* implementation. Here, the `snoc` function (which appends an element to the end of a list) specifies that it returns a list whose length is precisely incremented by one via a *refinement type*. Additionally, `rev_preserves_length` is formulated as an independent lemma in its own right, explicitly stating and **proving** that the list reversal function `rev` preserves the original length of the list:

```fst
let rec length (#a:Type) (xs:list a) : nat
  = match xs with 
    | [] -> 0
    | hd::tl -> 1 + length tl

let rec snoc 
    (#a:Type)
    (xs:list a)
    (x:a)
  : ys: list a{ length ys == length xs + 1 }
  = match xs with
    | [] -> [x]
    | hd::tl -> hd :: snoc tl x

let rec rev (#a:Type) (xs: list a)
  : list a
  = match xs with
    | [] -> []
    | hd :: tl -> rev tl `snoc` hd

let rec rev_preserves_length (#a: Type) (xs:list a)
  : Lemma (length xs == length (rev xs))
  = match xs with
    | [] -> ()
    | _::tl -> rev_preserves_length tl
```

In Hoop, the core execution runtime is mathematically proven to satisfy crucial safety properties using F\*. The verified **F\*** code is first **extracted** into OCaml by the F\* compiler, then compiled to JavaScript by [Melange](https://melange.re/) and bundled with `esbuild`. This artifact is then imported into PureScript through the FFI, wrapped underneath a thin, type-safe PureScript API shell.

Previously, `js_of_ocaml` was used to compile OCaml to JavaScript. Currently, Melange is selected for the following reasons: Melange places a higher emphasis on JavaScript interoperability than `js_of_ocaml`. In Melange, strings and arrays map directly to their native JS counterparts, which eliminates data conversion costs at the FFI boundary and further reduces representation-driven overhead. While `js_of_ocaml` is well-suited for compiling ML applications into standalone JavaScript for the web, Melange was determined to be the ideal choice given the project's requirement to be imported and used as a library from PureScript—a context where seamless interoperability is paramount.

## Boundary of Trust

As noted above, while the runtime provided by this library is rigorously verified using a theorem prover, the Hoop effectful programs accepted as input by the runtime are generated on the PureScript side rather than in F\*. Consequently, F\* can make no intrinsic guarantees about their properties. 

The F\*-verified runtime relies on certain assumptions regarding these opaque JavaScript values passed from PureScript. It is crucial to note that the correctness of the system is **conditional correctness under specific assumptions**—meaning the correctness guarantees are conditional on those boundary assumptions being satisfied.

### What is verified

- **Soundness of operational semantics**:
  - Soundness of stack manipulation:
    - Preservation of stack
    - Innermost lemma
    - Deep-handler semantics
    - Soundness & completeness of `lookup_clause`
  - Progress & preservation theorem:
    - A well-scoped program never reaches a stuck state.
- **Some equational-theoretic properties**:
  - Monad laws
  - Algebraicity of operations, together with a counterexample showing that *handling itself is not algebraic*
- Most importantly, **The Theorem of Correspondence**:
  - The final state of the actual execution machine and the reference machine consistently agree.

### What is trusted

- `runtime/ml/melange/hoop_ffi.ml`: Hand-written OCaml at the FFI boundary, carrying values across it through `%identity` externals.
- `runtime/ml/melange/hoop_prim.js`: The hand-written JavaScript primitives that file declares — property access, the clause-shape discriminator, and the handler-table builders.
- Two shims:
  - Native integer arithmetic in `Prims.ml` (assuming the execution stack never exceeds $2^{31}$ frames).
  - `List` operations in `FStar_List_Tot_Base.ml`.
- F\* standard library (`ulib`) axioms regarding strings and characters.
- The correctness of the toolchain, including F\* extraction, the Melange compiler (`melc`), `dune`, and `esbuild`.
- **Invariants guaranteed by PureScript's type system**:
  - Injectivity of `evKey`.
  - The structural invariants of cell-label locations within the stack.
  - The well-scopedness of PureScript-generated programs.

### How the trusted layer is checked

Trusted does not mean unexamined. `test/js/engine-smoke.mjs` exercises the boundary directly, one level *below* the PureScript surface. That placement is deliberate: the PureScript test suite can only build handler tables its own type checker permits, so it cannot reach the cases the boundary exists to handle. These tests can, and do — a `__proto__` effect label, a nullish return clause, a clause of neither recognised shape, an operation nobody handles.

Some of them discriminate rather than merely exercise. Two figures taken from Koka pin the by-value semantics of prompt-local cells: a runtime that kept a cell behind a shared mutable box would agree with every other test in the file and disagree with exactly those two.

This is what makes the trusted layer *replaceable*. Because F\* assumes this layer rather than verifying it, the layer can be rewritten without touching a single `.fst` or restating a proof — which is exactly what the migration from `js_of_ocaml` to Melange was. The suite is what stands in for the proof while that happens.

It is testing, not proof, and the distinction is the point of this whole section: the boundary assumptions are not discharged. They are checked.
