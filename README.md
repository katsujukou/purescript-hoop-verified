# Purescript Hoop

Hoop is an algebraic effects & handlers library based on a CEK-like effect runtime with verified soundness.

## Overview

Hoop is an algebraic effects and handlers library for PureScript.
While `purescript-run` serves as an excellent library with a similar objective, Hoop differs fundamentally in its core architectural design.

`purescript-run` represents effectful programs using the Free monad via `purescript-free`, where effect interpretation is achieved by folding over the free structure. In contrast, Hoop executes effectful programs directly on a dedicated runtime machine. This architecture is highly analogous to how `purescript-aff` runs its computations inside a trampolined interpreter loop implemented in JavaScript.

The most distinctive feature of Hoop is **the use of a theorem prover** in its runtime implementation: rather than being written directly in JavaScript, the Hoop runtime is fully **implemented and verified in F\*, a proof-oriented programming language**.

## Verified Correctness

F\* is a dependently typed language similar to Coq, Agda, and Lean. True to its nature as a proof-oriented language, it allows developers to write proofs directly alongside their programs.

For instance, the following snippet showcases a typical F\* implementation. Here, the `snoc` function (which appends an element to the end of a list) specifies that it returns a list whose length is precisely incremented by one via a *refinement type*. Additionally, the lemma `rev_preserves_length` independently states and **proves** that the list reversal function `rev` preserves the original length of the list:

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

In Hoop, the core execution runtime is mathematically proven to satisfy crucial safety properties using F\*. The verified **F\*** code is first **extracted** into OCaml by the F\* compiler, and then compiled into JavaScript via `js_of_ocaml`. This artifact is then imported into PureScript through the FFI, wrapped underneath a thin, type-safe PureScript API shell.

## Boundary of Trust

As noted above, while the runtime provided by this library is rigorously verified using a theorem prover, the Hoop effectful programs accepted as input by the runtime are generated on the PureScript side rather than in F\*. Consequently, F\* can make no intrinsic guarantees about their properties. 

The F\*-verified runtime relies on certain assumptions regarding these opaque JavaScript values passed from PureScript. It is crucial to note that the correctness of the system is **conditional correctness under specific assumptions**—meaning the correctness guarantees hold *if and only if* those boundary assumptions are satisfied.

### What is verified

- **Soundness of operational semantics**:
  - Soundness of stack manipulation:
    - Preservation of stack
    - Innermost lemma
    - Deep-handler semantics
    - Soundness & completeness of `lookup_clause`
  - Progress & preservation theorem:
    - A well-scoped program never reaches a stuck state.
- **Monad laws and Algebraicity**
- **Most importantly, The Theorem of Correspondence**:
  - The final state of the actual execution machine and the reference machine consistently agree.

### What is trusted

- `hoop_ffi.ml`: Hand-written OCaml code using `Obj.magic`.
- Two shims:
  - Native integer arithmetic in `Prims.ml` (assuming the execution stack never exceeds $2^{31}$ frames).
  - List operations in `FStar_List_Tot_Base.ml`.
- F\* standard library (`ulib`) axioms regarding strings and characters.
- The `ocamlc` compiler and `js_of_ocaml` itself.
- **Invariants guaranteed by PureScript's type system**:
  - Injectivity of `evKey`.
  - The structural invariants of cell-label locations within the stack.
  - The well-scopedness of PureScript-generated programs.
