# Hoop Documentation

Hoop is an algebraic effects and handlers library for PureScript. A unique feature of Hoop is that its effect-handling mechanism is implemented in F*, and its correctness has been mechanically verified through numerous theorems.

This directory serves as the comprehensive documentation for Hoop.
This documentation covers how to use Hoop and provides a concepts reference. 

## Learning

For **algebraic effects**, the [Effects Bibliography](https://github.com/yallop/effects-bibliography) compiles a rich set of learning resources, including effect systems, libraries, and academic papers.

At present, readers who are not familiar with F\* might be in the majority. For F\*, the following resources will be helpful:

* [https://fstar-lang.org/](https://fstar-lang.org/)
* [Proof-Oriented Programming in F*](https://fstar-lang.org/tutorial/)
* [GitHub Wiki](https://github.com/FStarLang/FStar/wiki)

### Table of Contents

* [**Getting Started**](./01-getting-started.md)
Provides a brief introduction to algebraic effects & handlers, along with the most basic usage of Hoop as a library.

* [**Comparison with Other Effect Languages**](./02-comparison-with-other-effect-languages.md)
Explains the architectural and design differences between Hoop and existing effect libraries or systems, such as `purescript-run` and Koka.

* [**Conceptual Guides**](./conceptual-guides/00-index.md)
[*WIP*] Read this section if you want to dive deeper into the ideas behind Hoop and understand the reasoning behind its current implementation. 

  * [Free Monad And Effect](./conceptual-guides/01-free-monad-and-effect.md)
  * [Interpreting Free Computations with A CEK Machine](./conceptual-guides/02-interpreting-free-computations-with-a-cek-machine.md)