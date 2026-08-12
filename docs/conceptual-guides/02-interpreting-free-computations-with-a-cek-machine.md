# Interpreting Free Computations with a CEK Machine

In this chapter, we will discuss the **CEK-machine**-based interpreter and explore how free monadic computations are interpreted and executed on top of it. Hoop's effect runtime is fundamentally built around a CEK machine. Therefore, getting to know the CEK machine is your very first step toward understanding the inner workings of the Hoop runtime.

## The CEK Machine

The CEK machine is a stack-based abstract machine designed for executing lambda calculus, and it serves as the underlying execution model for many functional programming languages. As the name suggests, the CEK machine is composed of three core components: Control, Environment, and Kontinuation.

- **Control**: The next expression or instruction to be executed
- **Environment**: The variable environment; a mapping from variable names (identifiers) to their respective values
- **Kontinuation**: The computation remaining to be executed after the current Control finishes (i.e., the continuation)

The CEK machine advances program execution step-by-step: each time it processes a single component C, it updates E and K, pops the next instruction from the stack K, processes it, and repeats. In Hoop, these three components—C, E, and K—are utilized as follows:

- **Control**: The Hoop program itself (the AST)
- **Environment**: A mapping from actions to their corresponding handling clauses (which we will cover in detail in later chapters)
- **Kontinuation**: The continuation stack, just like in a standard CEK machine

The C-part holds the AST of the Hoop program currently being executed. This program is represented as a computation tree like the free monad we explored in the previous chapter, which roughly takes the following shape (written in F\* syntax):

```fstar
type comp_tree (v : Type) =
  | Var: v -> comp_tree v
  | Op: comp:comp_tree v -> fn:(v -> comp_tree v) -> comp_tree v  
```

This definition is a significantly simplified version of the actual AST type found in `Hoop.Runtime.Syntax.fst`, tailored specifically for the conceptual explanations in this section.
Here, `v` represents the type of the value output by the computation tree. Since the Hoop runtime handles type-erased, opaque JavaScript values at runtime, all values are represented using this opaque type parameter. Although the constructor names differ from the free monad we introduced in the previous chapter, `Var` corresponds to `Pure`, and `Op` corresponds to `Bind`.

> *Note:* In F\*, the name `Pure` is avoided because it conflicts with the built-in effect name defined in the F\* standard library. The names `Var` and `Op` are adopted from the following paper:
> [Birthe van den Berg and Tom Schrijvers: *A Framework for Higher-Order Effects & Handlers*](https://arxiv.org/abs/2302.01415)

The K-part is a stack of *defunctionalized continuation frames*. When executing a computation tree given by a free monad above, namely a `comp_tree`, a continuation is literally nothing other than the right-hand side of a `>>=` bind operation, or `Op` node. Therefore, a frame pushed onto the K-stack has exactly one data constructor:

```fstar
type frame v = 
  | BindF: fn:(v -> comp_tree v) -> frame v
```

We do not actually need the E-part in this chapter. In a standard CEK machine, E represents a variable environment. However, in Hoop, PureScript (and by extension, JavaScript) closures already handle this responsibility out of the box. In reality, Hoop repurposes E for optimization reasons quite differently from the original CEK machine, but we will save that discussion for a later chapter on optimizations.

Based on this setup, we can write a **state transition table** for a CEK machine that interprets the simplest (and admittedly, most boring) free monad computation tree.

As mentioned earlier, the CEK machine updates E and K-stack while setting the next computation into the C-register. Thus, we describe how E and K change depending on the current shape (`Var` or `Op`) of the `comp_tree` stored in the C-register. Evaluation concludes when the `K` stack becomes completely empty.

| Current C | Current K | Next C | Next K |
| :--- | :--- | :--- | :--- |
| `Var x` | `[]` | Terminate with `x` returned | -- |
| `Var x` | `(BindF fn) :: κ'` | `fn x` | `κ'` |
| `Op c1 fn` | `κ` | `c1` | `BindF fn :: κ` |

This transition table dictates the following rules:

- When C is a `Var` node, the machine branches based on the status of the K stack:
  - If K is empty, the machine terminates and returns the underlying value `x`
  - If K is not empty, it pops the top frame `BindF fn`, applies the continuation `fn` to the currently held value `x`, and updates C with the resulting computation tree
- When C is an `Op` node, the machine places the left-hand computation tree into the C register, packs the right-hand side into a new `BindF` frame, and pushes it onto the K-stack.

Following these rules, we can construct an abstract stack machine capable of executing any arbitrary Free computation tree. In other words, **we have just formally defined the operational semantics** for our Free computation tree interpreter.

## Performing & Handling Effectful Actions

Up until the previous section, we only dealt with sequential execution via monadic binds. In this section, the execution of **effectful actions** is introduced, and things gradually become much more interesting.

First, let us clarify some terminology. As described in the [Getting Started](../01-getting-started.md) chapter, an effect in Hoop is an opaque symbol represented by a set of operations. We refer to a pair consisting of an effect label and an operation label, `(eff, op)`, as an effectful **action**. An action can carry a set of payloads.

An effect handler is a collection of functions—which we refer to as **clauses** -- where each clause corresponds to an operation label and accepts its payloads along with a captured delimited continuation. We assume that these handlers, or clause tables, have been installed beforehand using the `with handler ...` syntax.

From a runtime perspective, effects are triggered in a Hoop program via the `perform` primitive. The moment a perform occurs, the control flow of the program non-sequentially jumps to the position of the installed handler. Handlers are installed via the `with` primitive. To support these operations, the AST of a Hoop program features dedicated nodes for `Perform` and `Handle`:

```fstar
type comp_tree (v cl : Type) =
  | Var:
      value: v ->
      comp_tree v cl
  | Op:
      comp:comp_tree v cl ->
      fn:(v -> comp_tree v cl) ->
      comp_tree v cl
  | Perform:
      eff: string ->
      op: string ->
      payloads: list v ->
      comp_tree v cl
  | Handle:
      hs: handlers cl ->
      body: comp_tree v cl ->
      comp_tree v cl
  // An internal node used by the machine to enable global control for resumption.
  // The syntax for explicitly constructing Resumed nodes is not exported to the user.
  | Resumed:
      frames: list (frame v cl) ->
      value: v ->
      comp_tree v cl

and frame v cl =
  | BindF:
      fn:(v -> comp_tree v cl) ->
      frame v cl
  | PromptF:
      hs:handlers cl ->
      frame v cl
```

> Currently, `Resumed` node is replaced with more general form of
>
> ```fstar
>   | Splice: 
>       frames:list (frame v cl) ->
>       c: comp_tree v cl ->
>       comp_tree v cl
> ```
>
> `Resumed` node is specialized version of `Splice` node with `c == Var x`.

Again, this is a simplified version of the actual definition. Compared to the `comp_tree` introduced in the previous section, a new type parameter `cl` has been added. This parameter represents the type of the clauses. Since clauses in the Hoop runtime are type-erased, opaque JavaScript closures, they are abstracted into an opaque type parameter. Furthermore, due to the extensions in this section, an AST node can now wrap stack frames, and a stack frame can wrap an AST, meaning both types are now consolidated into a mutually recursive group.

How exactly is the non-sequential control flow of performing and handling effects achieved? The answer can be found in the state transition tables below.

### Handler Installation

| Current C | Current K | Next C | Next K |
| :--- | :--- | :--- | :--- |
| `Handle hs body` | κ | `body` | `(PromptF hs) :: κ` |

When processing a `Handle` node, the machine packs the clause table `hs` into a `PromptF` frame and pushes it onto the continuation stack. It then places the computation tree inside the handler's scope into the C-register to process it next.

A *prompt* serves as a landmark for the machine to non-sequentially transfer the control flow to the handler's location when an effect action is performed. This mechanism can be clearly observed in the state transition table for the `Perform` node below (where `@` denotes the concatenation of stack lists):

### Performing

| Current C | Current K | Next C | Next K |
| :--- | :--- | :--- | :--- |
| `Perform eff op pay` | $\kappa_1$ @ $\kappa_2$ <br> where<br> $\kappa_1$ = $\kappa_1^\prime$ @ `[PromptF hs]` <br> hs = { ..., [eff]: {..., [op]: h } }` | `h(...pay, kont)`<br>where<br>`kont = fun v -> Resumed κ_1 v` | $\kappa_2$ |
| `Perform eff op pay` | $\kappa$ <br> where <br> `(eff, op)` is not handled in $\kappa$ | Stuck | -- |

This table is somewhat intricate, so please review it carefully. When a `Perform` node is detected, the machine traverses the stack from the top to search for a prompt capable of handling `(eff, op)`. If such a `PromptF hs` frame is found, the machine extracts the clause corresponding to `(eff, op)` from the `hs` table and executes it by passing the payloads and the captured delimited continuation.

However, in our abstract machine, the continuation is not stored as a raw computation tree (comp_tree), but is instead accumulated on the stack as defunctionalized frames. Consequently, when a continuation is invoked and resumed, we cannot simply load its corresponding next computation straight into the C-register. To bridge these two representations -- `comp_tree` and `frame` -- the machine utilizes an internal node called `Resumed`. This is precisely why a clause receives its continuation callback in the following format:

```ml
fun v -> Resumed κ_1 v 
```

Crucially, invoking `kont` does not trigger an immediate, physical jump in the JavaScript call stack. Instead, as a prime example of defunctionalization, this lambda simply constructs a static `Resumed` node—a piece of data holding the value `v` and the captured stack $\kappa_1$. When this `Resumed` node is returned from the clause and loaded into the machine's C-register, the subsequent transition step finally executes the physical jump by prepending the captured frames back onto the active stack. Next, we cover this more precisely.

### Resumption

The state transition table for the `Resumed` node dictates the non-sequential jump from the handler clause back to the original `perform` site. In the PureScript surface language, resumption is triggered by passing the captured continuation `k` to the `continue` primitive, where the continuation is an opaque value of type `Cont b effrow o`.

> *Note*: A bit of terminology: the value returned from a continuation is commonly referred to as the **answer**.

Here, `b` is the result type expected by the suspended `perform` expression and therefore the type of the value supplied to the continuation. `o` is the answer type of the captured continuation and its handler. Accordingly, `continue k v` has type `Hoop effrow o`. On the runtime side, as mentioned earlier, a continuation is merely a lambda that constructs and returns a `Resumed` node. The true nature of `continue` is simply to reveal the underlying lambda type `b -> Hoop effrow o` from the opaque `Cont b effrow o` type. Once a `Resumed` node is loaded into the C-register via resumption, the machine redirects the execution back to the `perform` site according to the following transition table:

| Current C | Current K | Next C | Next K |
|---|---|---|---|
| `Resumed κ_1 v` | $\kappa_2$ | `Var v` | $\kappa_1$ @ $\kappa_2$ |

As shown above, processing a `Resumed` node simply prepends the captured continuation stack $\kappa_1$ back onto the current stack $\kappa_2$, wraps the value passed to continue into a `Var` node, and loads it into the C-register.

> Note on Constructor Design:
> Attentive readers might have noticed that the shape of Op in Hoop's computation tree appears structurally different from the definition found in the paper by Schrijvers et al.:
>
> ```hs
> Op :: ∀b . σ b -> (b -> Free σ a) -> Free σ a
> ```
>
> While the paper's `Op` directly couples a concrete effect signature `σ` with its continuation, Hoop’s `Op` adopts a variation of explicit bind node.
>
> Therefore, Hoop's `Op` node does not signify the occurrence of an effect itself. Instead, it represents a deferred monadic bind that horizontally aligns an unevaluated left-hand computation (`comp`) and a right-hand continuation function (`fn`).
>
> This architectural choice enables the Hoop runtime (CEK-like abstract machine) to avoid deeply deconstructing effect data structures. The moment it encounters an `Op` node, it executes an fast stack transition—setting the left-hand side into the Control register and pushing the right-hand side onto the K-stack.

## Deep vs Shallow Handler Semantics

In the state transition rule for the `Perform` node presented in the previous section, the captured continuation supplied to the clause was defined as $\kappa_1$. Note that the target frame `PromptF hs` itself is present at the bottom of the  captured $\kappa_1$ and hence still installed within the handler context. Interestingly, whether a captured continuation retains or discards its handling prompt is the exact deciding factor that distinguishes **Deep and Shallow handler semantics**.

### Deep Handlers

In Deep Handler Semantics, the handler remains active and wraps the entire continuation. When an effect is performed, the machine captures the continuation up to the handler, and when that continuation is later resumed, the same handler is automatically re-installed to guard the resumed computation. Hoop implements this behavior. In a deep handler model, a handler handles not only the immediate effect but also any subsequent effects of the same type that might be triggered inside its own continuation.

### Shallow Handlers

In Shallow Handler Semantics, a handler only handles the very first effect that occurs within its scope. When an effect is triggered, the handler is stripped away entirely. The captured continuation does not include the prompt, meaning that if the continuation performs the same effect again after being resumed, that effect will propagate outward to the next enclosing handler unless a new handler is explicitly re-installed manually.
By capturing `κ_1 = κ_1' @ [PromptF hs]` while executing the clause under $\kappa_2$, Hoop’s transition rule implements deep-handler semantics.
