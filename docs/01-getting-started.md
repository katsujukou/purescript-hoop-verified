# Getting Started

Hoop is a library of effect types and handlers. This document shows how to:

* define effect types
* perform those effects
* handle performed effects

## What are Effects & Handlers?

**Algebraic effects and handlers** offer a modular mechanism for abstracting computational effects, much like monads.
The theory of algebraic effects was initially developed by Gordon Plotkin, John Power, and others. The generalized formulation of handlers was later established by Gordon Plotkin and Matija Pretnar in their paper, [“Handlers of Algebraic Effects”](https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf).
In recent years, some programming languages supporting effect handlers have emerged. For instance, OCaml introduced an effect handler runtime and API in version 5.0, and has further expanded dedicated syntax across the subsequent 5.x series (see [OCaml Manual: Effect handlers](https://ocaml.org/manual/5.3/effects.html)).

To put it simply, an effect handler is a "*resumable exception.*"
Exceptions are a familiar concept to most developers. The following JavaScript code throws an exception when the argument is 0:

```js
function recipWithExcn(n) {
  if (n === 0) {
    throw new Error("n is zero!");
  }
  return 1 / n;
}
```

This function can be wrapped in a `try...catch` block to handle the exception:

```js
function handleRecip(n) {
  try {
    const m = n - 1;
    const r = recipWithExcn(m);
    console.log(`The reciprocal of ${n} - 1 is: ${r}`);
  } catch (e) {
    console.log(e.message);
  }
}
```

When this function is called with `1`, `recipWithExcn` throws an exception, and the control flow immediately jumps to the catch clause. The exception is handled there, the message `n is zero!` is printed to the standard output, and the program terminates.
As shown here, once an exception is thrown, the control flow is caught and must be handled entirely within the catch clause; it is impossible to resume execution from where the exception originated.

Effect handlers enhance this exception mechanism by **allowing the program to resume from the throw (or perform) site after handling the effect**. For example:

```js
// Pseudo-code assuming effect handler syntax

effect Message {
  msg(string): string;
}

function recipWithMsg(n) {
  if (n === 0) {
    const msg = perform Message.msg("n is zero!");
    return msg;
  }
  return `The reciprocal of ${n} is: ${1 / n}`;
}

function handleRecip(n) {
  try {
    const m = n - 1;
    const msg = recipWithMsg(m);
    console.log("Received: " + msg);
  }
  handle Message.msg(msg, k) {
    resume k msg;
  }
}
```

Instead of throwing an exception, this program *performs* a `Message.msg` operation. This shifts control to the innermost handler capable of handling that operation. Unlike an exception's catch clause, the handle clause receives both the operation's argument `msg` and a **continuation** `k`. k is a delimited continuation, captured from the remaining computation immediately following the perform site up to the corresponding handler boundary.

Executing `resume k msg` inside the handler clause resumes the suspended computation, making it appear as though the `perform Message.msg(...)` expression simply evaluated to and returned the value `msg`.Therefore, running `handleRecip(1)` first performs `Message.msg` with `n is zero!`. The handler passes the same string back to the continuation using `resume`. Ultimately, the `console.log` at the original perform site prints the following message:

```plain
Received: n is zero!
```

While this particular example might not fully showcase the benefits (admittedly, it is a poor example—sorry!), the decisive difference from exceptions is that the suspended computation is explicitly passed to the handler as the continuation k. This means that **programmers can choose when to resume the continuation, what value to pass back, or whether to resume it at all**. For instance, discarding the continuation without calling resume reproduces behavior similar to standard exceptions:

```js
// Pseudo-code
function handleLikeException(n) {
  try {
    const m = n - 1;
    const msg = recipWithMsg(m);
    console.log(msg);
  }
  handle Message.msg(msg, _) {
    console.log(msg);
  }
}
```

Furthermore, in systems that support multi-shot continuations (yes, Hoop does!), you can resume the exact same continuation multiple times:

```js
// Pseudo-code
function handle3Times(n) {
  try {
    const m = n - 1;
    const msg = recipWithMsg(m);
    console.log(msg);
  }
  handle Message{ 
    msg (msg, k) {
      resume k(msg);
      resume k(msg + " again!");
      resume k("One more time, " + msg);
    }
  }
}
```

Now you should have a solid grasp of what effect handlers are. The following sections will guide you through how to define, perform, and handle effects concretely using Hoop.

## Define Effects

First, declare an abstract effect type. In Hoop, these effects have a dedicated kind called `EffType`.
To declare data types of a kind other than `Type`, use the `foreign import data` idiom:

```purs
import Hoop (EffType)

foreign import data Emit :: EffType
```

Next, define the operations that belong to this effect:

```purs
import Hoop (EffNewtype)

type Emit' = ( emit :: Unit ->* Int )

instance EffNewtype Emit Emit'
```

This specifies that the Emit effect contains a single operation, `emit`.
Notice that the signature of the emit operation uses a weired `->*` arrow. This indicates that `emit` is not a standard function, but an **effectful operation**. This signature conveys two pieces of information:

* `emit` is invoked with a `Unit` argument -- meaning the handler for the emit action takes `Unit` as its payload.
* The handler must supply an `Int` value when resuming the captured continuation.

Using `EffNewtype`, we declare that the opaque `Emit` effect is **represented** by the set of operations defined in `Emit'`.

Following standard convention, it is also helpful to define a corresponding effect row alias:

```purs
type EMIT r = ( emit :: Emit | r )
```

## Perform Effectful Actions

Now, let's write a program that uses the `Emit` effect. In Hoop, you trigger an effect using the `perform` keyword:

```purs
import Hoop (perform)

program :: Hoop (EMIT ()) (Array Int)
program = do
  n1 <- perform @(EMIT ()) @"emit" unit
  n2 <- perform @(EMIT ()) @"emit" unit
  n3 <- perform @(EMIT ()) @"emit" unit

  pure [n1, n2, n3]
```

Notice that we provide two pieces of type information to perform via [Visible Type Application (VTA)](https://github.com/purescript/purescript/issues/3137).
The first type is the effect row closed with an empty row, `EMIT ()`, and the second type uses a `Symbol` (i.e. type-level string) to specify the particular operation, `"emit"`, belonging to the `Emit` effect.
The entire program's type follows the format `Hoop (effect row) (output type)`.
In the example above, the program only entails the `Emit` effect and outputs an `Array Int`, yielding the type `Hoop (EMIT ()) (Array Int)`.
Because effects are tracked within row labels, multiple effects can be composed naturally:

```purs
import Type.Row (type (+))

foreign import data State :: Type -> EffType
type State' s = ( get :: Unit ->* s
                , put :: s ->* Unit
                )
instance EffNewtype (State s) (State' s)

program2 :: Hoop (EMIT + STATE Int) Unit
program2 = do
  s0 <- perform @(STATE _) @"get" unit
  n1 <- perform @(EMIT ()) @"emit" unit
  n2 @- perform @(EMIT ()) @"emit" unit
  n3 <- perform @(EMIT ()) @"emit" unit
  put (s0 + n3)
  pure $ map (_ + s0) [n1, n2, n3]
```

To avoid calling perform manually every time, it is highly recommended to wrap the operation into a clean API function:

```purs
emit :: forall r. Hoop (EMIT r) Int
emit = perform @(EMIT ()) @"emit" unit
```

Using this helper makes your program significantly more concise:

```purs
program :: Hoop (EMIT ()) (Array Int)
program = do
  n1 <- emit
  n2 <- emit
  n3 <- emit

  pure [n1, n2, n3]
```

## Handle Effectful Actions

To handle effects, use the with handler syntax as follows:

```purs
import Hoop (handler, with)

program3 :: Hoop () (Array Int)
program3 = 
  with
    (handler
      { emit: { emit: \_ k -> continue k 42 }
      }
    )
    program
```

The function `\_ k -> continue k 42` acts as the body of the Emit effect handler, accepting two arguments.
The first argument is the action's payload (a `Unit` value, discarded here via `_`), and the second argument is the delimited continuation.
Inside the handler, you can resume execution by supplying a value to the continuation using `continue`.
Notice that `program3` now has the type `Hoop () (Array Int)`. Because the with block handles the Emit effect originally present in program, that effect is eliminated from the resulting effect row. Now, you can extract the final output value using `run`:

```purs
run program3 -- [42, 42, 42]
```

This covers the most basic usage of Hoop: defining an effect and its operations, triggering it via `perform @EFFECT @"op"`, and handling it via `with (handler h)`.

## Controllability

As mentioned earlier, Hoop supports multi-shot continuations, allowing you to invoke the continuation at any point and any number of times (including zero) inside a handler.
However, in practice, such fine-grained control is often unnecessary. In the `emit` example above, the handler simply calls `continue k` exactly once at the **tail position** of the handler.
For such scenarios, you should use `fast`-marked handlers:

```purs
program3' :: Array Int
program3' = run
  with
    (handler
      { emit: fast \_ -> pure 42 
      }
    )
    program
```

> *Note*: For an effect consisting of a single operation like `Emit`, you can write the handler as a direct function rather than a record.

A fast-handler does not receive the continuation explicitly. In contrast, handlers that explicitly take a continuation `k` are called full-handlers (*fully-controllable* handlers). While we omitted the `full` marker in previous snippets, a handler written as a plain function is actually a shorthand notation for a full-handler:

```purs
program3 :: Array Int
program3 = run
  with
    (handler
      -- fully-controllable handler
      { emit: full \_ k -> continue k 42 
      }
    )
    program
```

For fast-handlers, the runtime implicitly invokes the continuation exactly once at the end of the handler. Conceptually, a fast-handler is syntactic sugar that expands into a full-handler like so:

```purs
fast \payloads -> m == full \payloads k -> do
                              o <- m payloads
                              continue k o
```

By trading off full controllability for a "one-shot tail call" restriction, fast-handlers run significantly faster than full handlers.
If your logic does not strictly require the advanced control flows of a full-handler, we highly recommend to use a fast-handler.

## Handler-local Mutable Cells

The previous `Emit` handler always returned a constant `42`, which is a bit uninspiring. Let's make it stateful using a **handler-local cell**:

```purs
program4 :: Array Int
program4 = run
  with
    (var 0 \c -> 
      handler
        { emit: fast \_ k -> do
            n <- read c
            c := (n + 1)
            continue k n 
        }
    )
    program
```

This handler leverages `var` syntax to spin up a local mutable cell scoped strictly within the handler, updating it inside the `emit` handler.
Running this program increments the cell's state on each `emit` invocation, successfully returning an array containing sequential numbers like `[0, 1, 2]`.
