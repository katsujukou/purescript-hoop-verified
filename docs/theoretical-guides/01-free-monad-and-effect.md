# Free Monad and Computation Tree

In this chapter, we will explore the **Free Monad**, which serves as the core foundation for algebraic effect and handler systems.

## Free Construction

What does the word "Free" actually mean in the context of a Free Monad? Interestingly, it originates from the mathematical concept of *"Free Construction"*.

In mathematics, you will encounter many structures prefixed with the word "Free" (e.g., Free Monoids, Free Groups, Free Functors, etc). The common thread among them is that **they only satisfy the minimum conditions required to be that specific structure, and absolutely nothing more**.

But what does that actually mean? Let’s look at a concrete example. Most readers are likely familiar with *Monoids*.

A set $M$ is a Monoid if it is equipped with an **associative binary operation**

$$\times :: m \rightarrow m \rightarrow m$$

and a **unit element** (or identity) $\eta \in m$ with respect to this operation. Specifically, for any $m$, $m_1$, $m_2 \in M$, the following laws must hold:

- *Left Identity*: $\eta \times m = m$
- *Right Identity*: $m \times \eta = m$
- *Associativity*: $(m_1 \times m_2) \times m_3 = m_1 \times (m_2 \times m_3)$

In PureScript, as you know, this structure is captured by the following typeclass:

```hs
class Monoid m where
  append :: m -> m -> m 
  mempty :: m 
```

> *Note*
> In the actual Prelude definition, append belongs to the Semigroup class, and Monoid extends Semigroup by defining the mempty method.

Unfortunately, left/right identities and associativity cannot be enforced by the type system itself. Therefore, it is the programmer's responsibility to ensure that instances of the `Monoid` class strictly satisfy these monoid laws.

Like this monoid example, an algebraic structure is typically defined as a "base set (called the **underlying set**) coupled with operations that satisfy certain **laws**". Each individual Monoid is specified as a triple containing the underlying set, the monoid operation, and the unit element.
For instance, addition over integers $(+)$ is associative, and $0$ serves as the identity element, making $(\mathrm{Int}, +, 0)$ a Monoid. Similarly, multiplication over integers $(\times)$ is also associative, and $1$ serves as its identity, meaning $(\mathrm{Int}, \times, 1)$ is a Monoid as well.

Since both are Monoids, they naturally satisfy associativity and the identity laws. In other words, if we only look at the core requirement of "satisfying the Monoid laws," the additive monoid and the multiplicative monoid are indistinguishable. What differentiates them is **the additional structural properties** they possess on top of the laws.

What does it mean? Let’s consider the actual computation. In the additive monoid, $2 + 3 = 5$, whereas in the multiplicative monoid, $2 × 3 = 6$. They produce different results, and this is how we tell them apart. To phrase it a bit more redundantly, the additive monoid is characterized by a **structural mapping** that collapses any two elements into a completely different element (e.g., collapsing the operation of 2 and 3 into 5, 2 and 4 into 6, and so on). A Free Monoid is **a monoid where this structural mapping carries no substantive meaning** -- it is entirely trivial.

Looked at another way, the structural mapping of a typical monoid is a *lossy mapping*. For example, $0 + 5$, $1 + 4$, and $2 + 3$ are all collapsed into the single element $5$. The binary operation of an additive monoid *discards* the information of which two original elements composed it. In contrast, a Free Monoid is a monoid whose binary operation causes **no loss of information**, except for what is strictly required by associativity and identity. That is, in a free monoid over integers, the monoid product of $2$ and $3$ is simply "the monoid product of $2$ and $3$" -- nothing more, nothing less. However, if $\phi$ is the identity element, we can say that "the product of $\phi$ and $2$ is $2$," because the monoid laws demand it.

In short, a Free Monoid does not perform any folding or evaluation beyond what is forced by the monoid laws; its operations simply *accumulate* elements incrementally. And to let the cat out of the bag: `List Int` is precisely the Free Monoid over `Int`, where standard list concatenation (`++`) acts as the monoid operation and the empty list (`[]`) serves as the identity element.

## Free Monads

Now that we’ve gone through that long introduction, we are finally ready for **Free Monads**!

As you well know, a type constructor `m :: Type -> Type` is a monad if it provides two operations:

```hs
(>>=) :: m a -> (a -> m b) -> m b
pure :: a -> m a
```

And these operations must satisfy the three Monad laws:

- *Right identity*: `m >>= pure == m`
- *Left identity*: `pure x >>= f == f x`
- *Associativity*: `(m1 >>= m2) >>= m3 == m1 >>= (\x -> m2 x >>= m3)`

> *Note:*
> Is is not coincidence that the three laws above is so similar to the monoid laws. After all, monad is a monoid in the category of endofunctors, as all you know, huh?

Building on our previous discussion, a free monad is a monoid-like structure that satisfies only these laws, without performing any additional lossy folding (i.e., without identifying the result of `m1 >>= f` as some other distinct element `m2`). In a free monad, the result of a `pure` operation on some `x` is just "the `pure` operation of `x`", and a `bind` operation on `m1` and `f` is just "the `bind` operation of `m1` and `f`" -- nothing more, nothing less.

The most naive way to define a free monad over a functor `f` is given by the following data type:

```hs
data Free f a
  = Pure a 
  | Free (f (Free f a))
```

We can see that this is a truly free construction because we can implement its `Monad` instance without knowing anything about the intrinsic properties of `f`, other than the fact that `f` is a `Functor` (so we can only `map`ing some function over it):

```hs
instance Functor f => Monad (Free f) where
  pure x = Pure x 
  bind m f = 
    case m of 
      Pure x -> f x 
      Free mf -> Free $ map (_ >>= f) mf
```

*Verifying that this instance actually satisfies the Monad laws is left as an exercise for the reader! ;-)*

With this setup, for any given functor `f`, we can define a monad *for free*:

```hs
type T = Free f
```

Since `T` is a lawful Monad, we can write programs using our familiar do syntax:

```hs
t :: T Int
t = do
  x <- t1
  ...
  pure 42
```

Because a Free Monad does not perform lossy folding and instead incrementally accumulates each sub-expression into a data structure, this do block isn't actually performing an active calculation. Instead, it **generates a piece of data** that looks like this:

```hs
t = Bind 
      t1
      (\x -> ... (Pure 42))
```

You can view this as a peculiar kind of tree where the left child node is a concrete value, but the right child node is a thunk. This structural property is exactly why free monads are so widely used for building **Domain-Specific Languages (DSLs)**. A program written inside a free monad's do block is literally the *Abstract Syntax Tree (AST)* of the DSL defined by that monad. 

> *Note*:
> FYI, The following video elegantly explains how a free monad can be seen as a certain generalized tree:
> [Free from Tree](https://www.youtube.com/watch?v=eKkxmVFcd74)

## Codensity, Coyondeda

While the naive definition of *Free* introduced in the previous section is highly intuitive and great for explaining the core concept, a different but equivalent representation is preferred in production.

In a free monad, as long as we only identify terms based on the three monad laws, we are allowed to re-associate or transform the underlying tree into whatever representation best suits our goals. In fact, the [`purescript-free`](https://github.com/purescript/purescript-free) package uses a internal definition that is optimized for performance by transforming the tree into an equivalent representation (see: [Reflection without Remorse](https://dl.acm.org/doi/10.1145/2633357.2633360) paper for further reading).
It might feel a bit out of the blue, but the following alternative format is incredibly convenient for understanding algebraic effect and handler systems:

```hs
-- Unfortunately, in PureScript we cannot put `forall` before data constructor, so this is a conceptual pseudo-code
data Comp f a 
  = Pure a
  | forall b. Bind (f b) (b -> Comp f a)
```

This alternative structure is closely related to the naive version via the **co-yoneda lemma** in category theory. More precisely, it can be viewed as a variation of a *Church-encoded Free Monad* or a *Codensity/Yoneda-transformed Free Monad*. This specific representation is a highly practical optimization: it defers and automatically re-associates monadic binds to the right, resolving the notorious $O(N^2)$ left-associated overhead (the "left-binding dilemma") by ensuring that every `bind` operation is guaranteed to complete in $O(1)$ time. In the following chapters, we will use this specific representation of the free monad to explain Hoop’s algebraic effect and handler system.
