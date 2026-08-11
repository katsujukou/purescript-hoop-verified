-- @inline export mkAction1.mkAction arity=4
-- @inline export mkAction2.mkAction arity=4
-- @inline export mkAction3.mkAction arity=4
-- @inline export mkAction4.mkAction arity=4
-- @inline export mkAction5.mkAction arity=4

-- @inline export full always
-- @inline export fast always
-- @inline export unClause always

-- @inline export mkRegion always
-- @inline export scalar always

module Hoop.Types
  ( Action
  , AlgOnly
  , AllowScoped
  , AnyPayload
  , Clause
  , Computation
  , Controllability(..)
  , EffType(..)
  , EvKey(..)
  , Fast
  , Full
  , HCapability
  , HSig
  , Local
  , Region
  , Scalar(..)
  , Scoped
  , asAnyPayload
  , class EffNewtype
  , class MkAction
  , evKey
  , fast
  , full
  , mkAction
  , mkRegion
  , scalar
  , type (->*)
  , unClause
  ) where

import Prelude

import Data.Function.Uncurried (Fn4, runFn4)
import Data.String as String
import Fmt as Fmt
import Hoop.TypeUtil (class NonEmpty, type (:), List, Nil)
import Unsafe.Coerce (unsafeCoerce)

data EffType

class EffNewtype :: EffType -> Row Type -> Constraint
class EffNewtype eff repr | eff -> repr

foreign import data Computation :: Type -> Type -> Type

infix 0 type Computation as ->*

-- | **The kind of a higher-order operation's payload shape.**
-- |
-- | A scoped operation's argument is not a tuple of values but a
-- | *container of computations* the clause will choose between: `catch`'s
-- | `{ try, recover }`, `once`'s single body. The container is written by
-- | whoever declares the operation, parameterised by the computation
-- | constructor so that the same shape reads as `Hoop inner` at a perform
-- | site and as something the clause may run under `weave` inside a clause.
-- |
-- | ```purs
-- | newtype OnceScope :: HSig
-- | newtype OnceScope m a = OnceScope (m a)
-- |
-- | newtype CatchScope :: Type -> HSig
-- | newtype CatchScope e m a = CatchScope { try :: m a, recover :: e -> m a }
-- | ```
-- |
-- | The runtime never looks inside one. That is the point: locating the
-- | embedded computations generically is exactly the `HFunctor` traversal
-- | this design exists to avoid, so the clause — which knows the shape it
-- | declared — destructures it and the machine only supplies the capability
-- | to run what the clause picked.
type HSig = (Type -> Type) -> Type -> Type

-- | **The marker for a scoped operation in an effect's signature row**,
-- | standing where `a ->* b` stands for an ordinary one.
-- |
-- | ```purs
-- | type Nd' =
-- |   ( choice :: Unit ->* Boolean
-- |   , once   :: Scoped OnceScope
-- |   )
-- | ```
-- |
-- | It is the single source of truth from which both sides are derived: the
-- | perform helper becomes `h (Hoop eff) b -> Hoop eff b`, and the clause is
-- | required to be a `Hoop.Engine.ScopedClause`. Nothing else distinguishes
-- | the two kinds of operation, which is why they cannot drift apart.
foreign import data Scoped :: HSig -> Type

-- | **What kind of clause a handler is being built to admit.** An index on
-- | `Hoop.Engine.HHandler`, and the mechanism that keeps a scoped clause out of
-- | the ordinary construction path.
-- |
-- | It is a permission, not a description: the same clause record may be
-- | admissible under one capability and rejected under another, and which one
-- | applies is decided by what the handler is eventually *used* by — `with`
-- | fixes it to `AlgOnly`, `handlerScoped` to `AllowScoped`.
-- |
-- | Why this is a dedicated kind rather than a `Boolean`: a reader meeting
-- | `HHandler True ...` has to go looking for what the flag means, and there is
-- | no room to add a third alternative when general higher-order operations or
-- | latent ones arrive. A nominal kind names each permission and stays open.
data HCapability

-- | Ordinary algebraic operations only. A `scoped` clause under this capability
-- | is a type error, and that is what makes the ordinary `Handler` safe: a
-- | scoped clause needs its handler re-instantiated at the scope's result type,
-- | which a single `Handler` cannot supply.
foreign import data AlgOnly :: HCapability

-- | Scoped clauses admitted. Reachable only as the argument of
-- | `Hoop.Engine.handlerScoped`, which quantifies the answer type so that the
-- | whole clause table is checked at *every* result type rather than at one.
foreign import data AllowScoped :: HCapability

data Controllability

foreign import data Full :: Controllability
foreign import data Fast :: Controllability

-- | A handler clause tagged with its controllability. `f` is the raw
-- | handler function type, kept whole: the Engine unifies it with the
-- | canonical type computed from the operation signature, so the marker
-- | itself carries no constraints and never blocks inference.
-- |
-- | A `newtype`, not a `foreign import data`: the marker really is just `f`
-- | carrying a type-level tag, so `full` / `fast` / `unClause` are the
-- | constructor and its inverse rather than three coercions. The constructor
-- | is not exported, so the tag can only be attached by `full` or `fast`.
newtype Clause :: Controllability -> Type -> Type
newtype Clause c f = Clause f

-- `c` is phantom in the representation, which would let `coerce` retag a
-- `fast` clause as `full` -- exactly the confusion the tag exists to prevent.
-- The Engine picks the runtime clause constructor off this tag, so a retag is
-- a calling-convention error, not a harmless one. Pinned nominal.
type role Clause nominal representational

-- | Mark a clause as fully controllable: it receives the delimited
-- | continuation as its last argument and may resume it any number of
-- | times, including none.
full :: forall f. f -> Clause Full f
full = Clause

-- | Mark a clause as tail-resumptive: the body computes the operation's
-- | result (performing effects of the outer context if needed) and
-- | resumes exactly once, immediately.
-- |
-- | Cost model: the continuation is never captured. A `Pure` body
-- | resumes in place at zero cost; an effectful body also runs in
-- | place, under the handler's own evidence environment (its effects
-- | reach the outer context without touching the stack).
fast :: forall f. f -> Clause Fast f
fast = Clause

unClause :: forall c f. Clause c f -> f
unClause (Clause f) = f

-- | **The open-region token.** A computation whose row carries
-- | `"%hoop.var" :: Local s inits` runs with the cells `inits` installed,
-- | in the region `s`. It is the surface reading of the runtime's
-- | capability judgement: `Hoop.Runtime.WellScopedness` makes a `ReadP l`
-- | well scoped exactly when `can var_eff l` holds, and cells share the
-- | capability environment with handlers under the reserved effect name
-- | `%hoop.var`.
-- |
-- | The token is coarser than the runtime judgement -- one entry per
-- | region rather than one per cell -- and soundly so: a region is open
-- | precisely while every one of its cell frames is installed, so an open
-- | token entails `can var_eff l` for each `l` in `inits`.
-- |
-- | `s` is a phantom: `var` quantifies it rank-2, which is what stops a
-- | cell of one region being read in another that happens to declare the
-- | same label at the same type.
-- |
-- | No handler may be written for this label -- `Hoop.Engine` fails the
-- | attempt with a custom error, and the runtime could not represent such
-- | a table anyway (`Hoop.Runtime.Handlers.keys_no_var`).
foreign import data Local :: Type -> Row Type -> EffType

-- | The capability to reach the cells of one open region: `s` identifies
-- | the region, `inits` declares its cells. `read` and `write` take the
-- | region and name the cell by a visible type application, so there is no
-- | per-cell handle to hold -- and therefore none to let slip.
-- |
-- | This is what makes the scope discipline lexical rather than dynamic.
-- | `s` is bound by the rank-2 `forall` in `Hoop.Engine.var`, so nothing
-- | mentioning it -- neither the region nor a computation that uses it --
-- | can leave through an operation's result, the answer type or a
-- | continuation, all of which are fixed outside the region.
-- |
-- | The token carries nothing: a cell's runtime name is its label, and the
-- | label is recovered from the type at each `read` and `write`.
newtype Region :: Type -> Row Type -> Type
newtype Region s inits = Region Unit

mkRegion :: forall s inits. Region s inits
mkRegion = Region unit

-- | Declare a region of one cell holding a record.
-- |
-- | `var` reads a bare initial value as a single unnamed cell and a record
-- | as one cell per field, which leaves no way to ask for a single cell
-- | whose contents happen to be a record. This wrapper is that way.
-- |
-- | ```purs
-- | var (scalar { x: 0, y: 0 }) \c -> read c   -- one cell, a record inside
-- | var { x: 0, y: 0 } \c -> read @"x" c       -- two cells
-- | ```
newtype Scalar a = Scalar a

scalar :: forall a. a -> Scalar a
scalar = Scalar

newtype EvKey = EvKey String

derive newtype instance eqEvKey :: Eq EvKey
derive newtype instance ordEvKey :: Ord EvKey

evKey :: String -> String -> EvKey
evKey eff op = EvKey $ Fmt.fmt @"{len}:{eff}{op}" { len: String.length eff, eff, op }

foreign import data AnyPayload :: Type

asAnyPayload :: forall a. a -> AnyPayload
asAnyPayload = unsafeCoerce

-- | `key` is the machine's evidence-environment key for (eff, op). It
-- | is passed in precomputed (Hoop.Engine derives it once per operation
-- | helper, outside the payload lambda), so a perform allocates no key
-- | string.
type Action = { eff :: String, op :: String, key :: String, payload :: Array AnyPayload }

type MkActionFn r = Fn4 String String String (Array AnyPayload) r

runMkActionFn
  :: forall r
   . MkActionFn r
  -> String -- effect
  -> String -- op
  -> String -- evkey
  -> Array AnyPayload
  -> r
runMkActionFn = runFn4

class MkAction :: List Type -> Type -> Type -> Constraint
class NonEmpty args <= MkAction args r fn | args r -> fn where
  mkAction :: String -> String -> EvKey -> (MkActionFn r) -> fn

instance mkAction1 :: MkAction (a : Nil) r (a -> r) where
  mkAction eff op (EvKey key) k = \a -> runMkActionFn k eff op key [ asAnyPayload a ]

else instance mkAction2 :: MkAction (a : b : Nil) r (a -> b -> r) where
  mkAction eff op (EvKey key) k = \a b -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b ]

else instance mkAction3 :: MkAction (a : b : c : Nil) r (a -> b -> c -> r) where
  mkAction eff op (EvKey key) k = \a b c -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c ]

else instance mkAction4 :: MkAction (a : b : c : d : Nil) r (a -> b -> c -> d -> r) where
  mkAction eff op (EvKey key) k = \a b c d -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d ]

else instance mkAction5 :: MkAction (a : b : c : d : e : Nil) r (a -> b -> c -> d -> e -> r) where
  mkAction eff op (EvKey key) k = \a b c d e -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d, asAnyPayload e ]

else instance mkAction6 :: MkAction (a : b : c : d : e : f : Nil) r (a -> b -> c -> d -> e -> f -> r) where
  mkAction eff op (EvKey key) k = \a b c d e f -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d, asAnyPayload e, asAnyPayload f ]

else instance mkAction7 :: MkAction (a : b : c : d : e : f : g : Nil) r (a -> b -> c -> d -> e -> f -> g -> r) where
  mkAction eff op (EvKey key) k = \a b c d e f g -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d, asAnyPayload e, asAnyPayload f, asAnyPayload g ]

else instance mkAction8 :: MkAction (a : b : c : d : e : f : g : h : Nil) r (a -> b -> c -> d -> e -> f -> g -> h -> r) where
  mkAction eff op (EvKey key) k = \a b c d e f g h -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d, asAnyPayload e, asAnyPayload f, asAnyPayload g, asAnyPayload h ]

else instance mkAction9 :: MkAction (a : b : c : d : e : f : g : h : i : Nil) r (a -> b -> c -> d -> e -> f -> g -> h -> i -> r) where
  mkAction eff op (EvKey key) k = \a b c d e f g h i -> runMkActionFn k eff op key [ asAnyPayload a, asAnyPayload b, asAnyPayload c, asAnyPayload d, asAnyPayload e, asAnyPayload f, asAnyPayload g, asAnyPayload h, asAnyPayload i ]
