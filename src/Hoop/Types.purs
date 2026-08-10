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
  , AnyPayload
  , Clause
  , Computation
  , Controllability(..)
  , EffType(..)
  , EvKey(..)
  , Fast
  , Full
  , Local
  , Region
  , Scalar(..)
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

data Controllability

foreign import data Full :: Controllability
foreign import data Fast :: Controllability

-- | A handler clause tagged with its controllability. `f` is the raw
-- | handler function type, kept whole: the Engine unifies it with the
-- | canonical type computed from the operation signature, so the marker
-- | itself carries no constraints and never blocks inference.
foreign import data Clause :: Controllability -> Type -> Type

-- | Mark a clause as fully controllable: it receives the delimited
-- | continuation as its last argument and may resume it any number of
-- | times, including none.
full :: forall f. f -> Clause Full f
full = unsafeCoerce

-- | Mark a clause as tail-resumptive: the body computes the operation's
-- | result (performing effects of the outer context if needed) and
-- | resumes exactly once, immediately.
-- |
-- | Cost model: the continuation is never captured. A `Pure` body
-- | resumes in place at zero cost; an effectful body also runs in
-- | place, under the handler's own evidence environment (its effects
-- | reach the outer context without touching the stack).
fast :: forall f. f -> Clause Fast f
fast = unsafeCoerce

unClause :: forall c f. Clause c f -> f
unClause = unsafeCoerce

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
