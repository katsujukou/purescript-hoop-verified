-- @inline export mkAction1.mkAction arity=4
-- @inline export mkAction2.mkAction arity=4
-- @inline export mkAction3.mkAction arity=4
-- @inline export mkAction4.mkAction arity=4
-- @inline export mkAction5.mkAction arity=4

-- @inline export full always
-- @inline export fast always
-- @inline export unClause always

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
  , asAnyPayload
  , class EffNewtype
  , class MkAction
  , evKey
  , fast
  , full
  , mkAction
  , type (->*)
  , unClause
  )
  where

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
  -> String   -- effect
  -> String   -- op
  -> String   -- evkey
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
