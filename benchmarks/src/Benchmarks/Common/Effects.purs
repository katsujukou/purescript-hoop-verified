module Benchmarks.Common.Effects where

import Prelude

import Data.Tuple (Tuple(..))
import Hoop (class EffNewtype, type (->*), EffType, Handler, Hoop, continue, fast, full, handler, perform, read, scalar, var, with, (:=))
import Type.Proxy (Proxy(..))

foreign import data State :: Type -> EffType

type State' s =
  ( get :: Unit ->* s
  , put :: s ->* Unit
  )

instance EffNewtype (State s) (State' s)

type STATE s r = (state :: State s | r)

get :: forall s r. Hoop (STATE s r) s
get = perform @(STATE _ ()) @"get" unit

put :: forall s r. s -> Hoop (STATE s r) Unit
put = perform @(STATE _ ()) @"put"

stateVarH :: forall s r a. s -> Handler (STATE s ()) r a a
stateVarH s = var (scalar s) \h ->
  handler (Proxy :: _ (STATE _ ()))
    { state:
        { get: fast \_ -> read h
        , put: fast \s' -> h := s'
        }
    }

stateFullH :: forall s a r. Handler (STATE s ()) r a (s -> Hoop r (Tuple a s))
stateFullH =
  ( handler (Proxy :: _ (STATE _ ()))
      { pure: \a s -> pure (Tuple a s)
      , state:
          { get: full \_ k -> pure \s -> continue k s >>= \f -> f s
          , put: full \s' k -> pure \_ -> continue k unit >>= \f -> f s'
          }
      }
  )

-- Exceptions ----------------------------------------------------------------

foreign import data Exc :: EffType

type Exc' = (throw :: String ->* Unit)

instance EffNewtype Exc Exc'

type EXC r = (exc :: Exc | r)

throw :: forall r. String -> Hoop (EXC r) Unit
throw = perform @(EXC ()) @"throw"

-- | The general combinator: the recovery is closed over, so the handler
-- | table is rebuilt on every call. This is what a library would export.
catch :: forall r a. Hoop (EXC r) a -> (String -> Hoop r a) -> Hoop r a
catch action recover =
  with (handler (Proxy :: _ (EXC ())) { exc: \msg _k -> recover msg }) action

-- | The same handler with the recovery fixed, so the whole thing is a CAF and
-- | the table is built once at module init. Not a general `catch` -- it is the
-- | control for how much of `catch`'s cost is table construction.
catchUnitH :: forall r. Handler (EXC ()) r Unit Unit
catchUnitH = handler (Proxy :: _ (EXC ())) { exc: \_ _k -> pure unit }
