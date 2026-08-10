module Benchmarks.Common.Effects where

import Prelude

import Data.Tuple (Tuple(..))
import Hoop (class EffNewtype, type (->*), EffType, Handler, Hoop, continue, fast, full, handler, perform, read, scalar, var, (:=))
import Type.Proxy (Proxy(..))

foreign import data State :: Type -> EffType

type State' s =
  ( get :: Unit ->* s 
  , put :: s ->* Unit
  )
  
instance EffNewtype (State s) (State' s)

type STATE s r = ( state :: State s | r )

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