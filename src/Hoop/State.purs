module Hoop.State where

import Prelude

import Hoop.Engine (Hoop, perform)
import Hoop.Types (class EffNewtype, type (->*), EffType)

foreign import data State :: Type -> EffType

type State' s = 
  ( get :: Unit ->* s 
  , set :: s ->* Unit 
  )

instance EffNewtype (State s) (State' s) 

type STATE s r = (state :: State s | r)

get :: forall s r. Hoop (STATE s r) s 
get = perform @(STATE _ ()) @"get" unit 

set :: forall s r. s -> Hoop (STATE s r) Unit 
set = perform @(STATE _ ()) @"set"

