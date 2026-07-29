module Hoop.Reader where

import Prelude

import Hoop.Engine (Hoop, perform)
import Hoop.Types (class EffNewtype, type (->*), EffType)

foreign import data Reader :: Type -> EffType

type Reader' e = ( ask :: Unit ->* e )

instance EffNewtype (Reader e) (Reader' e)

type READER e r = (reader :: Reader e | r)

ask :: forall e r. Hoop (READER e r) e 
ask = perform @(READER _ ()) @"ask" unit 
