-- EXPECT: This operation is not scoped, so it cannot be performed with `performScoped`
--
-- The mirror image of the clause-side guard: `performScoped` builds a `PerformS`
-- node, and a `PerformS` dispatched against an ordinary clause is a runtime
-- rejection. It is refused here instead.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performScoped)
import Hoop.Types (class EffNewtype, type (->*), EffType)

foreign import data Ask :: EffType

type Ask' = (ask :: Unit ->* Int)

instance EffNewtype Ask Ask'

type ASK r = (ask :: Ask | r)
type ASK1 = ASK ()

bad :: forall r. Hoop (ASK r) Int
bad = performScoped @ASK1 @"ask" unit
