-- EXPECT: TypesDoNotUnify
-- EXPECT: Computation Unit Int
--
-- A real type-soundness hole, found by asking what else typechecks but
-- misbehaves. `performEffect` is exported and names the effect's REPRESENTATION
-- by type application, and its instance did not require `EffNewtype efftyp
-- repr` -- so the representation was a caller's claim rather than the effect's.
-- `askLying` compiled at `Hoop (ASK r) String`, ran, and returned the handler's
-- `Int`; the failure surfaced later, as `s.replace is not a function`.
--
-- The label-derived path (`PerformList`) always supplied the right `repr`
-- through `EffNewtype`, which is why nothing noticed.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performEffect)
import Hoop.Types (class EffNewtype, type (->*), EffType)

foreign import data Ask :: EffType

type Ask' = (ask :: Unit ->* Int)

instance EffNewtype Ask Ask'

type ASK r = (ask :: Ask | r)

type Lie = (ask :: Unit ->* String)

askLying :: forall r. Hoop (ASK r) String
askLying = performEffect @"ask" @Ask @Lie @"ask" unit
