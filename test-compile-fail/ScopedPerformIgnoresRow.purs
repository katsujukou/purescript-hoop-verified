-- EXPECT: TypesDoNotUnify
-- EXPECT: e :: Scopey
--
-- A real defect, found by asking whether `Rejected` is reachable from a
-- well-typed program and caught here: `performScoped` originally imposed NO
-- constraint on the row it appears in, because `PerformScopedOp`'s instance
-- head introduced `eff` without the `Row.Cons efflbl efftyp _ eff` that the
-- ordinary `performEffectImpl1` carries. `bad :: forall r. Hoop r Int`
-- compiled, so a scoped operation could be performed into a row that does not
-- declare it -- including the empty one.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performScoped)
import Hoop.Types (class EffNewtype, EffType, HSig, Scoped)

newtype Once :: HSig
newtype Once m a = Once (m a)

foreign import data Scopey :: EffType

type Scopey' = (op :: Scoped Once)

instance EffNewtype Scopey Scopey'

type SCOPEY1 = (e :: Scopey)

bad :: forall r. Hoop r Int
bad = performScoped @SCOPEY1 @"op" (Once (pure 1))
