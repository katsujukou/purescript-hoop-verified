-- EXPECT: TypesDoNotUnify
-- EXPECT: Scoped Once
--
-- The same hole on the scoped path, closed the same way. Worth its own fixture:
-- the two classes are separate instance chains, and a fix to one says nothing
-- about the other.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performScopedEffect)
import Hoop.Types (class EffNewtype, EffType, HSig, Scoped)

newtype Once :: HSig
newtype Once m a = Once (m a)

newtype Twice :: HSig
newtype Twice m a = Twice { one :: m a, two :: m a }

foreign import data Sc :: EffType

type Sc' = (op :: Scoped Once)

instance EffNewtype Sc Sc'

type SC r = (sc :: Sc | r)

type Lie = (op :: Scoped Twice)

bad :: forall r a. Hoop (SC r) a -> Hoop (SC r) a -> Hoop (SC r) a
bad p q = performScopedEffect @"sc" @Sc @Lie @"op" (Twice { one: p, two: q })
