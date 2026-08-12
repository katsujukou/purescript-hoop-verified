-- EXPECT: TypesDoNotUnify
-- EXPECT: Once
--
-- `PerformScopedOp` is the last step of the scoped perform chain and sits BELOW
-- both checks that make a perform site trustworthy. While it lacked them, this
-- compiled with `Sc`'s real representation being `Scoped Once`.
--
-- It cannot simply be hidden: PureScript needs a class in scope to discharge it
-- at a use site, so a chain reachable from an exported method must be exported
-- in full. The checks are repeated on it instead.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performScopedOp)
import Hoop.Types (class EffNewtype, EffType, HSig, Scoped)

newtype Once :: HSig
newtype Once m a = Once (m a)

newtype Twice :: HSig
newtype Twice m a = Twice { one :: m a, two :: m a }

foreign import data Sc :: EffType

type Sc' = (op :: Scoped Once)

instance EffNewtype Sc Sc'

type SC r = (sc :: Sc | r)

bad :: forall r a. Hoop (SC r) a -> Hoop (SC r) a -> Hoop (SC r) a
bad p q = performScopedOp @"sc" @Sc @Sc' @"op" @(Scoped Twice) (Twice { one: p, two: q })
