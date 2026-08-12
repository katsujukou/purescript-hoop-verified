-- EXPECT: `%hoop.var` is reserved for prompt-local cells
--
-- The other half of the same bypass: the reserved-label guard lives on
-- `PerformScopedEffect`, and `PerformScopedOp` sits below it. Spelling the row
-- out was all it took. The guard is now repeated on the lower class, exactly as
-- `performEffectVar` repeats `PerformList`'s.
module CompileFail where

import Prelude

import Hoop.Engine (Hoop, performScopedOp)
import Hoop.Types (class EffNewtype, EffType, HSig, Scoped)

newtype Once :: HSig
newtype Once m a = Once (m a)

foreign import data Sc :: EffType

type Sc' = (op :: Scoped Once)

instance EffNewtype Sc Sc'

badVar
  :: forall r a
   . Hoop ("%hoop.var" :: Sc | r) a
  -> Hoop ("%hoop.var" :: Sc | r) a
badVar p = performScopedOp @"%hoop.var" @Sc @Sc' @"op" @(Scoped Once) (Once p)
