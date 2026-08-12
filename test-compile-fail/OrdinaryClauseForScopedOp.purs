-- EXPECT: This is a scoped operation, so its clause must be built with `scoped`
--
-- The signature classes are what tell a user which marker an operation wants.
-- Without this arm the message is "must be Function (->) or Computation (->*)",
-- which is true of ordinary operations and no help here.
module CompileFail where

import Prelude

import Data.Either (Either(..))
import Data.Void (Void)
import Hoop.Engine (HHandler, handler)
import Hoop.Types (class EffNewtype, type (->*), AllowScoped, EffType, HSig, Scoped, full)
import Type.Proxy (Proxy(..))

foreign import data Exc :: EffType

newtype Catch :: HSig
newtype Catch m a = Catch { try :: m a, recover :: String -> m a }

type Exc' = (throw :: String ->* Void, catch :: Scoped Catch)

instance EffNewtype Exc Exc'

type EXC r = (exc :: Exc | r)
type EXC1 = EXC ()

runExc :: forall r b. HHandler AllowScoped EXC1 r b (Either String b)
runExc = handler (Proxy :: _ EXC1)
  { exc:
      { throw: full \msg _k -> pure (Left msg)
      , catch: full \_payload _k -> pure (Left "no")
      }
  , pure: Right
  }
