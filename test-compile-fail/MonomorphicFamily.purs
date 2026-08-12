-- EXPECT: TypesDoNotUnify
-- EXPECT: HHandler AllowScoped
--
-- The other half of the same guarantee: a table pinned at one answer type
-- cannot pose as a family, so nothing reaches `withF` that was not checked at
-- every result type a scope might run at.
module CompileFail where

import Prelude

import Data.Either (Either(..))
import Data.Void (Void, absurd)
import Hoop.Engine (HHandler, HandlerF, Hoop, handler, handlerScoped, perform, performScoped, scoped)
import Hoop.Types (class EffNewtype, type (->*), AllowScoped, EffType, HSig, Scoped, full)
import Type.Proxy (Proxy(..))

foreign import data Exc :: EffType

newtype Catch :: HSig
newtype Catch m a = Catch { try :: m a, recover :: String -> m a }

type Exc' = (throw :: String ->* Void, catch :: Scoped Catch)

instance EffNewtype Exc Exc'

type EXC r = (exc :: Exc | r)
type EXC1 = EXC ()

throwE :: forall r a. String -> Hoop (EXC r) a
throwE msg = absurd <$> perform @EXC1 @"throw" msg

catchE :: forall r a. Hoop (EXC r) a -> (String -> Hoop (EXC r) a) -> Hoop (EXC r) a
catchE try recover = performScoped @EXC1 @"catch" (Catch { try, recover })

runExcAtInt :: forall r. HHandler AllowScoped EXC1 r Int (Either String Int)
runExcAtInt = handler (Proxy :: _ EXC1)
  { exc:
      { throw: full \msg _k -> pure (Left msg)
      , catch: scoped \(Catch rec) t k ->
          t.runScope rec.try >>= case _ of
            Right cx -> t.resumeScope cx k
            Left e -> t.runScope (rec.recover e) >>= case _ of
              Right cx -> t.resumeScope cx k
              Left e' -> pure (Left e')
      }
  , pure: Right
  }

runExcAtIntF :: forall r. HandlerF EXC1 r (Either String)
runExcAtIntF = handlerScoped runExcAtInt
