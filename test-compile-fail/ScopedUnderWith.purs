-- EXPECT: A scoped operation cannot be handled by an ordinary `handler`
-- EXPECT: exc.catch
--
-- The defect this fixture pins: before the capability index, a table carrying
-- a scoped clause could be installed with ordinary `with`, and a scope would
-- then run under a return clause built for one answer type only.
module CompileFail where

import Prelude

import Data.Either (Either(..))
import Data.Void (Void, absurd)
import Hoop.Engine (Hoop, handler, perform, performScoped, scoped, with)
import Hoop.Types (class EffNewtype, type (->*), EffType, HSig, Scoped, full)
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

runExcWith :: forall r. Hoop (EXC r) Int -> Hoop r (Either String Int)
runExcWith = with
  ( handler (Proxy :: _ EXC1)
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
  )
