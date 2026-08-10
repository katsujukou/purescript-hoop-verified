-- @inline export varA always
-- @inline export varC always

module Test.HoistProbe where

import Prelude

import Hoop.Engine (Handler, handler, read, var, (:=))
import Hoop.State (STATE)
import Hoop.Types (Local, Region, fast, mkRegion, scalar)
import Type.Proxy (Proxy(..))

-- A: today's shape. The table is built under the `s =>` lambda.
varA :: forall s r a. s -> Handler (STATE s ()) r a a
varA s = var (scalar s) \h ->
  handler (Proxy :: _ (STATE s ()))
    { state:
        { get: fast \_ -> read h
        , set: fast \s' -> h := s'
        }
    }

-- C: the table as a polymorphic CAF; the region comes from `mkRegion`, so the
-- handler no longer mentions `var`'s callback argument at all.
tableC
  :: forall sk s r a
   . Handler (STATE s ()) ("%hoop.var" :: Local sk ("%hoop.scalar" :: s) | r) a a
tableC =
  handler (Proxy :: _ (STATE s ()))
    { state:
        { get: fast \_ -> read (mkRegion :: Region sk ("%hoop.scalar" :: s))
        , set: fast \s' -> (mkRegion :: Region sk ("%hoop.scalar" :: s)) := s'
        }
    }

varC :: forall s r a. s -> Handler (STATE s ()) r a a
varC s = var (scalar s) \_ -> tableC
