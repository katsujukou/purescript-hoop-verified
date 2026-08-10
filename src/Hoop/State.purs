module Hoop.State where

import Prelude

import Hoop.Engine (Handler, Hoop, handler, perform, read, var, (:=))
import Hoop.Types (class EffNewtype, type (->*), EffType, fast, scalar)
import Type.Proxy (Proxy(..))

foreign import data State :: Type -> EffType

type State' s =
  ( get :: Unit ->* s
  , set :: s ->* Unit
  )

instance EffNewtype (State s) (State' s)

type STATE s r = (state :: State s | r)

get :: forall s r. Hoop (STATE s r) s
get = perform @(STATE _ ()) @"get" unit

set :: forall s r. s -> Hoop (STATE s r) Unit
set = perform @(STATE _ ()) @"set"

-- | A state handler backed by a prompt-local cell, polymorphic in the
-- | state type. Both operations are tail-resumptive, so neither captures
-- | the continuation.
-- |
-- | The answer is `a`, not `a /\ s`: the final state is not handed back.
-- | That is the `ST` reading of cells and is deliberate -- see `var`. For
-- | the final state, use the parameter-passing handler instead, which
-- | costs the tail resumption.
-- |
-- | Note `scalar`. `var` reads a record as one cell per field and anything
-- | else as a single cell, and with `s` abstract it cannot tell which this
-- | is -- the dispatch stalls on the record instance rather than falling
-- | through. `scalar` names the intended reading, which is what a handler
-- | polymorphic in the cell's type has to do. See the note on `var`.
handleState :: forall s r a. s -> Handler (STATE s ()) r a a
handleState init = var (scalar init) \c ->
  handler (Proxy :: _ (STATE s ()))
    { state:
        { get: fast \_ -> read c
        , set: fast \s' -> c := s'
        }
    }

