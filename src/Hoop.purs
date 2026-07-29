module Hoop 
  ( module Hoop.Engine
  , module Hoop.Types
  ) where

import Prelude

import Hoop.Engine (Hoop, continue, handler, run, with)
import Hoop.Reader (READER, ask)
import Hoop.State (STATE, get, set)
import Hoop.Types (class EffNewtype, type (->*), Action, EffType, fast, full)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

program :: Hoop (STATE { val :: Int } + READER Int + ()) Int
program = do
  n <- ask
  { val: s } <- get 
  if n > 0 then
    pure 42 
  else do
    set { val: s * n }
    pure (s + 1)
  
main :: Int 
main = run $
  with 
    (handler (Proxy :: _ (STATE { val :: Int } + READER Int + ()))
      { reader: full \_ k -> continue k 42
      , state: 
        { get: full \_ k -> continue k { val: 0 }
        , set: full \_ k -> continue k unit
        }
      })
    program