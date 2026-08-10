module Benchmarks.CountMtlState where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Control.Monad.State (State, execState, get, put)
import Effect (Effect)
import Effect.Console (logShow)

count :: Int -> State Int Unit
count = tailRecM go
  where
  go i =
    if i == 0 then pure (Done unit)
    else do
      s <- get
      put (s + 1)
      pure (Loop (i - 1))

main :: Effect Unit
main = do
  n <- sizeArg
  logShow (execState (count n) 0)
