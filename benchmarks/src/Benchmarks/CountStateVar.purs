module Benchmarks.CountStateVar where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Benchmarks.Common.Effects (STATE, get, put, stateVarH)
import Effect (Effect)
import Effect.Console (logShow)
import Hoop (Hoop, run, with)

count :: forall r. Int -> Hoop (STATE Int r) Int
count i =
  if i == 0 then get
  else do
    s <- get
    put (s + 1)
    count (i - 1)

main :: Effect Unit
main = do
  n <- sizeArg
  logShow $ run $ with (stateVarH 0) (count n)