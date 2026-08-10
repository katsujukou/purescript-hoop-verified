module Benchmarks.CountStateFull where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Benchmarks.Common.Effects (STATE, get, put, stateFullH)
import Effect (Effect)
import Effect.Console (logShow)
import Hoop (Hoop, run, with)

count :: forall r. Int -> Hoop (STATE Int r) Unit
count i =
  if i == 0 then pure unit
  else do
    s <- get
    put (s + 1)
    count (i - 1)

main :: Effect Unit
main = do
  n <- sizeArg
  logShow $ run (run (with stateFullH (count n)) 0) 