module Benchmarks.CountRun where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Console as Console
import Run (Run)
import Run as Run
import Run.State (STATE, get, put, runState)

count :: forall r. Int -> Run (STATE Int r) Int
count i =
  if i == 0 then get
  else do
    s <- get
    put (s + 1)
    count (i - 1)

main :: Effect Unit
main = do
  n <- sizeArg
  count n
    # runState 0
    # Run.extract
    # fst
    # Console.logShow
