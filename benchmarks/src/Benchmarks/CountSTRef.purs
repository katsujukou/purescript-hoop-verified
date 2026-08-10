module Benchmarks.CountSTRef where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Control.Monad.ST (for, run) as ST
import Control.Monad.ST.Ref (modify, new, read) as STRef
import Effect (Effect)
import Effect.Console (logShow)

main :: Effect Unit
main = do
  n <- sizeArg
  logShow $ ST.run do
    acc <- STRef.new 0
    ST.for 0 n \i ->
      when (i `mod` 2 == 0) do
        void (STRef.modify (_ + i) acc)
    STRef.read acc
