module Benchmarks.CountEffectRef where

import Prelude

import Benchmarks.Common.Args (sizeArg)
import Effect (Effect, forE)
import Effect.Console (logShow)
import Effect.Ref as Ref

main :: Effect Unit
main = do
  n <- sizeArg
  acc <- Ref.new 0
  forE 0 n \i ->
    -- `when` (Applicative `pure`) + `void` (Functor `map`) + `Ref.modify` (an effectful foreign),
    -- so the loop body spans the whole dictionary surface GER lowers, not only `bind`/`discard`.
    when (i `mod` 2 == 0) do
      void (Ref.modify (_ + i) acc)
  total <- Ref.read acc
  logShow total
