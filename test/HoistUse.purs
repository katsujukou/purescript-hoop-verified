module Test.HoistUse where

import Prelude

import Hoop.Engine (Hoop, run, with)
import Hoop.State (STATE, get, set)
import Test.HoistProbe (varA, varC)

prog :: forall r. Hoop (STATE Int r) Int
prog = do
  a <- get
  _ <- set (a + 1)
  get

useA :: Int
useA = run (with (varA 0) prog)

useC :: Int
useC = run (with (varC 0) prog)
