module Benchmarks.Common.Args where

import Prelude

import Data.Array (last)
import Data.Int as Int
import Data.Maybe (fromMaybe)
import Effect (Effect)
import Node.Process (argv)

-- | The benchmark input size: the last argv entry when it parses as an
-- | Int (robust to both `node script.mjs N` and `spago run -- N`), else
-- | a small smoke default.
sizeArg :: Effect Int
sizeArg = do
  as <- argv
  pure (fromMaybe 1000 (last as >>= Int.fromString))