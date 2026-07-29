module Test.Hoop where

import Prelude

import Data.Array (index)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Hoop.Engine (Hoop, Payload, clause, entry, fromPayload, handle, handleWith, perform, run, toPayload)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

arg :: forall a. Int -> a -> Array Payload -> a
arg i def p = case index p i of
  Just x -> fromPayload x
  Nothing -> def

-- Reader ---------------------------------------------------------------------

ask :: Hoop Int
ask = perform "Reader" "ask" []

reader :: forall a. Int -> Hoop a -> Hoop a
reader n = handle [ entry "Reader" "ask" (clause \_ k -> k (toPayload n)) ]

-- Exception ------------------------------------------------------------------

throw :: forall a. String -> Hoop a
throw msg = perform "Exc" "throw" [ toPayload msg ]

catchAll :: forall a. (String -> a) -> Hoop a -> Hoop a
catchAll f = handle [ entry "Exc" "throw" (clause \p _ -> pure (f (arg 0 "?" p))) ]

-- Nondeterminism (the clause resumes twice) ------------------------------

choice :: Hoop Boolean
choice = perform "Amb" "choice" []

allChoices :: forall a. Hoop a -> Hoop (Array a)
allChoices = handleWith (\a -> pure [ a ])
  [ entry "Amb" "choice"
      ( clause \_ k -> do
          xs <- k (toPayload true)
          ys <- k (toPayload false)
          pure (xs <> ys)
      )
  ]

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Hoop.Engine" do

    it "pure and bind" do
      let
        prog = do
          x <- pure 1
          y <- pure 2
          pure (x + y)
      run prog `shouldEqual` 3

    it "perform reaches its handler" do
      run (reader 42 (map (_ + 1) ask)) `shouldEqual` 43

    it "deep handler: a second perform still reaches the handler after resuming" do
      let
        prog = do
          a <- ask
          b <- ask
          pure (a + b)
      run (reader 7 prog) `shouldEqual` 14

    it "the return clause is applied at the end" do
      run (handleWith (\v -> pure (v * 10))
             [ entry "Reader" "ask" (clause \_ k -> k (toPayload 1)) ]
             ask) `shouldEqual` 10

    it "the value k returns has already passed through the return clause" do
      run (handleWith (\v -> pure (v * 10))
             [ entry "Reader" "ask"
                 (clause \_ k -> map (_ + 100) (k (toPayload 1)))
             ]
             ask) `shouldEqual` 110

    it "a clause that discards the continuation skips the rest" do
      let
        prog = do
          _ <- throw "boom"
          pure "unreachable"
      run (catchAll ("caught: " <> _) prog) `shouldEqual` "caught: boom"

    it "multi-shot: the continuation can be resumed twice" do
      run (allChoices (map (if _ then 1 else 2) choice)) `shouldEqual` [ 1, 2 ]

    it "an inner handler shadows an outer one" do
      run (reader 1 (reader 2 ask)) `shouldEqual` 2

    it "an operation the inner handler does not cover escapes outward" do
      run (reader 1 (catchAll (\_ -> 0) ask)) `shouldEqual` 1

    it "a payload survives the round trip at its original type" do
      run (handle
             [ entry "Echo" "say" (clause \p k -> k (toPayload (arg 0 "" p))) ]
             (perform "Echo" "say" [ toPayload "hello" ]))
        `shouldEqual` "hello"
