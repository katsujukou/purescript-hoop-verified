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

-- 非決定計算（継続を2回呼ぶ） -------------------------------------------------

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

    it "pure と bind" do
      let
        prog = do
          x <- pure 1
          y <- pure 2
          pure (x + y)
      run prog `shouldEqual` 3

    it "perform がハンドラに届く" do
      run (reader 42 (map (_ + 1) ask)) `shouldEqual` 43

    it "deep handler: 再開後も2回目の perform が届く" do
      let
        prog = do
          a <- ask
          b <- ask
          pure (a + b)
      run (reader 7 prog) `shouldEqual` 14

    it "戻り節が最後に適用される" do
      run (handleWith (\v -> pure (v * 10))
             [ entry "Reader" "ask" (clause \_ k -> k (toPayload 1)) ]
             ask) `shouldEqual` 10

    it "k の戻り値は戻り節を通った後の値" do
      run (handleWith (\v -> pure (v * 10))
             [ entry "Reader" "ask"
                 (clause \_ k -> map (_ + 100) (k (toPayload 1)))
             ]
             ask) `shouldEqual` 110

    it "継続を捨てる節: 後続は走らない" do
      let
        prog = do
          _ <- throw "boom"
          pure "unreachable"
      run (catchAll ("caught: " <> _) prog) `shouldEqual` "caught: boom"

    it "multi-shot: 継続を2回再開できる" do
      run (allChoices (map (if _ then 1 else 2) choice)) `shouldEqual` [ 1, 2 ]

    it "内側のハンドラが外側を隠す" do
      run (reader 1 (reader 2 ask)) `shouldEqual` 2

    it "内側が扱わない作用は外側へ抜ける" do
      run (reader 1 (catchAll (\_ -> 0) ask)) `shouldEqual` 1

    it "payload は型を保って往復する" do
      run (handle
             [ entry "Echo" "say" (clause \p k -> k (toPayload (arg 0 "" p))) ]
             (perform "Echo" "say" [ toPayload "hello" ]))
        `shouldEqual` "hello"
