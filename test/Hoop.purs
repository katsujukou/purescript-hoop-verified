module Test.Hoop where

import Prelude

import Effect (Effect)
import Hoop.Engine (Hoop, continue, handler, perform, run, with)
import Hoop.Reader (READER, ask)
import Hoop.State (STATE, get, set)
import Hoop.Types (class EffNewtype, type (->*), EffType)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

-- Exception ------------------------------------------------------------------

foreign import data Exc :: EffType

type Exc' = (throw :: String ->* Unit)

instance EffNewtype Exc Exc'

type EXC r = (exc :: Exc | r)

throw :: forall r. String -> Hoop (EXC r) Unit
throw = perform @(EXC ()) @"throw"

-- Nondeterminism -------------------------------------------------------------

foreign import data Amb :: EffType

type Amb' = (flip :: Unit ->* Boolean)

instance EffNewtype Amb Amb'

type AMB r = (amb :: Amb | r)

flip :: forall r. Hoop (AMB r) Boolean
flip = perform @(AMB ()) @"flip" unit

--------------------------------------------------------------------------------

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Hoop" do

    it "pure and bind" do
      let
        prog = do
          x <- pure 1
          y <- pure 2
          pure (x + y)
      run prog `shouldEqual` 3

    it "perform reaches its handler" do
      let
        h = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 42 }
      run (with h (map (_ + 1) ask)) `shouldEqual` 43

    it "deep handler: a second perform still reaches the handler after resuming" do
      let
        h = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 7 }
        prog = do
          a <- ask
          b <- ask
          pure (a + b)
      run (with h prog) `shouldEqual` 14

    it "the return clause is applied at the end" do
      let
        h = handler (Proxy :: _ (READER Int ()))
              { reader: \_ k -> continue k 1
              , pure: \v -> v * 10
              }
      run (with h ask) `shouldEqual` 10

    it "the value continue returns has already passed through the return clause" do
      let
        h = handler (Proxy :: _ (READER Int ()))
              { reader: \_ k -> map (_ + 100) (continue k 1)
              , pure: \v -> v * 10
              }
      run (with h ask) `shouldEqual` 110

    it "a clause that discards the continuation skips the rest" do
      let
        h = handler (Proxy :: _ (EXC ()))
              { exc: \msg _ -> pure ("caught: " <> msg)
              , pure: \_ -> "unreachable"
              }
        prog = do
          _ <- throw "boom"
          pure unit
      run (with h prog) `shouldEqual` "caught: boom"

    it "multi-shot: the continuation can be resumed twice" do
      let
        h = handler (Proxy :: _ (AMB ()))
              { amb: \_ k -> do
                  xs <- continue k true
                  ys <- continue k false
                  pure (xs <> ys)
              , pure: \v -> [ v ]
              }
      run (with h (map (if _ then 1 else 2) flip)) `shouldEqual` [ 1, 2 ]

    it "an operation the inner handler does not cover escapes outward" do
      let
        readerH = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 5 }
        excH = handler (Proxy :: _ (EXC ())) { exc: \_ _ -> pure 0 }
        prog :: Hoop (EXC (READER Int ())) Int
        prog = ask
      run (with readerH (with excH prog)) `shouldEqual` 5

    it "a handler with several operations dispatches on the operation name" do
      let
        h = handler (Proxy :: _ (STATE Int ()))
              { state:
                  { get: \_ k -> continue k 5
                  , set: \_ k -> continue k unit
                  }
              }
        prog = do
          _ <- set 99
          n <- get
          pure (n * 2)
      run (with h prog) `shouldEqual` 10

    it "a payload survives the round trip at its original type" do
      let
        h = handler (Proxy :: _ (READER String ())) { reader: \_ k -> continue k "hello" }
      run (with h ask) `shouldEqual` "hello"

    it "an inner handler shadows an outer one" do
      let
        outer = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 1 }
        inner = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 2 }
        prog :: Hoop (READER Int (READER Int ())) Int
        prog = ask
      run (with outer (with inner prog)) `shouldEqual` 2

    -- A clause runs *outside* its own prompt: the machine cuts the captured
    -- segment at that prompt, so an operation performed by the clause body
    -- resolves against the handlers below it. Here the inner clause's own
    -- `ask` therefore reaches `outer`, never itself.
    it "a clause's own perform resolves outside its own prompt" do
      let
        outer = handler (Proxy :: _ (READER Int ())) { reader: \_ k -> continue k 1 }
        inner = handler (Proxy :: _ (READER Int ()))
          { reader: \_ k -> do
              n <- ask
              continue k (n * 10)
          }
        prog :: Hoop (READER Int (READER Int ())) Int
        prog = ask
      run (with outer (with inner prog)) `shouldEqual` 10
