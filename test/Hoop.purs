module Test.Hoop where

import Prelude

import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Hoop.Engine (Handler, Hoop, assign, continue, handler, perform, read, run, var, with, write, (:=))
import Hoop.Reader (READER, ask)
import Hoop.State (STATE, get, handleState, set)
import Hoop.Types (class EffNewtype, type (->*), EffType, fast, full, scalar)
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

-- State by parameter passing ------------------------------------------------
--
-- The other way to write a state handler: no cells, `full` clauses, and the
-- state threaded through the answer type. Not a fallback for
-- `Hoop.State.handleState` but the other of two tools, each with the thing
-- the other cannot do:
--
--   handleState  cells, `fast`, no capture     answer `a`
--   statePP      parameter passing, `full`     answer `s -> Hoop r (a /\ s)`
--
-- Cells are the `ST` reading -- a binder with a lifetime, no state in the
-- answer (see `var`). This is the state *monad* reading, so the final state
-- comes out, and every `get` and `set` captures the continuation to get it.
--
-- The answer cannot be `s -> a /\ s`. `continue k s` is a *computation* in
-- `Hoop r`, and a clause has no way out of it, so the state-passing function
-- has to land in `Hoop r` too. That is the whole difference from the
-- textbook presentation, and it is forced by the runtime, not by the API.
statePP :: forall s r a. Handler (STATE s ()) r a (s -> Hoop r (a /\ s))
statePP = handler (Proxy :: _ (STATE s ()))
  { state:
      { get: full \_ k -> pure \s -> continue k s >>= \f -> f s
      , set: full \s' k -> pure \_ -> continue k unit >>= \f -> f s'
      }
  , pure: \v -> \s -> pure (v /\ s)
  }

runState :: forall s a. s -> Hoop (STATE s ()) a -> a /\ s
runState s0 prog = run (run (with statePP prog) s0)

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

    -- Prompt-local cells ---------------------------------------------------

    it "a cell backs a state handler" do
      let
        h = var { count: 0 } \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read @"count" c
                , set: fast \n -> assign @"count" c n
                }
            }
        prog = do
          a <- get
          _ <- set (a + 5)
          b <- get
          pure (a + b)
      run (with h prog) `shouldEqual` 5

    it "one region may declare several cells" do
      let
        h = var { count: 0, label: "-" } \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read @"count" c
                , set: fast \n -> do
                    _ <- write @"label" c "set"
                    assign @"count" c n
                }
            }
        prog = do
          _ <- set 3
          get
      run (with h prog) `shouldEqual` 3

    -- A bare initial value declares one unnamed cell, so `read` and
    -- `write` need no label -- and `write` without a label is an ordinary
    -- binary function, hence `:=`.
    it "a bare initial value needs no field name" do
      let
        h = var 0 \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read c
                , set: fast \n -> c := n
                }
            }
        prog = do
          _ <- set 7
          n <- get
          pure (n * 3)
      run (with h prog) `shouldEqual` 21

    it "a record of one field may drop the label too" do
      let
        h = var { count: 0 } \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read c
                , set: fast \n -> c := n
                }
            }
      run (with h (set 4 *> get)) `shouldEqual` 4

    it "`scalar` keeps a record whole as a single cell" do
      let
        h = var (scalar { x: 1, y: 2 }) \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> map (\p -> p.x + p.y) (read c)
                , set: fast \n -> c := { x: n, y: n }
                }
            }
        prog = do
          a <- get
          _ <- set 10
          b <- get
          pure (a + b)
      run (with h prog) `shouldEqual` 23

    -- Labels are static: they come from the field names, and a bare `var`
    -- uses one reserved label for every region it opens. So two regions in
    -- one stack routinely carry the *same* label, and the machine's rule is
    -- innermost-wins -- a collision would be a wrong answer, not a crash.
    --
    -- It is not a collision, and the reason is structural: `var` installs
    -- the cells immediately below their own handler's prompt, and `step`
    -- runs a clause on the stack *below* that prompt. So the first frame of
    -- the right label under a clause is always its own handler's, whatever
    -- else is stacked above. These two tests pin that down.
    it "two regions sharing a label each see their own cell" do
      let
        stateH = var 0 \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read c
                , set: fast \n -> c := n
                }
            }
        readerH = var 99 \c ->
          handler (Proxy :: _ (READER Int ()))
            { reader: fast \_ -> read c }

        prog :: Hoop (READER Int (STATE Int ())) Int
        prog = do
          _ <- set 5
          r <- ask
          s <- get
          pure (r * 100 + s)
      run (with stateH (with readerH prog)) `shouldEqual` 9905

    it "the same handler nested in itself does not shadow its own cell" do
      let
        -- The same construction twice, so the same static label twice.
        outerH = var 0 \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read c
                , set: fast \n -> c := n
                }
            }
        innerH = var 0 \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read c
                , set: fast \n -> c := n
                }
            }

        prog :: Hoop (STATE Int ()) Int
        prog = do
          _ <- set 1
          inner <- with innerH (set 2 *> get)
          outer <- get
          pure (inner * 10 + outer)
      run (with outerH prog) `shouldEqual` 21

    -- `Hoop.State.handleState` is cell-backed and polymorphic in the state
    -- type, which is what a library exports. Exercised at two types to pin
    -- that the polymorphism is real and not an artefact of one call site.
    it "an exported handler may be polymorphic in its cell's type" do
      let
        prog = do
          a <- get
          _ <- set (a * 2)
          get
      run (with (handleState 6) prog) `shouldEqual` 12
      run (with (handleState "a") (set "b" *> get)) `shouldEqual` "b"

    it "state by parameter passing agrees with the cell-backed handler" do
      let
        prog :: forall r. Hoop (STATE Int r) Int
        prog = do
          a <- get
          _ <- set (a + 5)
          b <- get
          _ <- set (b * 2)
          pure (a + b)
      runState 0 prog `shouldEqual` (5 /\ 10)
      run (with (handleState 0) prog) `shouldEqual` 5

    -- The sharpest test in the file. A cell lives in a stack frame, by
    -- value, so the segment `flip` captures carries its own copy: the two
    -- resumptions see the writes each of them made and nothing more. A
    -- runtime holding the cell behind a shared mutable box would agree with
    -- every other test here and report [ 10, 10 ].
    it "a captured continuation carries its own copy of a cell" do
      let
        stateH = var { count: 0 } \c ->
          handler (Proxy :: _ (STATE Int ()))
            { state:
                { get: fast \_ -> read @"count" c
                , set: fast \n -> assign @"count" c n
                }
            }
        ambH = handler (Proxy :: _ (AMB ()))
          { amb: \_ k -> do
              xs <- continue k true
              ys <- continue k false
              pure (xs <> ys)
          , pure: \v -> [ v ]
          }

        prog :: Hoop (STATE Int (AMB ())) Int
        prog = do
          b <- flip
          _ <- if b then set 10 else pure unit
          get
      run (prog # with stateH # with ambH) `shouldEqual` [ 10, 0 ]
