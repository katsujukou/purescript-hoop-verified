-- | Scoped (higher-order) operations, end to end: the surface builds the
-- | clause, the F* machine borrows the prompts, and the scope runs under them.
-- |
-- | The compile-time half of the same slice -- that an ordinary `handler`
-- | refuses a scoped clause, and that a monomorphic table cannot pose as a
-- | family -- cannot live here, because a fixture that must NOT compile has no
-- | place in a module that must. It is in `test-compile-fail/`, run by
-- | `scripts/compile-fail.sh`.
module Test.Scoped where

import Prelude

import Data.Either (Either(..))
import Data.String as String
import Data.Void (Void, absurd)
import Hoop.Engine (HHandler, Handler, HandlerF, Hoop, handler, handlerScoped, perform, performScoped, read, run, scoped, var, with, withF, write)
import Hoop.Types (class EffNewtype, type (->*), AllowScoped, EffType, HSig, Scoped, fast, full)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- Exceptions with a scoped `catch` -------------------------------------------

foreign import data Exc :: EffType

-- | The operation's payload. Both computations live inside it, and the runtime
-- | never looks: it is one opaque payload element, which is what saves the
-- | machine from owing an `HFunctor` obligation on this type.
newtype Catch :: HSig
newtype Catch m a = Catch { try :: m a, recover :: String -> m a }

type Exc' = (throw :: String ->* Void, catch :: Scoped Catch)

instance EffNewtype Exc Exc'

type EXC r = (exc :: Exc | r)
type EXC1 = EXC ()

throwE :: forall r a. String -> Hoop (EXC r) a
throwE msg = absurd <$> perform @EXC1 @"throw" msg

catchE :: forall r a. Hoop (EXC r) a -> (String -> Hoop (EXC r) a) -> Hoop (EXC r) a
catchE try recover = performScoped @EXC1 @"catch" (Catch { try, recover })

-- | The clause always weaves: `runScope` is on the success path, not only on
-- | the recovery. A clause that discarded its scope would exercise the
-- | dispatch of `PerformS` and never the `Weave` transition.
runExc :: forall r b. HHandler AllowScoped EXC1 r b (Either String b)
runExc = handler (Proxy :: _ EXC1)
  { exc:
      { throw: full \msg _k -> pure (Left msg)
      , catch: scoped \(Catch rec) t k ->
          t.runScope rec.try >>= case _ of
            Right cx -> t.resumeScope cx k
            -- Non-recapture: the recovery runs in the scope, and if it throws,
            -- the clause reports that failure rather than catching it again.
            Left e -> t.runScope (rec.recover e) >>= case _ of
              Right cx -> t.resumeScope cx k
              Left e' -> pure (Left e')
      }
  , pure: Right
  }

runExcF :: forall r. HandlerF EXC1 r (Either String)
runExcF = handlerScoped runExc

-- Two cell-backed handlers, one on each side of the scoped one ---------------

foreign import data St :: EffType
type St' = (get :: Unit ->* Int, set :: Int ->* Int)

instance EffNewtype St St'
type ST r = (st :: St | r)
type ST1 = ST ()

foreign import data Ctr :: EffType
type Ctr' = (look :: Unit ->* Int, bump :: Int ->* Int)

instance EffNewtype Ctr Ctr'
type CTR r = (ctr :: Ctr | r)
type CTR1 = CTR ()

getS :: forall r. Hoop (ST r) Int
getS = perform @ST1 @"get" unit

setS :: forall r. Int -> Hoop (ST r) Int
setS = perform @ST1 @"set"

look :: forall r. Hoop (CTR r) Int
look = perform @CTR1 @"look" unit

bump :: forall r. Int -> Hoop (CTR r) Int
bump = perform @CTR1 @"bump"

-- Installed INSIDE the scoped handler, so its prompt and its cell both travel
-- in the borrowed segment. A bare `var` uses the one reserved scalar label,
-- which is what makes this a genuine collision with `ctrH`'s cell.
stateH :: forall r a. Handler ST1 r a a
stateH = var 200 \c ->
  handler (Proxy :: _ ST1)
    { st: { get: fast \_ -> read c, set: fast \n -> write c n } }

-- Installed OUTSIDE it, so its cell is reached through the real stack and is
-- never copied. Same reserved label.
ctrH :: forall r a. Handler CTR1 r a a
ctrH = var 7 \c ->
  handler (Proxy :: _ CTR1)
    { ctr: { look: fast \_ -> read c, bump: fast \n -> write c n } }

cellProg :: forall r. Hoop (ST + EXC + CTR + r) (Array Int)
cellProg = do
  inScope <- catchE
    ( do
        a <- getS -- the intermediate's cell, not the outer's
        _ <- setS 999 -- writes the BORROWED copy
        b <- getS
        _ <- bump 42 -- writes the outer cell, which is live
        pure [ a, b ]
    )
    (\_ -> pure [ -1, -1 ])
  after <- getS -- 200 if the borrowed cell was a snapshot
  seen <- look -- 42 if the outer cell is live
  pure (inScope <> [ after, seen ])

spec :: Spec Unit
spec = describe "scoped operations" do
  it "a scope that succeeds is resumed with its value" do
    run (withF runExcF (catchE (pure 7) (\_ -> pure 0)))
      `shouldEqual` Right 7

  it "a scope that throws is recovered, and the recovery is woven" do
    run (withF runExcF (catchE (throwE "boom") (\e -> pure (String.length e))))
      `shouldEqual` Right 4

  it "a recovery that throws is not recaptured" do
    run (withF runExcF (catchE (throwE "a") (\_ -> throwE "b") :: Hoop EXC1 Int))
      `shouldEqual` Left "b"

  it "the continuation after a scope receives the scope's value" do
    run
      ( withF runExcF
          ((+) <$> catchE (throwE "xy") (\e -> pure (String.length e)) <*> pure 100)
      ) `shouldEqual` Right 102

  -- The placement invariant recorded on `var`, re-derived across a borrow.
  -- `prepare_scope` keeps every `ParamF` with its label AND its value and never
  -- reorders, so the scope still meets the nearest cell first; and because the
  -- frame holds the value rather than a pointer, what it meets is a snapshot.
  -- A cell outside the scoped handler is not in the borrowed segment at all,
  -- so it stays live. Both halves are observed, by reading and by writing.
  it "a borrowed cell is a snapshot; a cell outside the scope stays live" do
    run (with ctrH (withF runExcF (with stateH cellProg)))
      `shouldEqual` Right [ 200, 999, 200, 42 ]
