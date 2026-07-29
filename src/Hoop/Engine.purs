-- | src/Hoop/Engine.js is generated (runtime/Hoop.Runtime.fst -> OCaml -> jsoo).
-- | Regenerate it with `hoop-build-runtime`. The handwritten boundary code lives
-- | in runtime/ml/hoop_ffi.ml.
-- |
-- | This is Phase 1, so only Pure / Bind / Perform / Handle / run are exposed.
-- | Evidence passing, the tail-resumptive fast path, prompt-local cells and
-- | scoped effects are not in the runtime yet.
module Hoop.Engine
  ( Hoop
  , Payload
  , Resume
  , Clause
  , HandlerEntry
  , toPayload
  , fromPayload
  , perform
  , clause
  , entry
  , handle
  , handleWith
  , run
  ) where

import Prelude

import Data.Function.Uncurried (Fn2, Fn3, mkFn2, runFn2, runFn3)
import Data.Nullable (Nullable, notNull, null)
import Unsafe.Coerce (unsafeCoerce)

-- | An effectful computation, corresponding to `comp_tree` in
-- | runtime/Hoop.Runtime.fst.
-- |
-- | Note that the type argument `a` is phantom: the runtime never inspects the
-- | type of a value, which is exactly what the F* side asserts by keeping
-- | `comp_tree` parametric in its value type. `a` carries meaning only inside
-- | PureScript's type checker.
foreign import data Hoop :: Type -> Type

-- | A value carried by the runtime, of a type the runtime does not know.
-- | Opaque from the PureScript side.
foreign import data Payload :: Type

-- | A delimited continuation. Invoking it from a clause reinstates the captured
-- | stack segment -- the handler included, since the semantics are deep.
type Resume b = Payload -> Hoop b

-- | A handler clause. The runtime invokes it as `(payload, k) => comp`.
type Clause b = Fn2 (Array Payload) (Resume b) (Hoop b)

-- | One entry of a handler table. Represented at runtime as the three-element
-- | JavaScript array `[eff, op, clause]`.
foreign import data HandlerEntry :: Type -> Type

-- Functions from the generated Engine.js. All of them are uncurried.
foreign import pureImpl :: forall a. a -> Hoop a
foreign import bindImpl :: forall a b. Fn2 (Hoop a) (a -> Hoop b) (Hoop b)
foreign import performImpl :: forall a. Fn3 String String (Array Payload) (Hoop a)
foreign import handleImpl
  :: forall a b
   . Fn3 (Nullable (Payload -> Hoop b)) (Array (HandlerEntry b)) (Hoop a) (Hoop b)
foreign import runImpl :: forall a. Hoop a -> a

instance Functor Hoop where
  map f m = runFn2 bindImpl m (\a -> pureImpl (f a))

instance Apply Hoop where
  apply mf ma = runFn2 bindImpl mf (\f -> runFn2 bindImpl ma (\a -> pureImpl (f a)))

instance Applicative Hoop where
  pure = pureImpl

instance Bind Hoop where
  bind m k = runFn2 bindImpl m k

instance Monad Hoop

-- | Wrap a value as a payload. The runtime never looks inside, so it is the
-- | caller's responsibility to read it back at the same type.
toPayload :: forall a. a -> Payload
toPayload = unsafeCoerce

fromPayload :: forall a. Payload -> a
fromPayload = unsafeCoerce

-- | Fire an operation.
perform :: forall a. String -> String -> Array Payload -> Hoop a
perform eff op payload = runFn3 performImpl eff op payload

-- | Build a handler clause.
clause :: forall b. (Array Payload -> Resume b -> Hoop b) -> Clause b
clause = mkFn2

-- | Build one entry of a handler table. Becomes the JavaScript array
-- | `[eff, op, clause]`.
entry :: forall b. String -> String -> Clause b -> HandlerEntry b
entry eff op c = unsafeCoerce [ unsafeCoerce eff, unsafeCoerce op, unsafeCoerce c ]

-- | Install a handler with no return clause, so the return clause is the identity.
handle :: forall a. Array (HandlerEntry a) -> Hoop a -> Hoop a
handle hs m = runFn3 handleImpl null hs m

-- | Install a handler with a return clause. `ret` is applied to the value the
-- | handled computation reaches on its own. It does not run when a clause
-- | discards the continuation instead.
handleWith
  :: forall a b. (a -> Hoop b) -> Array (HandlerEntry b) -> Hoop a -> Hoop b
handleWith ret hs m =
  runFn3 handleImpl (notNull (\p -> ret (fromPayload p))) hs m

-- | Drive the machine to completion. The Phase 1 runtime is synchronous and
-- | free of side effects. An unhandled operation raises a JavaScript Error.
run :: forall a. Hoop a -> a
run = runImpl
