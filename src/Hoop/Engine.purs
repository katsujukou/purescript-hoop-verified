-- | src/Hoop/Engine.js は生成物（runtime-fst/Hoop.Runtime.fst → OCaml → jsoo）。
-- | 再生成は `hoop-build-runtime`。境界の手書きコードは runtime-ml/hoop_ffi.ml。
-- |
-- | Phase 1 のため、公開しているのは Pure / Bind / Perform / Handle / run だけ。
-- | evidence-passing、tail-resumptive fast path、prompt-local cell、scoped effect
-- | はまだランタイムに無い。
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

-- | エフェクト付き計算。runtime-fst/Hoop.Runtime.fst の `comp` に対応する。
-- |
-- | 型引数 `a` はファントムであることに注意。ランタイムは値の型を一度も見ない
-- | （F* 側で `comp` が値型にパラメトリックなのがその主張）。`a` が意味を持つのは
-- | PureScript の型検査の中だけ。
foreign import data Hoop :: Type -> Type

-- | ランタイムが運ぶ、型の分からない値。PS 側からは不透明。
foreign import data Payload :: Type

-- | 限定継続。clause がこれを呼ぶと、捕捉されたスタック片が再設置される
-- | （deep handler なのでハンドラごと戻る）。
type Resume b = Payload -> Hoop b

-- | ハンドラの節。ランタイムは `(payload, k) => comp` として呼ぶ。
type Clause b = Fn2 (Array Payload) (Resume b) (Hoop b)

-- | ハンドラ表の1エントリ。実行時表現は `[eff, op, clause]` の3要素 JS 配列。
foreign import data HandlerEntry :: Type -> Type

-- 生成された Engine.js の関数。すべて非カリー化。
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

-- | 値を payload に入れる。ランタイムは中身を見ないので、取り出すときに
-- | 同じ型を指定する責任は呼び出し側にある。
toPayload :: forall a. a -> Payload
toPayload = unsafeCoerce

fromPayload :: forall a. Payload -> a
fromPayload = unsafeCoerce

-- | 作用を発火する。
perform :: forall a. String -> String -> Array Payload -> Hoop a
perform eff op payload = runFn3 performImpl eff op payload

-- | ハンドラの節を作る。
clause :: forall b. (Array Payload -> Resume b -> Hoop b) -> Clause b
clause = mkFn2

-- | ハンドラ表の1エントリを作る。`[eff, op, clause]` の JS 配列になる。
entry :: forall b. String -> String -> Clause b -> HandlerEntry b
entry eff op c = unsafeCoerce [ unsafeCoerce eff, unsafeCoerce op, unsafeCoerce c ]

-- | 戻り節なしでハンドラを設置する（戻り節は恒等）。
handle :: forall a. Array (HandlerEntry a) -> Hoop a -> Hoop a
handle hs m = runFn3 handleImpl null hs m

-- | 戻り節つきでハンドラを設置する。`ret` は被ハンドル計算が最後まで到達した
-- | 値に適用される。継続を捨てる節を通った場合は走らない。
handleWith
  :: forall a b. (a -> Hoop b) -> Array (HandlerEntry b) -> Hoop a -> Hoop b
handleWith ret hs m =
  runFn3 handleImpl (notNull (\p -> ret (fromPayload p))) hs m

-- | マシンを最後まで回す。Phase 1 のランタイムは同期的で、副作用を持たない。
-- | 未処理の作用があると JS の Error が投げられる。
run :: forall a. Hoop a -> a
run = runImpl
