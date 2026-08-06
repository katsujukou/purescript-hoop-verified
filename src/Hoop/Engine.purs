-- @inline export performImpl'(..).perform always
-- @inline export performListImpl(..).performList always
-- @inline export performEffectImpl1(..).performEffect always

-- @inline export handler always
-- @inline export with always
-- @inline export run always
-- @inline export continue always

-- @inline export buildHandlerReturnClause(..).buildHandler always
-- @inline export buildHandlerIdentity(..).buildHandler always
-- @inline export mkHandlersImpl(..).mkHandlers always
-- @inline export mkHandlersListNil(..).mkHandlersList always
-- @inline export mkHandlersListCons(..).mkHandlersList always
-- @inline export mkHandlerClausesNil(..).mkHandlerClauses always
-- @inline export mkHandlerClausesCons(..).mkHandlerClauses always
-- @inline export clauseForFull(..).toRuntimeClause always
-- @inline export clauseForFast(..).toRuntimeClause always
-- @inline export clauseForDefault(..).toRuntimeClause always
-- @inline export canonicalizeHandlersImpl(..).canonicalizeHandlers always
-- @inline export canonicalizeHandlersListNil(..).canonicalizeHandlersList always
-- @inline export canonicalizeHandlersListCons(..).canonicalizeHandlersList always
-- @inline export canonicalizeClausePass(..).canonicalizeClause always
-- @inline export canonicalizeClauseWrap(..).canonicalizeClause always

-- @inline export performScopedImpl'(..).performScoped always
-- @inline export performScopedListImpl(..).performScopedList always
-- @inline export performScopedEffectImpl(..).performScopedEffect always
-- @inline export performScopedImpl always
-- @inline export clauseForScoped(..).toRuntimeClause always
-- @inline export scoped always
-- @inline export handlerScoped always
-- @inline export withF always

-- @inline export handlerParam always
-- @inline export buildParamHandlerReturnClause(..).buildParamHandler always
-- @inline export buildParamHandlerIdentity(..).buildParamHandler always
-- @inline export mkParamHandlersImpl(..).mkParamHandlers always
-- @inline export mkParamHandlersListNil(..).mkParamHandlersList always
-- @inline export mkParamHandlersListCons(..).mkParamHandlersList always
-- @inline export mkParamHandlerClausesNil(..).mkParamHandlerClauses always
-- @inline export mkParamHandlerClausesCons(..).mkParamHandlerClauses always
module Hoop.Engine
  ( Cont
  , Handler
  , Hoop
  , RuntimeClause
  , RuntimeClauses
  , RuntimeHandlers
  , RuntimeReturn
  , buildHandler
  , canonicalizeHandlers
  , canonicalizeHandlersList
  , canonicalizeClause
  , class BuildHandler
  , class CanonicalizeClauseList
  , class CanonicalizeHandlers
  , class CanonicalizeHandlersList
  , class ClauseFor
  , class ComputationSignature
  , class FastSignature
  , class FullSignature
  , class MkHandlerClauses
  , class MkHandlers
  , class MkHandlersList
  , class Perform
  , class PerformEffect
  , class PerformList
  , class UnexpectedFieldsGuard
  , continue
  , handler
  , mkHandlers
  , mkHandlerClauses
  , mkHandlersList
  , perform
  , performEffect
  , performList
  , run
  , toRuntimeClause
  , with
  )
  where

import Prelude

import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4, runFn2, runFn3)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Hoop.TypeUtil (class HasLabel, class RowListLength, class TypeEquals, proof, type (++), type (:), type (|>), List, Nil)
import Hoop.Types (class EffNewtype, class MkAction, type (->*), AnyPayload, Clause, EffType, Fast, Full, evKey, mkAction, unClause)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Boolean (False, True)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Prim.TypeError (class Fail, QuoteLabel, Text)
import Record as Record
import Record.Unsafe as RU
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

foreign import data Hoop :: Row EffType -> Type -> Type

foreign import pureImpl :: forall r a. Fn1 a (Hoop r a)

foreign import bindImpl :: forall r a b. Fn2 (Hoop r a) (a -> Hoop r b) (Hoop r b)

instance functorHoop :: Functor (Hoop r) where
  map f m = runFn2 bindImpl m \a -> pureImpl (f a)

instance applyHoop :: Apply (Hoop r) where
  apply mf ma =
    runFn2 bindImpl mf \f ->
      runFn2 bindImpl ma \a ->
        pureImpl (f a)

instance applicativeHoop :: Applicative (Hoop r) where
  pure = pureImpl

instance bindHoop :: Bind (Hoop r) where
  bind = runFn2 bindImpl

instance monadHoop :: Monad (Hoop r)

foreign import performImpl
  :: forall r a
   . Fn4
       String -- eff 
       String -- op
       String -- evkey
       (Array AnyPayload)
       (Hoop r a)

{------------ Typed `perform` API ------------}

class Perform :: Row EffType -> Symbol -> Type -> Constraint
class Perform eff op comptyp | eff op -> comptyp where
  perform :: comptyp

instance performImpl1 ::
  ( RowToList eff effL
  , PerformList effL op comptyp
  ) =>
  Perform eff op comptyp
  where
  perform = performList @effL @op

class PerformList :: RowList EffType -> Symbol -> Type -> Constraint
class PerformList effL op comptyp | effL op -> comptyp where
  performList :: comptyp

instance performListImpl ::
  ( EffNewtype efftyp repr
  , PerformEffect efflbl efftyp repr op comptyp
  ) =>
  PerformList (RL.Cons efflbl efftyp RL.Nil) op comptyp where
  performList = performEffect @efflbl @efftyp @repr @op

else instance
  ( Fail (Text """You must specify effect row with exactly 1 element. e.g.: `perform @(OP ()) @"op"...` where `type OP r = (op :: Op | r)`""")
  ) =>
  PerformList _1 _2 _3 where
  performList = unsafeCrashWith "impossible"

class PerformEffect :: Symbol -> EffType -> Row Type -> Symbol -> Type -> Constraint
class PerformEffect efflbl efftyp repr op comptyp | efflbl efftyp repr op -> comptyp where
  performEffect :: comptyp

instance performEffectImpl1 ::
  ( Row.Cons op comp _1 repr
  , ComputationSignature comp args ret
  , Row.Cons efflbl efftyp _2 eff
  , MkAction args (Hoop eff ret) comptyp
  , IsSymbol efflbl
  , IsSymbol op
  ) =>
  PerformEffect efflbl efftyp repr op comptyp
  where
  performEffect = mkAction @args @(Hoop eff ret) eff op (evKey eff op) performImpl
    where
    eff = reflectSymbol (Proxy :: _ efflbl)
    op = reflectSymbol (Proxy :: _ op)

class ComputationSignature :: Type -> List Type -> Type -> Constraint
class ComputationSignature comp args ret | comp -> args ret

instance ComputationSignature (a ->* b) (a : Nil) b

else instance
  ( ComputationSignature b args ret
  ) =>
  ComputationSignature (a -> b) (a : args) ret

else instance
  ( Fail (Text "The type of operation must be Function (->) or Computation (->*)")
  ) =>
  ComputationSignature _1 _2 _3

{------------ Typed `handler` API ------------}

newtype Handler :: Row EffType -> Row EffType -> Type -> Type -> Type
newtype Handler effh r a o = Handler (forall effa. Hoop effa a -> Hoop r o)

-- | The delimited continuation passed to a full clause. `b` is the
-- | operation's result, `r` the row the handler performs into, `o` the
-- | answer type.
foreign import data Cont :: Type -> Row EffType -> Type -> Type

continue :: forall b r o. Cont b r o -> b -> Hoop r o
continue = unsafeCoerce

run :: forall a. Hoop () a -> a
run = runImpl

-- | Handle the effects `effh`, removing them from the computation's row.
with
  :: forall effh effb effa a o
   . Row.Union effh effb effa
  => Handler effh effb a o
  -> Hoop effa a
  -> Hoop effb o
with (Handler install) comp = install comp

-- | Build a handler from a record of clauses. The record may use the
-- | canonical form `{ eff: { op: clause } }`, or a bare clause
-- | `{ eff: clause }` for a single-operation effect. A clause is marked
-- | `full` (fully controllable: receives the delimited continuation
-- | last, may resume it any number of times including none) or `fast`
-- | (tail-resumptive: the body computes the operation's result, possibly
-- | performing effects of the outer context, and resumes exactly once).
-- | An unmarked clause defaults to `full`.
-- |
-- | The field name `pure` is reserved for the return clause (Koka's
-- | `return` clause; the generator of a fold-style handler): a *pure*
-- | function `a -> o` applied to the handled computation's final value.
-- | It cannot perform effects; the runtime lifts its result into the
-- | machine. When omitted, the handler is the identity on results and
-- | `o ~ a`.
-- |
-- | Each clause is checked against the canonical type computed from the
-- | operation's signature, so mismatches surface as type errors at the
-- | `handler` call site.
handler
  :: forall effh effhL pureEff hs' hsRow hsL hasPure r a o
   . RowToList effh effhL
  => HasLabel effhL "pure" pureEff
  => CanonicalizeHandlers effh hs' (Record hsRow)
  => RowToList hsRow hsL
  => HasLabel hsL "pure" hasPure
  => BuildHandler pureEff hasPure hsRow effh r a o
  => Proxy effh
  -> hs'
  -> Handler effh r a o
handler p hs' = buildHandler @pureEff @hasPure (canonicalizeHandlers p hs' :: Record hsRow)

class CanonicalizeHandlers :: Row EffType -> Type -> Type -> Constraint
class CanonicalizeHandlers effh from to | effh from -> to where
  canonicalizeHandlers :: Proxy effh -> from -> to

instance canonicalizeHandlersImpl ::
  ( RowToList effh effhL
  , CanonicalizeHandlersList effhL from to
  ) =>
  CanonicalizeHandlers effh (Record from) (Record to)
  where
  canonicalizeHandlers _ = canonicalizeHandlersList (Proxy :: _ effhL)

class CanonicalizeHandlersList :: RowList EffType -> Row Type -> Row Type -> Constraint
class CanonicalizeHandlersList effhL from to | effhL from -> to where
  canonicalizeHandlersList :: Proxy effhL -> Record from -> Record to

instance canonicalizeHandlersListNil :: CanonicalizeHandlersList RL.Nil from from where
  canonicalizeHandlersList _ h = h

instance canonicalizeHandlersListCons ::
  ( Row.Cons efflbl fromCls fromRest from
  , CanonicalizeHandlersList tail fromRest toRest
  , EffNewtype efftyp repr
  , RowToList repr reprL
  , RowListLength reprL reprLen
  , CanonicalizeClauseList reprLen reprL fromCls toCls
  , Row.Cons efflbl toCls toRest to
  , IsSymbol efflbl
  ) =>
  CanonicalizeHandlersList (RL.Cons efflbl efftyp tail) from to
  where
  canonicalizeHandlersList _ from =
    RU.unsafeSet
      efflbl
      (canonicalizeClause (Proxy :: _ reprLen) (Proxy :: _ reprL) fromCls)
      fromRest
    where
    efflbl = reflectSymbol (Proxy :: _ efflbl)
    fromRest = canonicalizeHandlersList (Proxy :: _ tail) (coerceFrom from)

    coerceFrom :: Record from -> Record fromRest
    coerceFrom = unsafeCoerce
    fromCls = Record.get (Proxy :: _ efflbl) from

class CanonicalizeClauseList :: Int -> RowList Type -> Type -> Type -> Constraint
class CanonicalizeClauseList n reprL fromCls toCls | n reprL fromCls -> toCls where
  canonicalizeClause :: Proxy n -> Proxy reprL -> fromCls -> toCls

-- Already in canonical (record-of-clauses) form.
instance canonicalizeClausePass :: CanonicalizeClauseList n reprL (Record cls) (Record cls) where
  canonicalizeClause _ _ = identity

-- A bare clause for a single-operation effect gets wrapped.
else instance canonicalizeClauseWrap ::
  ( Row.Cons op f () toCls
  , IsSymbol op
  ) =>
  CanonicalizeClauseList 1 (RL.Cons op _1 _2) f (Record toCls) where
  canonicalizeClause _ _ f = Record.insert (Proxy :: _ op) f {}

else instance
  ( Fail (Text "A handler for a multi-operation effect must be a record of clauses.")
  ) =>
  CanonicalizeClauseList _1 _2 _3 _4 where
  canonicalizeClause _ _ _ = unsafeCrashWith "impossible"

class BuildHandler :: Boolean -> Boolean -> Row Type -> Row EffType -> Row EffType -> Type -> Type -> Constraint
class BuildHandler pureEff has hs effh r a o where
  buildHandler :: Record hs -> Handler effh r a o

instance buildHandlerPureEffLabel ::
  ( Fail (Text "The effect label `pure` is reserved for the return clause.")
  ) =>
  BuildHandler True has hs effh r a o where
  buildHandler _ = unsafeCrashWith "impossible"

else instance buildHandlerReturnClause ::
  ( Row.Cons "pure" (a -> o) rest hs
  , MkHandlers effh (Record rest) r o
  ) =>
  BuildHandler False True hs effh r a o where
  -- unsafeGet's result type is pinned by mkReturnImpl; the Row.Cons
  -- constraint ties it to the actual field. The `pure` key survives in
  -- the coerced record at runtime, but harmlessly: the handler table is
  -- rebuilt from empty and only effect labels are read. The lets keep
  -- the table construction out of the installer closure, so a reused
  -- handler value builds it once.
  buildHandler hs =
    let
      ret = mkReturnImpl (RU.unsafeGet "pure" hs) :: RuntimeReturn r a o
      table = mkHandlers @effh (coerceRest hs)
    in
      Handler \comp -> runFn3 withImpl ret table comp
    where
    coerceRest :: Record hs -> Record rest
    coerceRest = unsafeCoerce

else instance buildHandlerIdentity ::
  ( TypeEquals a o
  , MkHandlers effh (Record hs) r o
  ) =>
  BuildHandler False False hs effh r a o where
  buildHandler hs =
    let
      ret = proof (undefinedReturnImpl :: RuntimeReturn r a a)
      table = mkHandlers @effh hs
    in
      Handler \comp -> runFn3 withImpl ret table comp

-- Runtime handler table in the machine's calling convention:
-- `{ eff: { op: clause } }`. `r` is the row the clauses may perform
-- into (the effects left after handling) and `o` the answer type.
foreign import data RuntimeHandlers :: Row EffType -> Type -> Type
foreign import data RuntimeClauses :: Row EffType -> Type -> Type
foreign import data RuntimeClause :: Row EffType -> Type -> Type

-- The return clause in the machine's convention: `a -> Hoop r o`,
-- or undefined for identity (in which case `a ~ o`). The PS-side
-- generator is a pure function; mkReturnImpl lifts its result by
-- wrapping in the `Var` node on the runtime side.
foreign import data RuntimeReturn :: Row EffType -> Type -> Type -> Type

foreign import mkReturnImpl :: forall r a o. (a -> o) -> RuntimeReturn r a o
foreign import undefinedReturnImpl :: forall r a. RuntimeReturn r a a

foreign import withImpl
  :: forall effa effb a b
   . Fn3
       (RuntimeReturn effb a b)
       (RuntimeHandlers effb b)
       (Hoop effa a)
       (Hoop effb b)

foreign import runImpl :: forall a. Hoop () a -> a

-- The clause adapters erase the handler's PS type; ClauseFor picks the
-- right one from the clause marker and is their only caller.
foreign import mkFullClauseImpl :: forall hsig r o. hsig -> RuntimeClause r o
foreign import mkFastClauseImpl :: forall hsig r o. hsig -> RuntimeClause r o

foreign import emptyHandlersImpl :: forall r o. Unit -> RuntimeHandlers r o
foreign import emptyClausesImpl :: forall r o. Unit -> RuntimeClauses r o
foreign import insertClausesImpl :: forall r o. Fn3 String (RuntimeClauses r o) (RuntimeHandlers r o) (RuntimeHandlers r o)
foreign import insertClauseImpl :: forall r o. Fn3 String (RuntimeClause r o) (RuntimeClauses r o) (RuntimeClauses r o)

-- | Convert a canonical handler record for `effh` into the runtime
-- | handler table, checking every clause against its operation signature
-- | along the way. Driven by the record the user actually wrote: only
-- | the clause markers are inspected structurally, everything else is
-- | plain unification, so unannotated lambdas (including aborting full
-- | clauses that never touch their continuation) are fully inferred.
class MkHandlers :: Row EffType -> Type -> Row EffType -> Type -> Constraint
class MkHandlers effh hs r o where
  mkHandlers :: hs -> RuntimeHandlers r o

instance mkHandlersImpl ::
  ( RowToList effh effhL
  , MkHandlersList effhL hsRow r o
  ) =>
  MkHandlers effh (Record hsRow) r o where
  mkHandlers = mkHandlersList @effhL

class MkHandlersList :: RowList EffType -> Row Type -> Row EffType -> Type -> Constraint
class MkHandlersList effhL hs r o where
  mkHandlersList :: Record hs -> RuntimeHandlers r o

-- The empty tail also closes the row: a clause record for an effect
-- outside `effh` fails the guard here, naming the offending field.
instance mkHandlersListNil ::
  ( RowToList hs hsL
  , UnexpectedFieldsGuard "A handler record may only contain the handled effects (and the reserved `pure`)." hsL
  ) =>
  MkHandlersList RL.Nil hs r o where
  mkHandlersList _ = emptyHandlersImpl unit

instance mkHandlersListCons ::
  ( Row.Cons efflbl (Record cls) rest hs
  , EffNewtype efftyp repr
  , RowToList repr reprL
  , MkHandlerClauses reprL cls r o
  , MkHandlersList tail rest r o
  , IsSymbol efflbl
  ) =>
  MkHandlersList (RL.Cons efflbl efftyp tail) hs r o where
  mkHandlersList hs =
    runFn3 insertClausesImpl
      efflbl
      (mkHandlerClauses @reprL (Record.get (Proxy :: _ efflbl) hs))
      (mkHandlersList @tail (coerceRest hs))
    where
    efflbl = reflectSymbol (Proxy :: _ efflbl)

    coerceRest :: Record hs -> Record rest
    coerceRest = unsafeCoerce

class MkHandlerClauses :: RowList Type -> Row Type -> Row EffType -> Type -> Constraint
class MkHandlerClauses reprL cls r o where
  mkHandlerClauses :: Record cls -> RuntimeClauses r o

-- The empty tail closes the row: a clause for an operation the effect
-- does not declare fails the guard here, naming the offending field.
instance mkHandlerClausesNil ::
  ( RowToList cls clsL
  , UnexpectedFieldsGuard "A clause record may only contain the effect's operations." clsL
  ) =>
  MkHandlerClauses RL.Nil cls r o where
  mkHandlerClauses _ = emptyClausesImpl unit

-- | Succeeds only on an empty RowList; otherwise fails with `msg` and
-- | the first offending field's name.
class UnexpectedFieldsGuard :: Symbol -> RowList Type -> Constraint
class UnexpectedFieldsGuard msg l

instance UnexpectedFieldsGuard msg RL.Nil

instance
  ( Fail
      ( Text msg
          |> (Text "  unexpected field: " ++ QuoteLabel l)
      )
  ) =>
  UnexpectedFieldsGuard msg (RL.Cons l t rest)

instance mkHandlerClausesCons ::
  ( Row.Cons op f rest cls
  , ClauseFor comp f r o
  , MkHandlerClauses tail rest r o
  , IsSymbol op
  ) =>
  MkHandlerClauses (RL.Cons op comp tail) cls r o where
  mkHandlerClauses cls =
    runFn3 insertClauseImpl
      op
      (toRuntimeClause @comp (Record.get (Proxy :: _ op) cls))
      (mkHandlerClauses @tail (coerceRest cls))
    where
    op = reflectSymbol (Proxy :: _ op)

    coerceRest :: Record cls -> Record rest
    coerceRest = unsafeCoerce

-- | Tie the clause the user wrote (`f`) to the operation signature
-- | `comp`. Only the marker constructor is matched structurally; the
-- | canonical handler type is computed from the signature (all inputs
-- | known) and forced onto `f` by the fundep, so shape errors — wrong
-- | arity, continuation misplaced, non-function — surface as unification
-- | failures against the canonical type.
class ClauseFor :: Type -> Type -> Row EffType -> Type -> Constraint
class ClauseFor comp f r o where
  toRuntimeClause :: f -> RuntimeClause r o

instance clauseForFull :: (FullSignature comp r o g) => ClauseFor comp (Clause Full g) r o where
  toRuntimeClause c = mkFullClauseImpl (unClause c)

else instance clauseForFast :: (FastSignature comp r o g) => ClauseFor comp (Clause Fast g) r o where
  toRuntimeClause c = mkFastClauseImpl (unClause c)

else instance clauseForDefault :: (FullSignature comp r o f) => ClauseFor comp f r o where
  toRuntimeClause = mkFullClauseImpl

-- | The canonical fully-controllable clause type for an operation
-- | signature: `a1 -> ... -> an ->* b` maps to
-- | `a1 -> ... -> an -> Cont b r o -> Hoop r o`.
class FullSignature :: Type -> Row EffType -> Type -> Type -> Constraint
class FullSignature comp r o f | comp r o -> f

instance FullSignature (a ->* b) r o (a -> Cont b r o -> Hoop r o)

else instance
  ( FullSignature rest r o f
  ) =>
  FullSignature (a -> rest) r o (a -> f)

else instance
  ( Fail (Text "The type of operation must be Function (->) or Computation (->*)")
  ) =>
  FullSignature _1 _2 _3 _4

-- | The canonical tail-resumptive clause type: the body computes the
-- | operation's result in the outer context:
-- | `a1 -> ... -> an ->* b` maps to `a1 -> ... -> an -> Hoop r b`.
class FastSignature :: Type -> Row EffType -> Type -> Type -> Constraint
class FastSignature comp r o f | comp r o -> f

instance FastSignature (a ->* b) r o (a -> Hoop r b)

else instance
  ( FastSignature rest r o f
  ) =>
  FastSignature (a -> rest) r o (a -> f)

else instance
  ( Fail (Text "The type of operation must be Function (->) or Computation (->*)")
  ) =>
  FastSignature _1 _2 _3 _4
