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

-- @inline export var always
-- @inline export read always
-- @inline export write always
-- @inline export assign always
-- @inline export installCellsNil(..).installCellsList always
-- @inline export installCellsCons(..).installCellsList always
-- @inline export varInitRecord(..).installCells always
-- @inline export varInitScalarWrapped(..).installCells always
-- @inline export varInitScalar(..).installCells always

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
  , HHandler
  , Handler
  , HandlerF
  , ScopeTactics
  , ScopedClause
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
  , class InstallCells
  , class SoleCell
  , class VarInit
  , class MkHandlerClauses
  , class MkHandlers
  , class MkHandlersList
  , class Perform
  , class PermitsClauses
  , class PermitsOps
  , class PerformEffect
  , class PerformList
  , class PerformScoped
  , class PerformScopedEffect
  , class PerformScopedList
  , class PerformScopedOp
  , class UnexpectedFieldsGuard
  , assign
  , continue
  , handler
  , handlerScoped
  , installCells
  , installCellsList
  , mkHandlers
  , mkHandlerClauses
  , mkHandlersList
  , perform
  , performEffect
  , performList
  , performScoped
  , performScopedEffect
  , performScopedList
  , performScopedOp
  , read
  , run
  , scoped
  , toRuntimeClause
  , var
  , with
  , withF
  , write
  , (:=)
  ) where

import Prelude

import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4, runFn2, runFn3, runFn4)
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Hoop.TypeUtil (class HasLabel, class RowListLength, type (++), type (:), type (|>), List, Nil)
import Hoop.Types (class EffNewtype, class MkAction, type (->*), AlgOnly, AllowScoped, AnyPayload, Clause, EffType, EvKey(..), Fast, Full, HCapability, HSig, Local, Region, Scalar(..), Scoped, asAnyPayload, evKey, mkAction, mkRegion, unClause)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Boolean (False, True)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Prim.TypeError (class Fail, QuoteLabel, Text)
import Record as Record
import Record.Unsafe as RU
import Type.Equality (class TypeEquals, proof, to)
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

-- The reserved label is not an effect the surface can reach: cells are
-- read and written by `read` / `write`, never performed. The runtime
-- agrees -- `Hoop.Runtime.WellScopedness` makes a `Perform` under
-- `var_eff` ill scoped outright.
instance performListVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells and has no operations to perform."
          |> Text "  Use `read @\"label\"` / `write @\"label\"` on the region `var` hands out."
      )
  ) =>
  PerformList (RL.Cons "%hoop.var" _1 RL.Nil) _2 _3 where
  performList = unsafeCrashWith "impossible"

else instance performListImpl ::
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

-- The same guard as on `PerformList`, repeated here because
-- `performEffect` is exported and names its effect label by type
-- application, so it is a way round that one. The runtime's `perform_impl`
-- does not check the reserved name -- `ws` merely assumes it -- which
-- makes this the boundary where the assumption is enforced.
instance performEffectVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells and has no operations to perform."
          |> Text "  Use `read @\"label\"` / `write @\"label\"` on the region `var` hands out."
      )
  ) =>
  PerformEffect "%hoop.var" _1 _2 _3 _4 where
  performEffect = unsafeCrashWith "impossible"

else instance performEffectImpl1 ::
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

{------------ Typed `performScoped` API ------------}

foreign import performScopedImpl
  :: forall r a
   . Fn4
       String -- eff
       String -- op
       String -- evkey
       (Array AnyPayload)
       (Hoop r a)

-- | **Perform a scoped operation.** The payload is the one higher-order value
-- | the operation's signature declares, `h (Hoop r) b`, and it carries the
-- | inner computations inside itself.
-- |
-- | The runtime never looks inside it. It is one opaque payload element like
-- | any other, and that is deliberate: a machine that traversed the inner
-- | computations would owe an `HFunctor` obligation on `h`, and the whole
-- | design exists to avoid asking for one. Locating and running the inner
-- | computations is the clause's job, through the capability it is handed.
class PerformScoped :: Row EffType -> Symbol -> Type -> Constraint
class PerformScoped eff op comptyp | eff op -> comptyp where
  performScoped :: comptyp

instance performScopedImpl' ::
  ( RowToList eff effL
  , PerformScopedList effL op comptyp
  ) =>
  PerformScoped eff op comptyp
  where
  performScoped = performScopedList @effL @op

class PerformScopedList :: RowList EffType -> Symbol -> Type -> Constraint
class PerformScopedList effL op comptyp | effL op -> comptyp where
  performScopedList :: comptyp

-- The reserved label, guarded exactly as on `PerformList` and for the same
-- reason: `Hoop.Runtime.WellScopedness` makes any `Perform` under `var_eff`
-- ill scoped, and a `PerformS` is no exception.
instance performScopedListVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells and has no operations to perform."
          |> Text "  Use `read @\"label\"` / `write @\"label\"` on the region `var` hands out."
      )
  ) =>
  PerformScopedList (RL.Cons "%hoop.var" _1 RL.Nil) _2 _3 where
  performScopedList = unsafeCrashWith "impossible"

else instance performScopedListImpl ::
  ( EffNewtype efftyp repr
  , PerformScopedEffect efflbl efftyp repr op comptyp
  ) =>
  PerformScopedList (RL.Cons efflbl efftyp RL.Nil) op comptyp where
  performScopedList = performScopedEffect @efflbl @efftyp @repr @op

else instance
  ( Fail (Text """You must specify effect row with exactly 1 element. e.g.: `performScoped @(OP ()) @"op"...` where `type OP r = (op :: Op | r)`""")
  ) =>
  PerformScopedList _1 _2 _3 where
  performScopedList = unsafeCrashWith "impossible"

class PerformScopedEffect :: Symbol -> EffType -> Row Type -> Symbol -> Type -> Constraint
class PerformScopedEffect efflbl efftyp repr op comptyp | efflbl efftyp repr op -> comptyp where
  performScopedEffect :: comptyp

instance performScopedEffectVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells and has no operations to perform."
          |> Text "  Use `read @\"label\"` / `write @\"label\"` on the region `var` hands out."
      )
  ) =>
  PerformScopedEffect "%hoop.var" _1 _2 _3 _4 where
  performScopedEffect = unsafeCrashWith "impossible"

else instance performScopedEffectImpl ::
  ( Row.Cons op comp _r repr
  , PerformScopedOp efflbl efftyp op comp comptyp
  ) =>
  PerformScopedEffect efflbl efftyp repr op comptyp
  where
  performScopedEffect = performScopedOp @efflbl @efftyp @op @comp

-- | The last step, and the one that decides whether the operation is scoped at
-- | all. Split out from `PerformScopedEffect` so that the operation's declared
-- | type appears in an instance HEAD.
-- |
-- | That placement is load-bearing. With the shape written into
-- | `PerformScopedEffect`'s head instead, or imposed by an equality in its
-- | context, the use site's expected type is unified against
-- | `h (Hoop eff) b -> Hoop eff b` before anything has looked at what the
-- | operation actually is, and performing an ordinary operation scoped reports
-- | "could not match `Unit` with `t1 (Hoop t2) t3`". Here the ordinary
-- | signature simply fails to match the first head, the chain falls through,
-- | and the failure says what is wrong.
class PerformScopedOp :: Symbol -> EffType -> Symbol -> Type -> Type -> Constraint
class PerformScopedOp efflbl efftyp op comp comptyp | efflbl efftyp op comp -> comptyp where
  performScopedOp :: comptyp

instance performScopedOpScoped ::
  ( Row.Cons efflbl efftyp _2 eff
  , IsSymbol efflbl
  , IsSymbol op
  ) =>
  PerformScopedOp efflbl efftyp op (Scoped h) (h (Hoop eff) b -> Hoop eff b)
  where
  performScopedOp payload =
    runFn4 performScopedImpl eff op key [ asAnyPayload payload ]
    where
    eff = reflectSymbol (Proxy :: _ efflbl)
    op = reflectSymbol (Proxy :: _ op)
    key = case evKey eff op of EvKey k -> k

else instance performScopedOpRefused ::
  ( Fail
      ( Text "This operation is not scoped, so it cannot be performed with `performScoped`."
          |> (Text "  offending operation: " ++ QuoteLabel efflbl ++ Text "." ++ QuoteLabel op)
          |> Text "  Declare it as `Scoped h` in the effect's representation, or use `perform`."
      )
  ) =>
  PerformScopedOp efflbl _0 op _1 _2 where
  performScopedOp = unsafeCrashWith "impossible"

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

-- | **A handler instance at one answer type, indexed by what it is permitted
-- | to admit.** The `H` is for higher-order: this is the type that tracks
-- | whether a higher-order clause may appear, and it is the counterpart of
-- | `Hoop.Types.HSig` on the handler side.
-- |
-- | The capability is decided by the *consumer*, not by the builder. `handler`
-- | leaves it open; `with` fixes it to `AlgOnly` and `handlerScoped` to
-- | `AllowScoped`, so the very same clause record is admitted or refused
-- | according to what it is eventually used by. That is what makes one builder
-- | serve both paths without either being able to borrow the other's
-- | permission.
-- |
-- | Ordinary users never write this type: `Handler` below is the synonym at
-- | `AlgOnly`, and existing annotations keep working unchanged.
-- |
-- | The constructor is not exported. Nothing outside this module may claim a
-- | capability it was not given.
newtype HHandler :: HCapability -> Row EffType -> Row EffType -> Type -> Type -> Type
newtype HHandler capability effh r a o = HHandler (forall effa. Hoop effa a -> Hoop r o)

-- `capability` and `effh` are both phantom in the representation -- the
-- installer's type mentions neither -- so role inference would make them
-- coercible. Neither may be: one is the permission, the other is the claim
-- about which effects get discharged. `handler` re-indexes the capability by
-- unwrapping and rewrapping the constructor, which roles do not govern, so
-- pinning everything nominal costs nothing and leaves `coerce` no way in.
type role HHandler nominal nominal nominal nominal nominal

-- | A handler over ordinary algebraic operations — what `with` installs, and
-- | what almost every handler is.
type Handler :: Row EffType -> Row EffType -> Type -> Type -> Type
type Handler effh r a o = HHandler AlgOnly effh r a o

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
with (HHandler install) comp = install comp

-- | **A handler that can be reinstalled at any result type.** Where an
-- | `HHandler` answers at one fixed `o`, this answers at `f b` for every `b`.
-- |
-- | That is exactly what a scoped operation needs. A scoped clause runs an
-- | inner computation whose result type is not the answer type of the handler
-- | that contains the clause -- the machine reinstalls the handler around the
-- | scope, and reinstalling it at a *different* result type is only meaningful
-- | if the table was built for every result type. A single `HHandler` cannot
-- | supply that; a family can.
-- |
-- | `f` is the answer former: the shape the handler wraps its result in
-- | (`Array` for a non-determinism handler, `Either e` for an exception
-- | handler). It is what the return clause produces, so a handler with a
-- | scoped clause needs a `pure` clause -- without one `o ~ a`, `f` collapses
-- | to the identity, and no scope can be given a different answer than its
-- | context.
-- |
-- | *Separate from `HHandler` / `with` by decision of the borrowable
-- | milestone, not of the final higher-order API.* Whether the two collapse
-- | into one once general higher-order operations arrive is open.
newtype HandlerF :: Row EffType -> Row EffType -> (Type -> Type) -> Type
newtype HandlerF effh r f = HandlerF (forall effa b. Hoop effa b -> Hoop r (f b))

-- Same reasoning as `HHandler`: `effh` is phantom in the representation and
-- must not be coercible, since it is the claim about which effects this family
-- discharges. `r` and `f` do occur, so inference would already pin them.
type role HandlerF nominal nominal nominal

-- | **Close a handler into a family.** The argument is polymorphic in the
-- | result type: the whole clause table is checked at *every* `b`, not at one,
-- | which is what makes reinstallation around a scope sound.
-- |
-- | This is the only way to obtain a `HandlerF`, and `withF` is the only way
-- | to install one, so a table carrying a scoped clause cannot reach the
-- | machine without having been checked at every result type. The other half
-- | of that guarantee is `PermitsClauses`, which stops such a table from being
-- | installed by ordinary `with`.
handlerScoped
  :: forall effh r f
   . (forall b. HHandler AllowScoped effh r b (f b))
  -> HandlerF effh r f
handlerScoped h = HandlerF \comp -> case h of HHandler install -> install comp

-- | Handle the effects `effh` with a family, wrapping the result in `f`.
withF
  :: forall effh effb effa a f
   . Row.Union effh effb effa
  => HandlerF effh effb f
  -> Hoop effa a
  -> Hoop effb (f a)
withF (HandlerF install) comp = install comp

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
  :: forall effh effhL pureEff hs' hsRow hsL hasPure r a o capability
   . RowToList effh effhL
  => HasLabel effhL "pure" pureEff
  => PermitsClauses capability effhL
  => CanonicalizeHandlers effh hs' (Record hsRow)
  => RowToList hsRow hsL
  => HasLabel hsL "pure" hasPure
  => BuildHandler pureEff hasPure hsRow effh r a o
  => Proxy effh
  -> hs'
  -> HHandler capability effh r a o
handler p hs' =
  coerceCapability (buildHandler @pureEff @hasPure (canonicalizeHandlers p hs' :: Record hsRow))
  where
  -- `BuildHandler` produces the `AlgOnly` synonym; the capability is a
  -- *permission*, decided by `PermitsClauses` above and carried in the type
  -- only. It indexes nothing at run time -- both capabilities install the same
  -- installer -- so unwrapping and rewrapping the newtype is the whole
  -- conversion. Total, checked, and free once the newtype is erased.
  coerceCapability :: Handler effh r a o -> HHandler capability effh r a o
  coerceCapability (HHandler install) = HHandler install

-- | **What a handler built at this capability is allowed to contain.**
-- |
-- | A `Scoped` operation needs its handler re-instantiated at the scope's
-- | result type, and a single `HHandler` cannot supply that -- only the
-- | `forall`-quantified family `handlerScoped` takes can. So a scoped clause
-- | under `AlgOnly` is refused here, at the point the handler is built, rather
-- | than left to misbehave at run time.
-- |
-- | *Why this is a predicate and not another parameter of `MkHandlers`.*
-- | Threading the capability through the classes that BUILD the table was tried
-- | and does not work: their methods (`mkHandlers`, `toRuntimeClause`) do not
-- | mention it, so nothing at a use site determines it and the instance chain
-- | stalls on an unknown, reporting a partial overlap instead of the intended
-- | `Fail`. Carrying no method is not by itself what saves this class -- a
-- | method-less class stalls just the same when its index is undetermined.
-- | What saves it is that `capability` occurs in `handler`'s RESULT type, so it
-- | is fixed at the point the handler is consumed: `with` demands `AlgOnly`,
-- | `handlerScoped` demands `AllowScoped`. The predicate is then discharged
-- | against a known capability, never against an unknown.
-- |
-- | *Why walking the row is safe here.* `effh` is closed by construction --
-- | `handler` already demands `RowToList effh effhL` to find its clauses, and
-- | each effect's `repr` is a closed row supplied by `EffNewtype`. This walks
-- | exactly the structure `MkHandlersList` already walks; it adds no
-- | requirement that a row be closed which was not there before.
class PermitsClauses :: HCapability -> RowList EffType -> Constraint
class PermitsClauses capability effhL

instance permitsClausesNil :: PermitsClauses capability RL.Nil

instance permitsClausesCons ::
  ( EffNewtype efftyp repr
  , RowToList repr reprL
  , PermitsOps capability efflbl reprL
  , PermitsClauses capability tail
  ) =>
  PermitsClauses capability (RL.Cons efflbl efftyp tail)

-- | The same, one effect's operations at a time. Split out so the failure can
-- | name the effect and the operation rather than the whole row.
class PermitsOps :: HCapability -> Symbol -> RowList Type -> Constraint
class PermitsOps capability efflbl reprL

instance permitsOpsNil :: PermitsOps capability efflbl RL.Nil

-- A scoped operation is permitted by exactly one capability, and it is named
-- here. Everything else is denied by the arm below, so a capability added later
-- starts out with no scoped permission and has to be granted one deliberately.
instance permitsOpsScopedAllowed ::
  ( PermitsOps AllowScoped efflbl tail
  ) =>
  PermitsOps AllowScoped efflbl (RL.Cons op (Scoped h) tail)

-- A scoped operation reached through the ordinary path. This is the fixture of
-- the whole capability index: without it, a monomorphic table carrying a scoped
-- clause installs happily and misrepresents the scope's value at run time.
else instance permitsOpsScopedRefused ::
  ( Fail
      ( Text "A scoped operation cannot be handled by an ordinary `handler`."
          |> (Text "  offending operation: " ++ QuoteLabel efflbl ++ Text "." ++ QuoteLabel op)
          |> Text "  Its clause runs inner computations at a result type this handler does not have,"
          |> Text "  so the handler must be built as a family: use `handlerScoped` and install with `withF`."
      )
  ) =>
  PermitsOps AlgOnly efflbl (RL.Cons op (Scoped h) tail)

-- Any other capability. No other capability is provided by this library today,
-- but `HCapability` is an open kind: a user can declare their own inhabitant
-- and pin a handler's result to it, which reaches this arm. So this is not a
-- placeholder for a future extension -- it is the arm that keeps a capability
-- nobody vetted from being scoped-permissive by default.
else instance permitsOpsScopedDenied ::
  ( Fail
      ( Text "A scoped operation is not permitted by this handler capability."
          |> (Text "  offending operation: " ++ QuoteLabel efflbl ++ Text "." ++ QuoteLabel op)
      )
  ) =>
  PermitsOps capability efflbl (RL.Cons op (Scoped h) tail)

else instance permitsOpsCons ::
  ( PermitsOps capability efflbl tail
  ) =>
  PermitsOps capability efflbl (RL.Cons op comp tail)

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

-- A region is opened by `var` and by nothing else. The runtime cannot
-- represent a handler table that binds a cell -- `keys` is provably free
-- of `VarKey` (`Hoop.Runtime.Handlers.keys_no_var`) -- so this guard has
-- no soundness to protect; it is here to say so in words.
instance canonicalizeHandlersListVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells; no handler can be written for it."
          |> Text "  Use `var` to open a region of cells around the handler."
      )
  ) =>
  CanonicalizeHandlersList (RL.Cons "%hoop.var" _1 _2) from to where
  canonicalizeHandlersList _ _ = unsafeCrashWith "impossible"

else instance canonicalizeHandlersListCons ::
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
      HHandler \comp -> runFn3 withImpl ret table comp
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
      HHandler \comp -> runFn3 withImpl ret table comp

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

-- The same guard, for the callers that reach the table builder without
-- going through `canonicalizeHandlers` first.
instance mkHandlersListVar ::
  ( Fail
      ( Text "`%hoop.var` is reserved for prompt-local cells; no handler can be written for it."
          |> Text "  Use `var` to open a region of cells around the handler."
      )
  ) =>
  MkHandlersList (RL.Cons "%hoop.var" _1 _2) hs r o where
  mkHandlersList _ = unsafeCrashWith "impossible"

else instance mkHandlersListCons ::
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

-- Dispatched on the OPERATION, not on the clause value. Matching
-- `ScopedClause h ff r o` in the second position instead leaves `r` and `o` as
-- unknowns at the point the chain is consulted -- the clause's own type is
-- being inferred from the lambda the user wrote -- and the solver refuses to
-- commit to an instance head containing unknowns. The operation is always
-- known, so keying on it commits immediately and the equality below is what
-- forces the clause into shape.
else instance clauseForScoped ::
  ( TypeEquals f (ScopedClause h ff r o)
  ) =>
  ClauseFor (Scoped h) f r o where
  toRuntimeClause c = case to c of
    ScopedClause g -> mkScopedClauseImpl (scopedBody g)

else instance clauseForDefault :: (FullSignature comp r o f) => ClauseFor comp f r o where
  toRuntimeClause = mkFullClauseImpl

-- | The canonical fully-controllable clause type for an operation
-- | signature: `a1 -> ... -> an ->* b` maps to
-- | `a1 -> ... -> an -> Cont b r o -> Hoop r o`.
class FullSignature :: Type -> Row EffType -> Type -> Type -> Constraint
class FullSignature comp r o f | comp r o -> f

instance FullSignature (a ->* b) r o (a -> Cont b r o -> Hoop r o)

-- A scoped operation reached by an ordinary clause. Without this arm the user
-- is told the signature "must be Function or Computation", which is true of
-- ordinary operations and useless here.
else instance
  ( Fail
      ( Text "This is a scoped operation, so its clause must be built with `scoped`."
          |> Text "  An ordinary `full` / `fast` clause cannot run the computations the payload carries."
      )
  ) =>
  FullSignature (Scoped h) _2 _3 _4

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
  ( Fail
      ( Text "This is a scoped operation, so its clause must be built with `scoped`."
          |> Text "  An ordinary `full` / `fast` clause cannot run the computations the payload carries."
      )
  ) =>
  FastSignature (Scoped h) _2 _3 _4

else instance
  ( FastSignature rest r o f
  ) =>
  FastSignature (a -> rest) r o (a -> f)

else instance
  ( Fail (Text "The type of operation must be Function (->) or Computation (->*)")
  ) =>
  FastSignature _1 _2 _3 _4

{------------ Scoped clauses ------------}

foreign import mkScopedClauseImpl :: forall h f r o. ScopedBody h f r o -> RuntimeClause r o

-- The machine's calling convention for a scoped clause, and the shape
-- `mkScopedClause` in hoop_prim.js curries into: the operation's one payload,
-- then the weave capability, then the continuation.
--
-- NOT EXPORTED. The raw weave is a bare `Hoop inner x -> Hoop r (f x)`, and
-- handing it to a clause would leak two things the tactics record is there to
-- withhold: that the intervening context is trivial at this milestone, and that
-- `weave` may be applied to a computation the clause did not receive. The
-- clause sees `ScopeTactics` and nothing else.
type ScopedBody :: HSig -> (Type -> Type) -> Row EffType -> Type -> Type
type ScopedBody h f r o =
  forall b inner
   . h (Hoop inner) b
  -> (forall x. Hoop inner x -> Hoop r (f x))
  -> Cont b r o
  -> Hoop r o

-- | **What a scoped clause may do with the computations it was handed.**
-- |
-- | Three operations, and their roles do not overlap: `runScope` introduces a
-- | context, `bindScope` extends one, `resumeScope` eliminates one onto the
-- | continuation. Each was demanded by a clause that could not be written
-- | without it, and nothing further was — no `pureScope`, and deliberately no
-- | inspector.
-- |
-- | `f` is the handler's own answer former and is concrete: a clause may match
-- | on it, and `catch` must (it tells failure from success by it). `ctx` is the
-- | dynamically intervening context and is bound by the clause's own `forall`:
-- | unnameable, uninspectable, unchooseable. Folding the two into one layer
-- | makes `catch` inexpressible, which is why the shape is `f (ctx x)` rather
-- | than a single functor.
-- |
-- | **A trap worth naming.** Sequencing two inner computations by calling
-- | `bindScope` twice on the same context typechecks and is wrong: it re-enters
-- | the intervening context twice, which for a nondeterministic `ctx`
-- | duplicates branches. Sequence inside `Hoop inner` instead, and use one
-- | `bindScope` on the result.
type ScopeTactics :: (Type -> Type) -> (Type -> Type) -> Row EffType -> Row EffType -> Type -> Type
type ScopeTactics f ctx inner r o =
  { runScope :: forall x. Hoop inner x -> Hoop r (f (ctx x))
  , bindScope :: forall x y. ctx x -> (x -> Hoop inner y) -> Hoop r (f (ctx y))
  , resumeScope :: forall x. ctx x -> Cont x r o -> Hoop r o
  }

-- | **A clause for a scoped operation.** Built by `scoped`; the constructor is
-- | not exported.
-- |
-- | `inner` is the row the payload's computations run in and `b` is the
-- | operation's result: both are bound here, so the clause cannot choose
-- | either.
-- |
-- | Note what that does and does not rule out. The clause may certainly build
-- | computations of its own — `pure x` is a `Hoop inner x`, and so is anything
-- | it maps or binds onto a computation it was handed. What it cannot build is
-- | a computation demanding a capability the rigid `inner` does not have. So
-- | the guarantee is: **everything reaching `runScope` is typed at the clause's
-- | own rigid inner family**, which is exactly the assumption
-- | `Hoop.Runtime.WellScopedness.apply_scoped_ok` makes and the FFI cannot
-- | check — see the note at `apply_scoped` in
-- | runtime/ml/melange/hoop_ffi.ml.
newtype ScopedClause :: HSig -> (Type -> Type) -> Row EffType -> Type -> Type
newtype ScopedClause h f r o = ScopedClause
  ( forall b inner ctx
     . h (Hoop inner) b
    -> ScopeTactics f ctx inner r o
    -> Cont b r o
    -> Hoop r o
  )

type role ScopedClause nominal nominal nominal nominal

-- | Mark a clause as scoped: it receives the operation's higher-order payload,
-- | the scope tactics, and the continuation.
scoped
  :: forall h f r o
   . ( forall b inner ctx
        . h (Hoop inner) b
       -> ScopeTactics f ctx inner r o
       -> Cont b r o
       -> Hoop r o
     )
  -> ScopedClause h f r o
scoped = ScopedClause

-- The tactics record, at `ctx ~ Identity`.
--
-- That is the intervening context at the borrowable milestone: a scope here
-- runs under prompts that were borrowed whole, so nothing sits between the
-- scope and its answer. The clause is quantified over `ctx` and cannot tell,
-- which is what keeps the general case open at no cost -- `Identity` erases.
--
-- `Identity` is introduced on the way IN, inside the computation, so `weave`
-- is instantiated at `Identity x` and hands back the `Hoop r (f (Identity x))`
-- the tactics record asks for. Every step is a legitimate instantiation of the
-- weave's own `forall`; nothing here is coerced.
--
-- Introducing it on the way out instead -- `unsafeCoerce (weave body)` --
-- would be a coercion `Hoop r (f x) -> Hoop r (f (Identity x))`, which is NOT
-- justified by `Identity` erasing. The change is under `f`, and `f` is a rigid
-- variable whose argument need not be representational, so that spelling adds
-- a representation assumption to the trusted base that no proof covers. It is
-- also unreachable for `coerce`, for the same reason.
--
-- The price is one `map` per `runScope` or `bindScope` invocation, which the
-- monad laws make the identity. Optimising it away is a separate matter from
-- getting it right.
scopeTactics
  :: forall f inner r o
   . (forall x. Hoop inner x -> Hoop r (f x))
  -> ScopeTactics f Identity inner r o
scopeTactics weave =
  { runScope: \body -> weave (Identity <$> body)
  , bindScope: \cx g -> weave (Identity <$> g (unwrap cx))
  , resumeScope: \cx k -> continue k (unwrap cx)
  }

scopedBody
  :: forall h f r o
   . ( forall b inner ctx
        . h (Hoop inner) b
       -> ScopeTactics f ctx inner r o
       -> Cont b r o
       -> Hoop r o
     )
  -> ScopedBody h f r o
scopedBody g = \payload weave k -> g payload (scopeTactics weave) k

{------------ Prompt-local cells ------------}

-- The three cell primitives, in the machine's calling convention.
-- `newCellImpl` is the one that changes the row: it wraps a computation
-- running with the cell installed into one running without it, which is
-- exactly what `NewP` does to the stack.
--
-- NOT EXPORTED, AND LOAD-BEARING. `var` is the only caller, and the
-- placement invariant recorded on `var` -- the one that makes cell labels
-- safe to collide -- holds because of that. Export this, or call it from
-- anywhere else, and a cell can be installed at a stack position that is
-- not directly below its handler's prompt; the invariant is then lost,
-- innermost-wins starts resolving a clause to somebody else's cell, and
-- labels have to be minted per dynamic instantiation to get the guarantee
-- back. That is a different design, not a patch: a minted label is not a
-- `Symbol`, so it cannot key the row token, and the type-level scope
-- discipline would have to be rebuilt on something else.
--
-- Worth re-reading before scoped effects: an operation that carries a
-- computation gets to decide where that computation runs, which is exactly
-- the freedom this invariant assumes nobody has.
foreign import newCellImpl :: forall inner outer a o. Fn3 String a (Hoop inner o) (Hoop outer o)
foreign import readCellImpl :: forall r a. String -> Hoop r a

-- Evaluates to the value written, not to unit: the `WriteP` rule steps to
-- `Var x`. `write` below returns it; `assign` is the one that discards it.
foreign import writeCellImpl :: forall r a. Fn2 String a (Hoop r a)

-- | The region a closed `var` is instantiated at. The region variable is a
-- | phantom used only to keep two regions apart under the rank-2 `forall`
-- | in `var`; once `var` has discharged the token there is nothing left to
-- | tell apart, so the caller's `s` is instantiated here.
data Closed

-- | Open a region of prompt-local cells around a handler.
-- |
-- | ```purs
-- | with
-- |   (var { count: 0 } \c ->
-- |      handler (Proxy :: _ (STATE Int + ()))
-- |        { state:
-- |            { get: fast \_ -> read @"count" c
-- |            , set: fast \n -> write @"count" c n
-- |            }
-- |        })
-- |   program
-- | ```
-- |
-- | The record of initial values is the region's declaration: one cell per
-- | field, named by the field and typed by the value. The callback receives
-- | the region token, and the row it works in carries the matching
-- | `Local`, which `var` discharges -- so a cell is reachable from the
-- | handler's clauses and from nothing outside them.
-- |
-- | This is precisely nested `NewP` around the handler's prompt: cells sit
-- | *below* it, so a clause (which runs outside its own prompt) can reach
-- | them, and a captured continuation carries its own copy of their
-- | contents.
-- |
-- | **THE PLACEMENT INVARIANT.** *Cells are installed directly below their
-- | own handler's prompt, and a clause runs on the stack below that
-- | prompt. So the first frame of a given label that a clause meets is
-- | always its own handler's, whatever else is stacked above.*
-- |
-- | This is why cell labels need not be unique, and they are not: they are
-- | field names, and a bare `var` uses one reserved label for every region
-- | it ever opens. Two regions in one stack routinely share a label, and
-- | the machine's rule is innermost-wins, so a collision would be a *wrong
-- | answer* rather than a crash -- the worse failure mode. The invariant is
-- | what rules it out, and it holds for one reason only: `newCellImpl` is
-- | private and `var` is its sole caller, so nothing can install a cell
-- | anywhere else. See the note there for what breaks if that changes.
-- |
-- | The invariant is pinned by two tests in `Test.Hoop` ("two regions
-- | sharing a label each see their own cell", "the same handler nested in
-- | itself does not shadow its own cell"), not proved. F* proves what
-- | `NewP` / `ReadP` / `WriteP` mean; where the surface *puts* them is this
-- | module's obligation.
-- |
-- | **Re-derived for scoped borrowing, and it holds.** A scoped operation
-- | lets a clause choose where an inner computation runs, which is the case
-- | the invariant did not originally cover. `prepare_scope` settles it:
-- | borrowing keeps every `ParamF` entire -- label *and* value -- and is a
-- | filter-and-rewrite that never reorders frames, so a borrowed clause still
-- | meets its own handler's cell first, with no label minting at run time.
-- |
-- | Three separate results back that, and they answer different questions:
-- |
-- | * *Capability preservation* — `Hoop.Runtime.Metatheory.borrow_param` gives
-- |   `param_in l (borrow k) <==> param_in l k`, and `prepare_scope_can` lifts
-- |   it to the whole prepared segment. This is about which cells a scope can
-- |   still REACH. It says nothing about their values or their order, and
-- |   dropping the `ParamF` clause would make `prepare_scope_can` false.
-- | * *Structure preservation* — `Hoop.Runtime.Semantics.prepare_scope_fast_agrees`
-- |   proves the shipped accumulating walk computes the specification's list
-- |   exactly, so "keeps label and value, never reorders" is a claim about
-- |   what actually runs and not only about the `noextract` spec.
-- | * *The list itself* — fixtures 35-40 in `Hoop.Runtime.Test` normalise it.
-- |   36 pins that a cell survives with BOTH label and value; 39 pins order on
-- |   an interleaved segment (two binds, two cells, two prompts, owner last)
-- |   that nothing reordered, deduplicated or reversed would satisfy; 40 spells
-- |   the same expected list out again through `prepare_scope_fast`, and was
-- |   perturbed by hand -- the two prompts swapped -- and confirmed to fail
-- |   before the expected value was restored.
-- |
-- | Note the consequence, which is a semantic fact rather than a hazard: the
-- | frame carries the *value*, so a scope receives a snapshot that branches.
-- | A cell stays live across a scope only for a handler installed outside the
-- | scoped one -- composition order decides it.
-- |
-- | What F\* proves is that the machine preserves cell reachability across a
-- | borrow. That the *surface* still installs cells nowhere but under `var`
-- | remains this module's obligation, and it is now pinned end to end rather
-- | than inspected: `Test.Scoped`, "a borrowed cell is a snapshot; a cell
-- | outside the scope stays live", runs two regions that share the reserved
-- | scalar label -- one inside the scoped handler, one outside it -- across a
-- | borrowed scope, reading and writing both, and answers
-- | `[ 200, 999, 200, 42 ]`. The four positions separate the three claims:
-- | the scope meets the nearer cell (200, not the outer 7), a write inside is
-- | visible inside (999), the borrowed cell is a snapshot (200 again after
-- | return, not 999), and the cell outside the scope is live (42).
-- | `test/js/engine-smoke.mjs` pins the snapshot half again below the surface.
-- |
-- | **A handler polymorphic in its cell's type must say `scalar`.** The
-- | record-or-not dispatch is an instance chain, and with the initial
-- | value's type abstract there is nothing to dispatch on: the chain
-- | stalls on the record instance rather than falling through to the
-- | scalar one, and reports it as a partial overlap. Naming the reading
-- | settles it, and the region row stays concrete in shape (one cell)
-- | while its contents stay abstract, which is what `read` needs.
-- |
-- | ```purs
-- | handleState :: forall s r a. s -> Handler (STATE s ()) r a a
-- | handleState init = var (scalar init) \c ->   -- ✗ without `scalar`
-- |   handler (Proxy :: _ (STATE s ()))
-- |     { state: { get: fast \_ -> read c, set: fast \s' -> c := s' } }
-- | ```
-- |
-- | `Hoop.State.handleState` is that handler, and is the worked example.
-- |
-- | **Declare a handler's cells in one `var`, not in nested ones.** Every
-- | region's token sits in the row under the same reserved label, so
-- | nesting duplicates that label and only the innermost is reachable:
-- |
-- | ```purs
-- | var { outer: 1 } \c1 ->        -- legal, but c1 is out of reach below
-- |   var { inner: 2 } \c2 ->
-- |     handler ...
-- |       { get: fast \_ -> read @"inner" c1 }   -- ✗ s0 vs s1, at "%hoop.var"
-- |
-- | var { outer: 1, inner: 2 } \c ->             -- ✓ one region, both cells
-- |   handler ... { get: fast \_ -> read @"outer" c }
-- | ```
-- |
-- | The failure is a type error naming `%hoop.var` and two region
-- | variables, never a wrong answer, so the rule is enforced -- just not
-- | explained -- by the compiler. Lifting it would need the token to carry
-- | a *stack* of regions, and extending that stack is a class whose result
-- | mentions `s`, which is exactly what cannot be solved under the rank-2
-- | `forall` that makes the containment work. Fresh labels would not help:
-- | a row label is a `Symbol`, and there is no minting one.
-- |
-- | **Escape is a type error.** `s` is bound by the callback's own
-- | `forall`, and every way to touch a cell mentions it -- the token, and
-- | any computation reading or writing through it. None of them can be
-- | smuggled out through an operation's result, the answer type or a
-- | continuation, because all three are fixed outside the region. Naming a
-- | cell by type application rather than by a handle value is what buys
-- | this: there is no per-cell token whose type could forget the region.
-- |
-- | **This is `ST`, not `StateT`.** Settled deliberately, so read it as a
-- | positioning rather than as a stage on the way somewhere.
-- |
-- | A cell is a binder with a lifetime. `var` is `runST` and `Region s` is
-- | `ST s`: the rank-2 `forall` bounds the lifetime, and outside it there
-- | is nothing left to observe. The state consequently does *not* appear
-- | in the handler's answer type, and a cell-backed handler is
-- | `Handler effh r a a` -- never `Handler effh r a (a /\ s)`.
-- |
-- | Two things follow, and neither is a gap to be closed later.
-- |
-- |   - **A cell-backed handler does not hand back its final state.** The
-- |     return clause is a pure `a -> o` and cannot read a cell, and there
-- |     is no way round that within this reading. Wanting the final state
-- |     means wanting a state *monad*, and that is the other handler: the
-- |     parameter-passing one, written with `full` clauses and an answer
-- |     type of `s -> Hoop r (a /\ s)`. `Test.Hoop.statePP` is it. The two
-- |     coexist on purpose -- cells buy tail resumption, parameter passing
-- |     buys the state in the answer.
-- |
-- |   - **There is no `with`-variant that opens a region around a whole
-- |     computation.** One would work -- a body sits above the cell frames
-- |     and the search runs downward, so it would reach them, and it would
-- |     be the way to get the final state out with `fast` clauses intact.
-- |     It is left out because it makes cells readable *and writable* by
-- |     the handled program, and a handler's local state being poked at by
-- |     the code it handles is not what a cell is for. `with` stays a
-- |     single combinator.
-- Polymorphic in the capability, and it has to be: a scoped handler is as
-- entitled to keep state in a cell as an ordinary one, and pinning this to
-- `Handler` would make that unsayable. Installing cells says nothing about
-- which clauses a table may carry, so the permission passes straight through.
var
  :: forall init inits effh r a o capability
   . VarInit init inits
  => init
  -> ( forall s
        . Region s inits
       -> HHandler capability effh ("%hoop.var" :: Local s inits | r) a o
     )
  -> HHandler capability effh r a o
var init k =
  let
    inner :: HHandler capability effh ("%hoop.var" :: Local Closed inits | r) a o
    inner = k mkRegion
  in
    case inner of
      HHandler install -> HHandler \comp -> installCells init (install comp)

-- | Read a cell of the open region. The `Row.Cons` constraint is the
-- | cell's membership in it: a label the region does not declare, or one
-- | declared at another type, has nothing to match.
-- |
-- | The label may be omitted when the region declares exactly one cell --
-- | always the case for a bare `var 0`, and the reason it needs no field
-- | name. For a record, prefer writing it: `read c` on a one-field record
-- | stops compiling the day a second field is added.
-- |
-- | **A helper polymorphic over the region must write the row open.** The
-- | region's cells have to be visible in the type for `Row.Cons` to find
-- | the one named, so a rigid `inits` will not do however many constraints
-- | are carried alongside it; `(count :: Int | rest)` will. `RowToList`
-- | and `SoleCell` then have nothing to reduce and are simply propagated,
-- | the caller discharging them where the row is closed.
-- |
-- | ```purs
-- | bump
-- |   :: forall s rest initsL r
-- |    . RowToList (count :: Int | rest) initsL
-- |   => SoleCell initsL "count"
-- |   => Region s (count :: Int | rest)
-- |   -> Hoop ("%hoop.var" :: Local s (count :: Int | rest) | r) Unit
-- | bump c = do
-- |   n <- read @"count" c
-- |   assign @"count" c (n + 1)
-- | ```
read
  :: forall @l s inits initsL a rest r
   . RowToList inits initsL
  => SoleCell initsL l
  => Row.Cons l a rest inits
  => IsSymbol l
  => Region s inits
  -> Hoop ("%hoop.var" :: Local s inits | r) a
read _ = readCellImpl (reflectSymbol (Proxy :: _ l))

-- | Write a cell of the open region, and evaluate to the value written.
-- |
-- | Nothing is mutated: the machine rebuilds the stack down to the cell's
-- | frame, so a continuation captured before the write still sees the
-- | value it was captured with.
-- |
-- | The result is the machine's own -- the `WriteP` rule steps to `Var x`
-- | -- so this costs exactly one node. Use `assign` (or `:=`) in statement
-- | position, where the extra node buys the `Unit`.
-- |
-- | The label may be omitted on the same terms as `read`'s.
write
  :: forall @l s inits initsL a rest r
   . RowToList inits initsL
  => SoleCell initsL l
  => Row.Cons l a rest inits
  => IsSymbol l
  => Region s inits
  -> a
  -> Hoop ("%hoop.var" :: Local s inits | r) a
write _ x = runFn2 writeCellImpl (reflectSymbol (Proxy :: _ l)) x

-- | `write`, with the written value discarded -- the shape a `set`-like
-- | operation wants. Costs the one node `write` saves.
-- |
-- | With the label inferred this is an ordinary binary function, which is
-- | what lets it carry the `:=` operator: an operator takes no type
-- | application, so `c := n` works exactly where `read c` does.
assign
  :: forall @l s inits initsL a rest r
   . RowToList inits initsL
  => SoleCell initsL l
  => Row.Cons l a rest inits
  => IsSymbol l
  => Region s inits
  -> a
  -> Hoop ("%hoop.var" :: Local s inits | r) Unit
assign c x = runFn2 bindImpl (write @l c x) \_ -> pureImpl unit

infix 4 assign as :=

-- | The label a `read` or `write` means when none was given.
-- |
-- | A one-cell region names it; any other region leaves it to the type
-- | application, which is what the fall-through instance is for -- it
-- | determines nothing and so lets the caller's label stand.
class SoleCell :: RowList Type -> Symbol -> Constraint
class SoleCell initsL l | initsL -> l

instance soleCellOne :: SoleCell (RL.Cons l a RL.Nil) l
else instance soleCellMany :: SoleCell initsL l

-- | Normalise a region's declaration and install its cells.
-- |
-- | A record declares one cell per field; anything else declares a single
-- | cell under a reserved label the surface never shows, which is what
-- | lets `var 0` skip inventing a field name. `Scalar` forces the second
-- | reading for a value that is itself a record.
-- |
-- | The mapping mentions no region: `init -> inits` is settled entirely
-- | outside `var`'s rank-2 `forall`, and the region variable is attached
-- | afterwards, by `Region s inits` and the row token.
class VarInit :: Type -> Row Type -> Constraint
class VarInit init inits | init -> inits where
  -- The two rows are unrelated on purpose: this is the row discharge, the
  -- surface counterpart of pushing the cells' frames onto the stack.
  installCells :: forall inner outer o. init -> Hoop inner o -> Hoop outer o

instance varInitRecord ::
  ( RowToList inits initsL
  , InstallCells initsL
  ) =>
  VarInit (Record inits) inits where
  installCells = installCellsList @initsL

else instance varInitScalarWrapped ::
  VarInit (Scalar a) ("%hoop.scalar" :: a) where
  installCells (Scalar x) body = runFn3 newCellImpl scalarLabel x body

else instance varInitScalar ::
  VarInit a ("%hoop.scalar" :: a) where
  installCells x body = runFn3 newCellImpl scalarLabel x body

-- The label the one cell of a non-record region lives under. Reserved, and
-- never shown: `read` and `write` recover it from `SoleCell`.
scalarLabel :: String
scalarLabel = "%hoop.scalar"

-- | Wrap a computation in the `NewP` nodes that install a record region's
-- | cells, driven by the `RowList` of its initial values.
class InstallCells :: RowList Type -> Constraint
class InstallCells initsL where
  installCellsList :: forall inits inner outer o. Record inits -> Hoop inner o -> Hoop outer o

instance installCellsNil :: InstallCells RL.Nil where
  installCellsList _ = unsafeCoerce

instance installCellsCons ::
  ( InstallCells tail
  , IsSymbol l
  ) =>
  InstallCells (RL.Cons l a tail) where
  installCellsList inits body =
    runFn3 newCellImpl l (RU.unsafeGet l inits) (installCellsList @tail inits body)
    where
    l = reflectSymbol (Proxy :: _ l)