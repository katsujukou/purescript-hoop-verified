module Hoop.TypeUtil where

import Prim.Boolean (False, True)
import Prim.Int as Int
import Prim.RowList (RowList)
import Prim.RowList as RL
import Prim.TypeError (Above, Beside)

infixl 6 type Beside as ++
infixl 5 type Above as |>

data List :: forall k. k -> Type
data List k

foreign import data Nil :: forall k. List k
foreign import data Cons :: forall k. k -> List k -> List k

infixr 6 type Cons as :

class NonEmpty :: forall k. List k -> Constraint
class NonEmpty xs

instance NonEmpty (Cons x xs)

-- The standard type-equality trick: the fundeps improve either side to
-- the other at the use site, and `proof` converts under any context.
class TypeEquals :: forall k. k -> k -> Constraint
class TypeEquals a b | a -> b, b -> a where
  proof :: forall p. p a -> p b

instance TypeEquals a a where
  proof = \x -> x

class HasLabel :: forall k. RowList k -> Symbol -> Boolean -> Constraint
class HasLabel rl l b | rl l -> b

instance HasLabel RL.Nil l False
else instance HasLabel (RL.Cons l t rest) l True
else instance (HasLabel rest l b) => HasLabel (RL.Cons l' t rest) l b

class RowListLength :: forall k. RowList k -> Int -> Constraint
class RowListLength l n | l -> n

instance RowListLength RL.Nil 0
instance
  ( RowListLength tl m
  , Int.Add m 1 n
  ) =>
  RowListLength (RL.Cons _1 _2 tl) n
