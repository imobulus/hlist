{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Data.HList.Fcf (
  module Data.HList.Fcf,
  module Fcf
) where

import Fcf
import Data.Kind
import Fcf.Class.Monoid (type (<>))


type family Curry (list :: [Type]) a :: Type where
  Curry '[] a = a
  Curry (b ': cs) a = b -> Curry cs a

type family ConcatAll (list :: [[k]]) :: [k] where
  ConcatAll '[] = '[]
  ConcatAll (a ': as) = a <> ConcatAll as

data MapPure :: (k -> l) -> [k] -> Exp [l]
type instance Eval (MapPure f list) = Eval (Map (Pure1 f) list)

data CollectConstraints :: [Constraint] -> Exp Constraint
type instance Eval (CollectConstraints '[]) = ()
type instance Eval (CollectConstraints (a ': bs)) = (a, Eval (CollectConstraints bs))

data All :: (k -> Exp Constraint) -> [k] -> Exp Constraint
type instance Eval (All c list) = Eval (CollectConstraints =<< Map c list)

data AllPure :: (k -> Constraint) -> [k] -> Exp Constraint
type instance Eval (AllPure c list) = Eval (All (Pure1 c) list)

data Equal :: k -> k -> Exp Constraint
type instance Eval (Equal a b) = a ~ b
