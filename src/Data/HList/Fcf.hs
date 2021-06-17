{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Data.HList.Fcf (
  module Fcf,
  module Data.HList.Fcf
) where

import Fcf
import Data.Kind
import Fcf.Class.Monoid (type (<>))

-- | @Curry list a@ returns type of curried functions, which take arguments
-- of types from @list@ and return a value of type @a@.
--
-- @
--   add :: Curry '[Int, Int] String
--   add m n = show $ m + n
--   >>> :type add
--   >>> Int -> Int -> String
-- @
type family Curry (list :: [Type]) a :: Type where
  Curry '[] a = a
  Curry (b ': cs) a = b -> Curry cs a

-- | Shorthand to map pure functions via fcf.
data MapPure :: (k -> l) -> [k] -> Exp [l]
type instance Eval (MapPure f list) = Eval (Map (Pure1 f) list)

-- | Collects a list of constraints to one.
data CollectConstraints :: [Constraint] -> Exp Constraint
type instance Eval (CollectConstraints '[]) = ()
type instance Eval (CollectConstraints (a ': bs)) = (a, Eval (CollectConstraints bs))

-- | @'All' c list@ constrains all elements of the @list@ to satisfy constraint @c@.
data All :: (k -> Exp Constraint) -> [k] -> Exp Constraint
type instance Eval (All c list) = Eval (CollectConstraints =<< Map c list)

-- | Shorthand for 'All' for using with pure constraints.
data AllPure :: (k -> Constraint) -> [k] -> Exp Constraint
type instance Eval (AllPure c list) = Eval (All (Pure1 c) list)

-- | Fcf for @~@.
data Equal :: k -> k -> Exp Constraint
type instance Eval (Equal a b) = a ~ b
