{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.HList.Tuples where

import Fcf
import Data.Kind (Type)
import Data.HList.HList

type family NestedTupleForm (list :: [Type]) :: Type where
  NestedTupleForm '[] = ()
  NestedTupleForm (a ': bs) = (a, NestedTupleForm bs)

nestedTupleForm :: HList list -> NestedTupleForm list
nestedTupleForm HEmpty = ()
nestedTupleForm (a :|| bs) = (a, nestedTupleForm bs) 


