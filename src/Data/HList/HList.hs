{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
-- |
-- Module:      Data.HList
-- Copyright:   (c) 2021 Egor Riabov
-- License:     BSD3
-- Maintainer:  Egor Riabov <imobulus@yandex.ru>
-- Stability:   experimental
-- Portability: portable
--
-- Package for working with heterogenous lists, which are basically tuples on steroids.
module Data.HList.HList (
  -- * What?
  -- $what

  -- ** Why?
  -- $why

  -- ** How?
  -- $how
  module Data.HList.HList
) where

import Data.Kind
import qualified Data.HList.Fcf as Fcf
import Data.HList.Fcf
import Fcf.Class.Monoid (type (<>))
import Data.Proxy (Proxy(Proxy))
import Data.HList.Internal.Coerce
import qualified Fcf.Data.List as Fcl

infixr :||

-- | The type of heterogenous lists. Can be constructed straightforwardly
-- 
-- @
--   myHList :: HList '[Int, Int, Char]
--   myHList = 2 :|| 3 :|| \'c\' :|| HEmpty
-- @
--
-- or using 'fromTuple' from "Data.HList.TH" module:
--
-- @
--   >>> $(fromTuple 3) (\'a\', "bc", 4)
--   >>> \'a\' :|| "bc" :|| 4 :|| HEmpty
-- @
data HList :: [Type] -> Type where
  (:||) :: a -> HList bs -> HList (a ': bs)
  HEmpty :: HList '[]

instance AllPure Show @@ types => Show (HList types) where
  show HEmpty = "HEmpty"
  show (a :|| as) = show a <> " :|| " <> show as

-- | Length function for 'HList'. Can be derived from the type using 'natVal'.
hLength :: HList a -> Int
hLength HEmpty = 0
hLength (a :|| bs) = 1 + hLength bs

hetUncurry :: Curry list a -> HList list -> a
hetUncurry a HEmpty = a
hetUncurry f (b :|| cs) = hetUncurry (f b) cs

hetFoldr :: (forall a lst. a -> f (HList lst) -> f (HList (a ': lst))) -> f (HList '[]) -> HList list -> f (HList list)
hetFoldr _ a HEmpty = a
hetFoldr f initial (a :|| bs) = f a (hetFoldr f initial bs)

infixr ++|

(++|) :: HList list1 -> HList list2 -> HList (list1 <> list2)
(++|) HEmpty a = a
(++|) (a :|| bs) c = a :|| (bs ++| c)

hetConcat :: forall (list :: [[Type]]).
  Proxy list ->
  HList (Map (Pure1 HList) @@ list) -> HList (Fcl.Concat @@ list)
hetConcat _ HEmpty = case mapEmptyLaw (Proxy @'(Pure1 HList, list)) of
  Refl -> HEmpty
hetConcat _ (a :|| bs) = case (
  mapHeadLaw (Proxy @'(Pure1 HList, list)),
  mapTailLaw (Proxy @'(Pure1 HList, list)),
  mapNonemptyLaw (Proxy @'(Pure1 HList, list)) :: (HeadE list : TailE list) :~: list
  ) of
  (Refl, Refl, Refl) -> a ++| hetConcat (Proxy @(TailE list)) bs

toList :: forall (a :: Type) (list :: [Type]).
  All (Equal a) @@ list =>
  HList list -> [a]
toList HEmpty = []
toList (a :|| bs) = a : toList bs

hetMapToList :: forall k (f :: k -> Exp Type) (g :: Type) (c :: k -> Exp Constraint) (list :: [k]).
  Eval (Fcf.All c list) =>
  Proxy '(f, g, c, list) ->
  (forall a. c @@ a => Proxy a -> f @@ a -> g) ->
  HList (Map f @@ list) -> [g]
hetMapToList _ _ HEmpty = []
hetMapToList _ f (a :|| bs) = case (
  mapHeadLaw (Proxy @'(f, list)),
  mapRefl (Proxy @HList) $ mapTailLaw (Proxy @'(f, list)),
  mapRefl (Proxy @(Fcf.All c)) $ mapNonemptyLaw (Proxy @'(f, list))
  ) of
  (Refl, Refl, Refl) -> f (Proxy @(HeadE list)) a : hetMapToList (Proxy @'(f, g, c, TailE list)) f bs

hetMap :: forall (f :: Type -> Exp Type) (c :: Type -> Exp Constraint) (list :: [Type]).
  Eval (Fcf.All c list) =>
  Proxy '(f, c) ->
  (forall a. c @@ a => a -> f @@ a) ->
  HList list ->
    HList (Eval (Map f list))
hetMap _ _ HEmpty = HEmpty
hetMap proxy f (a :|| bs) = f a :|| hetMap proxy f bs

-- | Maps a function over a heterogenous list with environment @f@
hetMapEnv :: forall k (f :: k -> Exp Type) (g :: k -> Exp Type) (c :: k -> Exp Constraint) (list :: [k]).
  Eval (Fcf.All c list) =>
  Proxy '(f, g, c, list) ->
  (forall a. c @@ a => Proxy a -> f @@ a -> g @@ a) ->
  HList (Map f @@ list) ->
    HList (Map g @@ list)

hetMapEnv _ _ HEmpty = case
  mapRefl (Proxy @HList) $
  mapFcfRefl (Proxy @(Map g)) $
  mapEmptyLaw (Proxy @'(f, list)) of
  Refl -> HEmpty

hetMapEnv _ f ((a :: a) :|| (bs :: HList bs)) = case (
  mapHeadLaw (Proxy @'(f, list)),
  mapRefl (Proxy @HList) $ mapTailLaw (Proxy @'(f, list)),
  mapRefl (Proxy @(Fcf.All c)) $ mapNonemptyLaw (Proxy @'(f, list))
  ) of
  (Refl, Refl, Refl) -> f (Proxy @(HeadE list)) a :|| hetMapEnv (Proxy @'(f, g, c, TailE list)) f bs


hetSequence :: forall (m :: Type -> Type) (list :: [Type]). Monad m => HList (Eval (MapPure m list)) -> m (HList list)

hetSequence HEmpty = case mapRefl (Proxy @HList) $ mapEmptyLaw (Proxy @'(Pure1 m, list)) of
  Refl -> return HEmpty

hetSequence ((a :: a) :|| (bs :: HList bs)) = case (
  mapHeadLaw (Proxy @'(Pure1 m, list))
    :: a :~: m (HeadE list),
  mapRefl (Proxy @HList) $ mapTailLaw (Proxy @'(Pure1 m, list))
    :: HList bs :~: HList (Map (Pure1 m) @@ TailE list),
  mapRefl (Proxy @HList) $ mapNonemptyLaw (Proxy @'(Pure1 m, list))
    :: HList (HeadE list ': TailE list) :~: HList list
  ) of
  (Refl, Refl, Refl) -> do
    a_ref <- a
    bs_ref <- hetSequence bs
    return (a_ref :|| bs_ref)

-- $what
--
-- Heterogenous list (or 'HList') is a list of values, whose types are annotated
-- on type-level using promoted lists from @{-\# LANGUAGE DataKinds \#-}@, but with
-- ordinary list-like structure.
--
-- > myHList :: HList '[Int, Char, Bool]
-- > myHList = 2 :|| 'f' :|| True :|| HEmpty

-- $why
--
-- HList's can be useful in code where arbitrary tuples are involved, such as
-- Nikita Volkov's <https://hackage.haskell.org/package/hasql HaSql> library.
-- Unlike tuples, HList's are more generic, thus allow writing functions on
-- them, similar to 'Prelude.concat' and 'Prelude.map' for ordinary Lists.
--
-- $how
--
-- The library relies on <https://hackage.haskell.org/package/first-class-families first-class-families>
-- package to perform nontrivial operations with typelevel lists. 