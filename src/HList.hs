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
module HList where

import Data.Kind
import qualified HList.Fcf as Fcf
import  HList.Fcf
import Data.Proxy (Proxy(Proxy))
import HList.Internal.Coerce
import qualified Fcf.Data.List as Fcl
import Fcf.Class.Monoid (type (<>))

-- HLIST

infixr :|

data HList :: [Type] -> Type where
  (:|) :: a -> HList bs -> HList (a ': bs)
  HEmpty :: HList '[]

instance AllPure Show @@ types => Show (HList types) where
  show HEmpty = "HEmpty"
  show (a :| as) = show a <> " :| " <> show as

hetUncurry :: Curry list a -> HList list -> a
hetUncurry a HEmpty = a
hetUncurry f (b :| cs) = hetUncurry (f b) cs

hetFoldr :: (forall a lst. a -> f (HList lst) -> f (HList (a ': lst))) -> f (HList '[]) -> HList list -> f (HList list)
hetFoldr _ a HEmpty = a
hetFoldr f initial (a :| bs) = f a (hetFoldr f initial bs)

infixr ++|

(++|) :: HList list1 -> HList list2 -> HList (list1 <> list2)
(++|) HEmpty a = a
(++|) (a :| bs) c = a :| (bs ++| c)

hetConcat :: forall (list :: [[Type]]).
  Proxy list ->
  HList (Map (Pure1 HList) @@ list) -> HList (Fcl.Concat @@ list)
hetConcat _ HEmpty = case mapEmptyLaw (Proxy @(Pure1 HList)) (Proxy @list) of
  Refl -> HEmpty
hetConcat _ (a :| bs) = case mapHeadLaw (Proxy @(Pure1 HList)) (Proxy @list) of
  Refl -> case mapTailLaw (Proxy @(Pure1 HList)) (Proxy @list) of
    Refl -> case mapNonemptyLaw (Proxy @(Pure1 HList)) (Proxy @list) :: (HeadE list : TailE list) :~: list of
      Refl -> a ++| hetConcat (Proxy @(TailE list)) bs

testList :: HList '[HList '[Int, Int], HList '[Char]]
testList = (1 :| 2 :| HEmpty) :| ('a' :| HEmpty) :| HEmpty

testListConcat :: HList '[Int, Int, Char]
testListConcat = hetConcat (Proxy @'[ '[Int, Int], '[Char] ]) testList

-- >>> testListConcat
-- 1 :| 2 :| 'a' :| HEmpty

toList :: forall (a :: Type) (list :: [Type]).
  All (Equal a) @@ list =>
  HList list -> [a]
toList HEmpty = []
toList (a :| bs) = a : toList bs

hetMapToList :: forall k (f :: k -> Exp Type) (g :: Type) (c :: k -> Exp Constraint) (list :: [k]).
  Eval (Fcf.All c list) =>
  Proxy f -> Proxy g -> Proxy c -> Proxy list ->
  (forall a. c @@ a => Proxy a -> f @@ a -> g) ->
  HList (Map f @@ list) -> [g]
hetMapToList _ _ _ _ _ HEmpty = []
hetMapToList p q r Proxy f (a :| bs) = let
  aHead = coerceRefl a $ mapHeadLaw (Proxy @f) (Proxy @list)
  bsTail = coerceRefl bs $ mapRefl (Proxy @HList) $ mapTailLaw (Proxy @f) (Proxy @list)
  in case mapRefl (Proxy @(Fcf.All c)) $ mapNonemptyLaw (Proxy @f) (Proxy @list) of
    Refl -> f (Proxy @(HeadE list)) aHead : hetMapToList p q r (Proxy @(TailE list)) f bsTail

hetMap :: forall (f :: Type -> Exp Type) (c :: Type -> Exp Constraint) (list :: [Type]).
  Eval (Fcf.All c list) =>
  Proxy f -> Proxy c ->
  (forall a. c @@ a => a -> f @@ a) ->
  HList list ->
    HList (Eval (Map f list))
hetMap Proxy Proxy _ HEmpty = HEmpty
hetMap p q f (a :| bs) = f a :| hetMap p q f bs

-- | Maps a function over a heterogenous list with environment @f@
hetMapEnv :: forall k (f :: k -> Exp Type) (g :: k -> Exp Type) (c :: k -> Exp Constraint) (list :: [k]).
  Eval (Fcf.All c list) =>
  Proxy f -> Proxy g -> Proxy c -> Proxy list ->
  (forall a. c @@ a => Proxy a -> f @@ a -> g @@ a) ->
  HList (Map f @@ list) ->
    HList (Map g @@ list)

hetMapEnv Proxy Proxy Proxy Proxy _ HEmpty = coerceRefl HEmpty proofListIsEmpty
 where
  proofListIsEmpty = mapRefl (Proxy @HList) $ mapFcfRefl (Proxy @(Map g)) $ mapEmptyLaw (Proxy @f) (Proxy @list)

hetMapEnv p q r Proxy f ((a :: a) :| (bs :: HList bs)) = let
  aHead = coerceRefl a $ mapHeadLaw (Proxy @f) (Proxy @list)
  bsTail = coerceRefl bs $ mapRefl (Proxy @HList) $ mapTailLaw (Proxy @f) (Proxy @list)
  in case mapRefl (Proxy @(Fcf.All c)) $ mapNonemptyLaw (Proxy @f) (Proxy @list) of
    Refl -> f (Proxy @(HeadE list)) aHead :| hetMapEnv p q r (Proxy @(TailE list)) f bsTail


hetSequence :: forall (m :: Type -> Type) (list :: [Type]). Monad m => HList (Eval (MapPure m list)) -> m (HList list)

hetSequence HEmpty = return $ coerceRefl HEmpty proofListIsEmpty
 where
  proofListIsEmpty = mapRefl (Proxy @HList) $ mapEmptyLaw (Proxy @(Pure1 m)) (Proxy @list)

hetSequence ((a :: a) :| (bs :: HList bs)) = do
  a_ref <- aTyped
  bs_ref <- hetSequence bsTyped
  return $ coerceRefl (a_ref :| bs_ref) proofHeadTail
 where
  proofHead = mapHeadLaw (Proxy @(Pure1 m)) (Proxy @list)
    :: a :~: m (HeadE list)
  proofTail = mapRefl (Proxy @HList) $ mapTailLaw (Proxy @(Pure1 m)) (Proxy @list)
    :: HList bs :~: HList (Map (Pure1 m) @@ TailE list)
  proofHeadTail = mapRefl (Proxy @HList) $ mapNonemptyLaw (Proxy @(Pure1 m)) (Proxy @list)
    :: HList (HeadE list ': TailE list) :~: HList list
  aTyped = coerceRefl a proofHead
  bsTyped = coerceRefl bs proofTail
