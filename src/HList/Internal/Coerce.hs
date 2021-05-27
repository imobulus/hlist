{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
module HList.Internal.Coerce (
  module Data.Type.Equality,
  module HList.Internal.Coerce
) where

-- import Hasql.Combinators.HList
import Unsafe.Coerce (unsafeCoerce)
import Data.Data (Proxy(Proxy))
import Fcf (type (<=<), Exp, Eval, type (@@), Map)
import qualified GHC.TypeLits as TL
import Data.Type.Equality

coerceRefl :: forall a b. a -> a :~: b -> b
coerceRefl a Refl = a

mapRefl :: Proxy f -> a :~: b -> f a :~: f b
mapRefl Proxy Refl = Refl

mapFcfRefl :: forall k l (f :: k -> Exp l) (a :: k) (b :: k).
  Proxy f -> a :~: b -> (f @@ a) :~: (f @@ b)
mapFcfRefl Proxy Refl = Refl

symRefl :: a :~: b -> b :~: a
symRefl Refl = Refl

---- begin unsafeCoerce zone ----

type family HeadE (list :: [k]) :: k where
  HeadE (a ': _) = a
  HeadE '[] = TL.TypeError ('TL.Text "Attempt to take head of empty list")

type family TailE (list :: [k]) :: [k] where
  TailE (_ ': bs) = bs
  TailE '[] = TL.TypeError ('TL.Text "Attempt to take head of empty list")

mapFishLaw :: forall k l m (list :: [k]) (f :: l -> Exp m) (g :: k -> Exp l).
  Proxy f -> Proxy g -> Proxy list ->
  Eval (Map (f <=< g) list) :~: Eval (Map f (Eval (Map g list)))
mapFishLaw _ _ _ = unsafeCoerce Refl

mapEmptyLaw :: forall k l (list :: [k]) (f :: k -> Exp l).
  Eval (Map f list) ~ '[] =>
  Proxy f -> Proxy list -> '[] :~: list
mapEmptyLaw _ _ = unsafeCoerce Refl

mapHeadLaw :: forall k l a bs (list :: [k]) (f :: k -> Exp l).
  Eval (Map f list) ~ (a ': bs) =>
  Proxy f -> Proxy list -> a :~: (f @@ HeadE list)
mapHeadLaw _ _ = unsafeCoerce Refl

mapTailLaw :: forall k l a bs (list :: [k]) (f :: k -> Exp l).
  Map f @@ list ~ (a ': bs) =>
  Proxy f -> Proxy list -> bs :~: (Map f @@ TailE list)
mapTailLaw _ _ = unsafeCoerce Refl

mapNonemptyLaw :: forall k l a bs (list :: [k]) (f :: k -> Exp l).
  Map f @@ list ~ (a ': bs) =>
  Proxy f -> Proxy list -> (HeadE list ': TailE list) :~: list
mapNonemptyLaw _ _ = unsafeCoerce Refl

---- end unsafeCoerce zone ----
