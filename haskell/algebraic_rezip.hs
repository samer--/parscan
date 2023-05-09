{-# LANGUAGE DataKinds, TypeFamilies, RankNTypes, UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses, QuantifiedConstraints, UndecidableInstances #-}
module Algebraic where

{- BROKEN - This module is very broken -}

import Control.Arrow (first, second)
import Data.Kind
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Classes

import Common hiding (unzipWith)

type Unary = Type → Type

class Rezippable f where
   data U f s ∷ * → *
   -- type UC f ∷ * → Constraint
   -- unzipInto ∷ (∀ s. UC f s => (U f s a, U f s b) → r) → f (a,b) → r
   unzipInto ∷ (∀ s. (U f s a, U f s b) → r) → f (a,b) → r
   rezip ∷ (U f s a, U f s b) → f (a,b)
   -- rezip ∷ (U f s a, U f s b) → U f s (a,b) -- this is not good for some reason
   -- project ∷ U f s a -> f a

newtype Flip h f g a = Flip (h g f a)
   deriving (Show, Show1, Functor, Applicative, Scannable)

instance Scannable Identity where
   scan (Identity x) = (mempty, x)

-- newtype Lift f s a = LF {lower ∷ a} deriving (Functor, Show)


instance Rezippable Identity where
   newtype U Identity s a = UId {unUId::a} deriving (Functor, Show)
   -- type UC Identity = Functor1 Lift
   rezip = Identity . (unUId ⊗ unUId)
   unzipInto f = f . (UId ⊗ UId) . runIdentity

-- instance (Rezippable f, Rezippable g) ⇒ Rezippable (Compose f g) where
--    type U (Compose f g) = Compose (U f) (U g)
--    unzipWith f = (Compose ⊗ Compose) . unzipWith (unzipWith f) . getCompose
--    rezipWith f = Compose . rezipWith (rezipWith f) . (getCompose ⊗ getCompose)

-- instance (Rezippable f, Scannable f, Scannable g) ⇒ Scannable (Compose f g) where
--   -- scan = first (Compose . rezipWith mapAdd) . assocl . second scan . unzipWith scan . getCompose
--   scan = first (Compose . fmap mapAdd)
--          . unzipInto (first rezip . assocl . second scan)
--          . fmap scan . getCompose

(pair, unpair) = (uncurry Pair, \(Pair x y) → (x,y))

type family Fst a ∷ *
type family Snd a ∷ *

type instance Fst (s₁, s₂) = s₁
type instance Snd (s₁, s₂) = s₂

-- Very broken
-- instance (Rezippable f, Rezippable g) ⇒ Rezippable (Product f g) where
--    newtype U (Product f g) s a = UProd {unProd :: Product (U f (Fst s)) (U g (Snd s)) a}
--    rezip = pair . (rezip ⊗ rezip) . transp . (unpair . unProd ⊗ unpair . unProd)
--    -- unzipInto = _ -- (pair ⊗ pair) . transp . (unzipWith f ⊗ unzipWith f) . unpair
--    unzipInto k (Pair x y) = (`unzipInto` x) (\(x₁,x₂) →
--                             (`unzipInto` y) (\(y₁,y₂) →
--                             k (UProd (Pair x₁ y₁), UProd (Pair x₂ y₂))))

instance (Scannable f, Scannable g) ⇒ Scannable (Product f g) where
   scan (Pair x y) = first joinSubscans . assocl . second scan2 . transp . (scan ⊗ scan) $ (x,y)
      where scan2 (x , y) = ((mempty , x) , x <> y)
            joinSubscans = uncurry Pair . (mapAdd ⊗ mapAdd) .transp

instance (Scannable f, Scannable g) ⇒ Scannable (Sum f g) where
  scan (InL x) = first InL . scan $ x
  scan (InR y) = first InR . scan $ y

{- Now define some tree structures as type families
   These families (each with two clauses) are faintly reminiscent of the
   GADTs used to define the tree datatypes in the other modules, but they
   don't introduce any data constructors.
-}
type family TD (d ∷ Nat) ∷ Unary where
  TD 'Zero     = Identity
  TD ('Succ n) = Compose Pair (TD n)

type family BU (d ∷ Nat) ∷ Unary where
  BU 'Zero     = Identity
  BU ('Succ n) = Compose (BU n) Pair

type family Bush (d ∷ Nat) ∷ Unary where
  Bush 'Zero     = Pair
  Bush ('Succ n) = Compose (Bush n) (Bush n)

type family AltTD (d ∷ Nat) ∷ Unary where
  AltTD 'Zero     = Identity
  AltTD ('Succ n) = Product (AltTD n) (AltTD n)

type FatPair = Product Identity Identity

type family FatTD (d ∷ Nat) ∷ Unary where
  FatTD 'Zero     = Identity
  FatTD ('Succ n) = Compose FatPair (FatTD n)

type family FatBU (d ∷ Nat) ∷ Unary where
  FatBU 'Zero     = Identity
  FatBU ('Succ n) = Compose (FatBU n) FatPair
