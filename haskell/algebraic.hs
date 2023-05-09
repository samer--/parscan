{-# LANGUAGE DataKinds, TypeFamilies, RankNTypes, UnicodeSyntax #-}
module Algebraic where

import Control.Arrow (first, second)
import Data.Kind
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Classes

import Common


type Unary = Type → Type
newtype Flip h f g a = Flip (h g f a) deriving (Show, Show1, Functor, Applicative, Zippable, Scannable)

instance Scannable Identity where
  scan (Identity x) = (mempty, x)

instance Zippable Identity where
  fzipWith f (Identity x, Identity y) = Identity (f (x,y))
  unzipWith f = (Identity ⊗ Identity) . f . runIdentity

instance (Zippable f, Zippable g) ⇒ Zippable (Compose f g) where
   unzipWith f = (Compose ⊗ Compose) . unzipWith (unzipWith f) . getCompose
   fzipWith   f = Compose . fzipWith (fzipWith f) . (getCompose ⊗ getCompose)

instance (Zippable f, Scannable f, Scannable g) ⇒ Scannable (Compose f g) where
  scan = first (Compose . fzipWith mapAdd) . assocl . second scan . unzipWith scan . getCompose

(pair, unpair) = (uncurry Pair, \(Pair x y) → (x,y))

instance (Zippable f, Zippable g) ⇒ Zippable (Product f g) where
  unzipWith f = (pair ⊗ pair) . transp . (unzipWith f ⊗ unzipWith f) . unpair
  fzipWith f   = pair . (fzipWith f ⊗ fzipWith f) . transp . (unpair ⊗ unpair)

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

-- Can this work??
type family GeneralT (h ∷ Unary → Unary) (d ∷ Nat) ∷ Unary
type instance GeneralT _ 'Zero = Identity
type instance GeneralT h ('Succ n) = h (GeneralT h n)

{- Yes! Try:
  iota :: GeneralT (Compose Pair) Three
  iota :: GeneralT (Flip Compose Pair) Three
-}
