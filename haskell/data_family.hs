{-# LANGUAGE GADTs, DataKinds, TypeFamilies, QuantifiedConstraints, UndecidableInstances #-}
module DataFamily where

import Prelude hiding (zipWith)
import Control.Arrow (first, second)
import Data.Kind
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Classes

import Common
import Algebraic


data family TDD (d :: Nat) :: (Type -> Type)
newtype instance TDD Zero a = Id a deriving (Show, Functor)
newtype instance TDD (Succ n) a = Comp (Compose Pair (TDD n) a)

deriving instance Show1 (TDD n) => Show1 (TDD (Succ n)) -- not supposed to work!
deriving instance (Show a, Show1 (TDD n), Show (TDD n a)) => Show (TDD (Succ n) a)
deriving instance Functor (TDD n) => Functor (TDD (Succ n))

instance Show1 (TDD Zero) where
  liftShowsPrec showsPrec showsList n (Id x) = showsPrec n x

instance Applicative (TDD Zero) where
  pure = Id
  Id f <*> Id x = Id (f x)
instance Applicative (TDD n) => Applicative (TDD (Succ n)) where
  pure = Comp . pure
  Comp f <*> Comp x = Comp (f <*> x)

instance Scannable (TDD Zero) where
  scan (Id x) = (Id mempty, x)
instance Scannable (TDD n) => Scannable (TDD (Succ n)) where
  scan (Comp c) = first Comp (scan c)

{-
  Phew - that was a bit work... But it works:
  scan $ pure @(TDD (Succ (Succ (Succ Zero)))) (1::Int)
  It's turns out to be very similar to the version in topdown2.hs, except
  that here we are relying on the Compose to handle the Applicative instance
  and to provide the implementation of scan.
  I can't be bothered to repeat for bottom up tree - it will require
  Zippable instances too.
-}
