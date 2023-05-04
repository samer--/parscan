{-# LANGUAGE GADTs, DataKinds, TypeFamilies, QuantifiedConstraints, UndecidableInstances #-}
module AlgebraicGADT where

import Control.Arrow (first, second)
import Data.Kind
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Classes

import Common
import Algebraic

-- GADT for a tree with a generalised branch functor.

data FT (b :: Unary -> Unary) (n :: Nat) (a :: *) where
  L :: a -> FT b 'Zero a
  B :: b (FT b n) a -> FT b ('Succ n) a

-- deriving instance (Show a,
--                    forall f. Functor f => Functor (b f),
--                    forall f. Functor f => Show (b f a))
--                   => Show (FT b n a)
-- deriving instance (forall f. Functor f => Functor (b f),
--                    forall f. Functor f => Show1 (b f),
--                    Show1 (FT b n))
--                   => Show1 (FT b ('Succ n))
-- FAIL

deriving instance (forall f.Functor f => Functor (b f)) => Functor (FT b n)

-- By some minor miracle, this system of instances seems to work.

instance (Show a, Show1 (FT b n)) => Show (FT b n a) where showsPrec = showsPrec1
instance Show1 (FT b 'Zero) where
  liftShowsPrec shp _ _ (L x) = showsUnaryWith shp "L" 10 x
instance Show1 (b (FT b n)) => Show1 (FT b ('Succ n)) where
  liftShowsPrec shp shl _ (B y) = showsUnaryWith (liftShowsPrec shp shl) "B" 10 y

instance Functor (FT b 'Zero) => Applicative (FT b 'Zero) where
  pure = L
  L f <*> L x = L (f x)
instance ( (forall f.Functor f => Functor (b f))
         , Applicative (b (FT b n))
         ) => Applicative (FT b ('Succ n)) where
  pure x = B (pure x)
  B fb <*> B xb = B (fb <*> xb)

-- cheaty Zippable instance
instance (Functor (FT b n), Applicative (FT b n)) => Zippable (FT b n) where
  fzipWith   = zipWithA
  unzipWith = unzipWithF

-- Now for Scannable instance
instance Functor (FT b 'Zero) => Scannable (FT b 'Zero) where
  scan (L x) = (L mempty, x)
instance (Functor (FT b ('Succ n)), Scannable (b (FT b n))) => Scannable (FT b ('Succ n)) where
  scan (B y) = first B (scan y)

{- Try:
 iota :: FT (Compose Pair) Three Int
 iota :: FT (Flip Compose Pair) Three Int

 -}
