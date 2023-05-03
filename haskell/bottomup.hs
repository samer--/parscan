{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, DeriveTraversable, UndecidableInstances #-}
module BottomUp where

import Prelude hiding (zipWith)
import Control.Arrow (first, second)
import Control.Applicative
import qualified Data.Traversable
import Common


data T (d :: Nat) a where
  L :: a -> T Zero a
  B :: T d (Pair a) -> T (Succ d) a

deriving instance Show a => Show (T d a)
deriving instance Functor (T d)
deriving instance Foldable (T d)
deriving instance Traversable (T d)

instance Applicative (T Zero) where
  pure = L
  L f <*> L x = L (f x)

instance Applicative (T n) => Applicative (T (Succ n)) where
  pure = B . pure . pure
  B fp <*> B xp = B ((<*>) <$> fp <*> xp)

instance Zippable (T n) where
  zipWith f (L x, L y) = L (f (x,y))
  zipWith f (B a, B b) = B (zipWith (zipWith f) (a, b))
  unzipWith f (L x) = (L ⊗ L) (f x)
  unzipWith f (B t) = (B ⊗ B) (unzipWith (unzipWith f) t)

instance Zippable (T n) => Scannable (T n) where
  scan (L x) = (L mempty, x)
  scan (B t) = (first (B . zipWith mapAdd) . assocl . second scan . unzipWith scan) t
