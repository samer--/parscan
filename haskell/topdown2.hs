{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, DeriveTraversable #-}
module TopDown where

import Prelude hiding (zipWith)
import Control.Arrow (first, second)
import Common


data T (d :: Nat) a where
  L :: a -> T Zero a
  B :: Pair (T d a) -> T (Succ d) a

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

instance Scannable (T n) where
  scan (L x)  = (L mempty, x)
  scan (B ab) = (first (B . zipWith mapAdd) . assocl . second scan . unzipWith scan) ab
