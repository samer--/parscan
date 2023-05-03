{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving #-}
module TopDown where

import qualified Data.Traversable
import Control.Arrow (first, second)
import Common


{- In this version, I tried defining the Applicative instance for T n in one
 - go, relying on constTreeOfDepth to implement pure. This seemed to demand the
 - us of toINat from the IsNat class in order to supply a value level natural
 - number so we can pattern match on the depth to build the tree. This in turn
 - demanded (on GHC's advice) to introduce the IsNat class constraint on the
 - Applicative instance. This in turn demanded the IsNat constraint on the B
 - constructor of the tree. So there you go. See topdown2 for an alternative
 - approach which defines the Applicative instance inductively using two clauses.
 -}

data T d a where
  L :: a -> T Zero a
  B :: IsNat d => Pair (T d a) -> T (Succ d) a

deriving instance Functor (T d)
deriving instance Show a => Show (T d a)

instance Foldable (T n) where
  foldMap = Data.Traversable.foldMapDefault -- traverses with Monoid m => Const m applicative

instance Traversable (T n) where
  sequenceA (L a) = L <$> a
  sequenceA (B (l:#r)) = B <$> ((:#) <$> sequenceA l <*> sequenceA r)

constTreeOfDepth :: INat n -> a -> T n a
constTreeOfDepth Z = L
constTreeOfDepth (S n) = B . pure . constTreeOfDepth n

instance IsNat n => Applicative (T n) where
  pure = constTreeOfDepth (toINat :: INat n)
  L f <*> L x = L (f x)
  B (f1:#f2) <*> B (x1:#x2) = B (f1 <*> x1 :# f2 <*> x2)

instance Scannable (T n) where
  scan (L x) = (L mempty, x)
  scan (B ab) = (first (B . zipWithP mapAdd) . assocl . second scanP . unzipWithP scan) ab
