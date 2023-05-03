{-# LANGUAGE GADTs, DataKinds #-}
module Simple where

import qualified Data.Traversable
import Common

----------------------------------------------
-- Simple version, depth indexed

data T d a where
  L :: a -> T Zero a
  B :: T d a -> T d a -> T (Succ d) a

deriving instance Functor (T d)
deriving instance Show a => Show (T d a)

instance Foldable (T n) where
  foldMap f (L x) = f x
  foldMap f (B l r) = foldMap f l <> foldMap f r

instance Traversable (T n) where
  sequenceA (L a) = L <$> a
  sequenceA (B l r) = B <$> sequenceA l <*> sequenceA r

instance Applicative (T Zero) where
  pure = L
  L f <*> L x = L (f x)

instance Applicative (T n) => Applicative (T (Succ n)) where
  pure x = B (pure x) (pure x)
  B f1 f2 <*> B x1 x2 = B (f1 <*> x1) (f2 <*> x2)

constTreeOfDepth :: forall n a. (INat n -> a -> T n a)
constTreeOfDepth Z x = pure x
constTreeOfDepth (S n) x = B (constTreeOfDepth n x) (constTreeOfDepth n x)

-- scanT :: Monoid a => T d a -> (T d a, a)
instance Scannable (T d) where
  scan (L x) = (L mempty, x)
  scan (B a b) = (B a' (fmap (asum <>) b'), asum <> bsum) where
    (a', asum) = scan a
    (b', bsum) = scan b
