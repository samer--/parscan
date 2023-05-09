{-# LANGUAGE StandaloneDeriving, GADTs, DataKinds, TypeFamilies #-}
{-# LANGUAGE RankNTypes, UndecidableInstances, UnicodeSyntax #-}
module Rezip where

{- Using the type system to ensure perfectly safe and invertible zip and unzip

 We start from the observation that Haskell's `zip` function is a bit 'loose' in the sense that
 permits zipping lists of different lengths. This means it can silently destroy information and
 is not the true inverse of `unzip`. It is true that `uncurry zip . unzip = id`, but
 `unzip . uncurry zip ≠ id`.

 The aim of this module is to explore how to use the type system to ensure 'safe', invertible
 zips, not just for lists, but as a type class that can support many data types. It boils down
 to ensuring that we can only zip two data structures of the same 'shape'. For lists, this means
 that the lists must be of the same length. With that as our driving example, we'll focus on approaches
 built around lists and type-level length indexed vectors.
 -}

import Common
import Data.Functor.Classes
import Data.Functor.Identity


-- Start with standard length length indexed vector type, using the data kind
-- Nat from the Common module.
data Vec (n :: Nat) a where
  VN :: Vec 'Zero a
  VC :: a -> Vec n a -> Vec ('Succ n) a

deriving instance Functor (Vec n)
deriving instance Foldable (Vec n)
deriving instance Traversable (Vec n)

-- deriving instance Show (Vec 'Zero a)
-- deriving instance (Show a, Show (Vec n a)) => Show (Vec ('Succ n) a)
-- instance Show1 (Vec 'Zero) where liftShowsPrec _ _ _ _ = showString "VN"
-- instance Show1 (Vec n) => Show1 (Vec ('Succ n)) where
instance Show1 (Vec n) where
  liftShowsPrec shp shl _ vec = showString "<" . shl (listOfVec vec) . showString ">"

instance (Show a, Show1 (Vec n)) => Show (Vec n a) where showsPrec = showsPrec1

-- now a safe zip function for Vec
zipVec :: (Vec n a, Vec n b) -> Vec n (a,b)
zipVec (VN, VN) = VN
zipVec (VC x xs, VC y ys) = VC (x,y) (zipVec (xs, ys))

-- projects the family of Vec types down to the list type
listOfVec :: forall n a. Vec n a -> [a]
listOfVec VN = []
listOfVec (VC x xs) = x : listOfVec xs

zipVecToList = listOfVec . zipVec

----- Vector pair as an existential data type encapsulating length constraint ---

data VecPair a b = forall (n :: Nat). VP (Vec n a) (Vec n b)
deriving instance (Show a, Show b) => Show (VecPair a b)

rezipVP :: VecPair a b -> [(a,b)]
rezipVP (VP xs ys) = listOfVec $ zipVec (xs, ys)

unzipList :: (Show a, Show b) => [(a,b)] -> VecPair a b
unzipList [] = VP VN VN
unzipList (xy : xys) = cons2 xy $ unzipList xys where
  cons2 (x,y) (VP xs ys) = VP (VC x xs) (VC y ys)

-- We need some functions to work with VecPair, so we can manipulate the first
-- and second vectors while maintaining the constraint that they are the same length.
fsndVP :: (forall n. Vec n b -> Vec n c) -> VecPair a b -> VecPair a c
fsndVP f (VP x y) = VP x (f y)

-- a lensish sort of thing, for what it's worth. The forall n seems to spoil it for
-- the Lens library though.
fstOfVP :: Functor f => (forall n. Vec n a -> f (Vec n c)) -> VecPair a b -> f (VecPair c b)
fstOfVP f (VP x y) = fmap (`VP` y) (f x)

sndOfVP :: Functor f => (forall n. Vec n b -> f (Vec n c)) -> VecPair a b -> f (VecPair a c)
sndOfVP f (VP x y) = fmap (x `VP`) (f y)

-- The standard Lens type is not able to handle the above lenses where the component type
-- includes an existential type index. This lens type seems to handle it ok.
type LensE g s t a b = forall f. Functor f => (forall i. g i a -> f (g i b)) -> s -> f t

-- Applies transformer function to focused thing while producing a by-product
-- Relies on Functor instance of (side,) to hold the by-product.
-- c: container, e: element, i: input, o: output.
splitL :: LensE g s t a b -> (forall i. g i a -> (side, g i b)) -> s -> (side, t)
splitL lens = lens

-- flipped version to suit scan better - by product on the RIGHT.
splitR :: LensE g s t a b -> (forall i. g i a -> (g i b, side)) -> s -> (t, side)
splitR lens f = swap . lens (swap . f)

-- view' ∷ Lens c c' e e' → c → e
over :: LensE g s t a b -> (forall i. g i a -> g i b) -> s -> t
over lens f = runIdentity . lens (Identity . f)

-- maybe this can work, but I don't love introducing the new VecPair data type
-- and thus having to introduce modifier functions or lenses to handle it.
-- Let's try another way.

--------------------------- Continuation passign style ---------------------------

-- The idea here is to use a sufficiently polymorphic 'continuation' function to
-- handle the unzipped pair of vectors. Within this function, the length of the two
-- vectors is visible in there types, but this information is not allowed to leak
-- out of the function. Thus, instead of using an existentially data type to hide
-- the length information, we use a universally quantified function type. Within
-- the function, the two unzipped halves are a bit like an 'entangled' pair in Quantum
-- mechanics - they can be manipulated independently using ordinary Vec handling
-- functions, but their lengths a constrained to be equal, we so we can safely
-- call zipVec if we want to.
unzipK :: [(a,b)] -> (forall n. (Vec n a, Vec n b) -> r) -> r
unzipK [] k = k (VN, VN)
unzipK ((x,y):t) k = unzipK t (\(xs, ys) -> k (VC x xs, VC y ys))

-- this seems to work, including the use of show and fmap inside the continuation.
testK = unzipK [(1,2),(3,4),(1,2)] (\(x,y)-> (show y, zipVecToList (x,fmap (+1) y)))


--------------------- Introducing a type class to abstract interface -------------

-- Here is a type class which an associated indexed type G f to represent the
-- results of unzipping.
class Functor f => Rezippable f where
  type G f :: * -> * -> *
  rezip :: (G f s a, G f s b) -> f (a,b)
  unzipInto :: f (a,b) -> (forall s. (G f s a, G f s b) -> r) -> r

-- Unfortunately, I don't know how to allow the index s to be assigned
-- a specific kind. Hence, we cannot use the Vec type defined above and
-- we have to introduce a new one that does not use Nat as the kind of
-- the length index type.
data ZZ :: *  where
data SS :: * -> * where

data Vec' n a where
  VN' :: Vec' ZZ a
  VC' :: a -> Vec' n a -> Vec' (SS n) a

deriving instance Functor (Vec' n)
deriving instance Foldable (Vec' n)

zipVec' :: (Vec' n a, Vec' n b) -> Vec' n (a,b)
zipVec' (VN', VN') = VN'
zipVec' (VC' x xs, VC' y ys) = VC' (x,y) (zipVec' (xs, ys))

listOfVec' :: forall n a. Vec' n a -> [a]
listOfVec' VN' = []
listOfVec' (VC' x xs) = x : listOfVec' xs

instance Rezippable [] where
  type G [] = Vec'
  rezip = listOfVec' . zipVec'
  unzipInto []        k = k (VN', VN')
  unzipInto ((x,y):t) k = unzipInto t (\(xs, ys) -> k (VC' x xs, VC' y ys))

-- Unfortunately this goes horribly wrong when we try to apply it to rezippable,
-- scannable functors in algebraic_rezip.hs
