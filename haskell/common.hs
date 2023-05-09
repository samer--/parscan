{-# LANGUAGE AllowAmbiguousTypes, GADTs, DataKinds, UnicodeSyntax #-}
module Common where

import Data.Functor.Identity
import Data.Functor.Classes
import Control.Arrow (first)
import Control.Applicative (liftA2)
import Control.Monad.State.Strict
import System.IO.Unsafe
import qualified Data.Traversable

infix 8 ⊗, ▲

{-# ANN module "HLint: ignore Use camelCase" #-}

noisy_add ∷ Int → Int → Int
noisy_add x y =
  unsafePerformIO (putStrLn ("\nadding "++show x++" + "++show y) >> return (x+y))

instance Semigroup Int where (<>) = (+)
instance Monoid    Int where mempty = 0

---------------------------------------------

dup x = (x,x)
(f ⊗ g) (x,y) = (f x, g y)
(f ▲ g) x = (f x, g x)
(forkl, forkr) = ((▲ id), (id ▲))
(prod, fork) = ((⊗), (▲))
swap (x,y) = (y,x)
assocl (x, (y, z)) = ((x, y), z)
transp ((a,b), (c,d)) = ((a,c), (b,d))

-- zip for Applicatives - not guaranteed to be shape preserving
zipWithA ∷ Applicative f ⇒ ((a,b) → c) → (f a, f b) → f c
zipWithA f = uncurry (liftA2 (curry f))

-- unzip using only Functor: will be shape preserving but double traversal?
unzipF ∷ Functor f ⇒ f (a,b) → (f a, f b)
unzipF x = (fmap fst x, fmap snd x)

unzipWithF f = unzipF . fmap f

scanTraversable t = runState (traverse (state . forkr . (<>)) t) mempty -- x ↦ s ↦ (s, s<>x)


mapAdd ∷ (Monoid a, Functor f) ⇒  (f a, a) → f a
mapAdd = uncurry (fmap . (<>)) . swap

class Zippable f where
  fzipWith ∷ ((a, b) → c) → (f a, f b) → f c
  unzipWith ∷ (a → (b, c)) → f a → (f b, f c)

class Functor f ⇒ Scannable f where
  scan ∷ Monoid m ⇒ f m → (f m, m)

---------------------------------------------
-- Pair functor, as distinct from tuples

infixr 3 :#

data Pair a = a :# a deriving (Show, Functor)

instance Show1 Pair where
  liftShowsPrec showsPrec _showsList n (x :# y) = showParen True (showsPrec n x . showString ":#" . showsPrec n y)

instance Foldable Pair where
  foldMap f (x :# y) = f x <> f y

instance Applicative Pair where
  pure x = x :# x
  (f :# g) <*> (x :# y) = f x :# g y

instance Traversable Pair where
  sequenceA (ap1 :# ap2) = (:#) <$> ap1 <*> ap2 -- ∷ Pair (f a) → f (Pair a)

zipWithP f (x1 :# x2, y1 :# y2) = f (x1,y1) :# f (x2,y2)
unzipP ((x1,y1) :# (x2,y2)) = (x1 :# x2, y1 :# y2)
unzipWithP f = unzipP . fmap f
scanP (x :# y) = (mempty :# x, x <> y)

instance Zippable Pair where
  fzipWith = zipWithP
  unzipWith = unzipWithP

instance Scannable Pair where
  scan = scanP

scanWith ∷ (Scannable f, Monoid m) ⇒ (a → m) → f a → (f m, m)
scanWith f = scan . fmap f

iota ∷ (Applicative f, Scannable f) ⇒ f Int
iota = fst . scan . pure $ 1

--------------------------------------------------
-- Fun with type level naturals

{- Thanks to DataKinds, this defines both value level terms Zero and
 - Succ _ of - type Nat AND types Zero and Succ _ of kind Nat -}
data Nat = Zero | Succ Nat deriving Show

-- These are type indexed naturals: natural number values whos type is
-- indexed by the corresponding type level natural.
data INat (a ∷ Nat) where
  Z ∷ INat 'Zero
  S ∷ IsNat n ⇒ INat n → INat ('Succ n) -- this constraint is needed by topdown.hs

-- this class allows us to turn type level nats in to term level nats
class IsNat a where
  toInt  ∷ Int
  toINat ∷ INat a

instance IsNat 'Zero where
  toInt   = 0
  toINat  = Z

instance IsNat n ⇒ IsNat ('Succ n) where
  toInt  = 1 + toInt @n
  toINat = S toINat

instance IsNat n ⇒ Show (INat n) where
  show x = "{" ++  show (toInt @n) ++ "}"

type One = 'Succ 'Zero
type Two = 'Succ One
type Three = 'Succ Two
type Four = 'Succ Three
