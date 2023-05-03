module Scan2 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Basics


variable
   A B C D : Set
   F G : Set → Set

-- Basic stuff ------------------------------

-- Using this data type for the Id functor instead of the type level identity
-- function means that Agda's implicit argument inference works without help in 
-- some of the definitions below (ie without passing record values explicitly),
-- but at the cost of a lot of these `I` constructors in the data structures.

data Id (A : Set) : Set where
   I : A → Id A
unI : Id A → A
unI (I x) = x

instance 𝟙Functor : Functor (const 𝟙)
𝟙Functor = record { map = λ _ _ → Unit }

instance IFunctor : Functor Id
IFunctor = record { map = λ f → I ∘ f ∘ unI }

instance AddNat : Monoid Nat
AddNat = record { ε = 0; _∙_ = _+_ }

-- scanning and zipping
-- NB. zipping and unzipping is needed for scanning compositions of functors.
-- Applicative does provide something which *look* like a zip, but it is not
-- guaranteed to work like a zip (be shape preserving, interact with unzip,
-- map, fst and snd in the expected way). Hence the Zip type class. Note that
-- we can always unzip a functor by mapping twice, but there might be a better
-- way for some types.

record Scan (F : Set → Set) : Set₁ where
   field
      scan : {{M : Monoid A}} → F A → F A × A

record Zip (F : Set → Set) : Set₁ where
   field
      zipWith   : (A × B → C) → F A × F B → F C -- these two should be
      unzipWith : (A → B × C) → F A → F B × F C -- mutual inverses
      pure      : A → F A

-- Let's open the type classes so far -------

open Functor {{...}}
open Monoid {{...}}
open Scan {{...}}
open Zip {{...}}

-- usefull for scanners
mapAdd : {{FF : Functor F}} {{M : Monoid A}} → A × F A → F A
mapAdd = uncurry (map ∘ _∙_)

-- Scan instances for unit and id

instance 𝟙Scan : Scan (const 𝟙)
𝟙Scan = record { scan = λ _ → (Unit , ε) }

instance IdScan : Scan Id
IdScan = record { scan = (I ε ,_) ∘ unI }

instance 𝟙Zip : Zip (const 𝟙)
𝟙Zip = record { pure = const Unit;
                zipWith   = λ _ _ → Unit;
                unzipWith = λ _ _ → (Unit , Unit) }

instance IdZip : Zip Id
IdZip = record { pure = I; 
                 zipWith = λ f → I ∘ f ∘ unI ⊗ unI; 
                 unzipWith = λ f → I ⊗ I ∘ f ∘ unI }

-- instances for product -----------------------

Product : (Set → Set) → (Set → Set) → Set → Set
Product F G A = F A × G A

Pair : Set → Set
Pair A = A × A

-- NB. maybe introduce a separate Pair datatype with functor instance?
PairF : Set → Set
PairF = Pair ∘ Id

instance ×Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (Product F G)
×Functor = record { map = λ f → map f ⊗ map f }

instance ×Zip : {{FZ : Zip F}} {{GZ : Zip G}} → Zip (Product F G)
×Zip = record { pure = pure ▲ pure;
                zipWith = λ f → zipWith f ⊗ zipWith f ∘ transp;
                unzipWith = λ f → transp ∘ unzipWith f ⊗ unzipWith f }

scan× : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        {{M : Monoid A}} → Product F G A → Product F G A × A
scan× = ffst (mapAdd ⊗ mapAdd ∘ transp ∘ swap) ∘ assocl ∘ fsnd scanP ∘ transp ∘ scan ⊗ scan
   where scanP : {{M : Monoid A}} → Pair A → Pair A × A
         scanP (x , y) = (ε , x) , (x ∙ y)

instance ×Scan : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}} → Scan (Product F G)
×Scan = record { scan = scan× }


-- Composition of functors ---------------------------------------------------

data _⊙_ (F G : Set → Set) (A : Set) : Set where
   Comp : F (G A) → (F ⊙ G) A

private
   unComp : (F ⊙ G) A → F (G A)
   unComp (Comp x) = x

instance ⊙Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (F ⊙ G)
⊙Functor = record { map = λ f → Comp ∘ map (map f) ∘ unComp }

instance ⊙Zip : {{FZ : Zip F}} {{GZ : Zip G}} → Zip (F ⊙ G)
⊙Zip = record { 
   pure = Comp ∘ pure ∘ pure;
   zipWith   = λ f → Comp ∘ zipWith (zipWith f) ∘ unComp ⊗ unComp;
   unzipWith = λ f → Comp ⊗ Comp ∘ unzipWith (unzipWith f) ∘ unComp }


scan⊙ : {{FZ : Zip F}} {{M : Monoid A}} 
        {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        → F (G A) → F (G A) × A
scan⊙ = ffst (zipWith mapAdd ∘ swap) ∘ assocl ∘ fsnd scan ∘ unzipWith scan

instance ⊙Scan : {{FZ : Zip F}} {{FF : Functor F}} {{GF : Functor G}}
                 {{FS : Scan F}} {{GS : Scan G}} → Scan (F ⊙ G)
⊙Scan = record { scan = ffst Comp ∘ scan⊙ ∘ unComp }

-- Depth indexed top down tree --------------------------------------

TN↓ : Nat → Set → Set
TN↓ zero = Id
TN↓ (suc n) = PairF ⊙ TN↓ n

TN↑ : Nat → Set → Set
TN↑ zero = Id
TN↑ (suc n) = TN↑ n ⊙ PairF

Bush : Nat → Set → Set
Bush zero A = PairF A
Bush (suc n) = Bush n ⊙ Bush n

--- Tests ------------------------------------

tree1 : TN↓ 3 Nat
tree1 = pure 1

tree2 : TN↑ 3 Nat
tree2 = pure 1

bush : Bush 2 Nat
bush = pure 1

bush₁ bush₂ : Bush 2 Nat × Nat
bush₁ = scan bush
bush₂ = scan (fst bush₁)

-- something funny going on here that prevents these from working.
-- It seems that with n an unspecified Nat, Agda can not tell which instance 
-- of Zip to use, even though it will eventually need to be ×Zip or ⊙Zip.

-- iota↓ : (n : Nat) → {{_ : Monoid Nat}} {{_ : Functor (TN↓ n)}} {{_ : Zip (TN↓ n)}} → TN↓ n Nat
-- iota↓ n = fst (scan (id {TN↓ n Nat} (pure 1)))
-- iota : {{FS : Scan F}} {{FZ : Zip F}} → (F : Set → Set) → F Nat
-- iota _ = fst ⦉ scan ⦉ pure 1
