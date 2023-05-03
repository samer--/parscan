module Scan2 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Basics


variable
   A B C D : Set
   F G : Set → Set

-- Basic stuff ------------------------------

id₁ : {A : Set₁} → A → A
id₁ x = x

instance 𝟙Functor : Functor (const 𝟙)
𝟙Functor = record { map = λ _ _ → Unit }

instance IdFunctor : Functor id₁
IdFunctor = record { map = id }

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

instance IdScan : Scan id₁
IdScan = record { scan = λ x → (ε , x) }

instance 𝟙Zip : Zip (const 𝟙)
𝟙Zip = record { pure = const Unit;
                zipWith   = λ _ _ → Unit;
                unzipWith = λ _ _ → (Unit , Unit) }

instance IdZip : Zip id₁
IdZip = record { pure = id; zipWith = id; unzipWith = id }

-- instances for product -----------------------

Product : (Set → Set) → (Set → Set) → Set → Set
Product F G A = F A × G A

Pair : Set → Set
Pair A = A × A

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
⊙Functor {{FF}} {{GF}} = record { map = λ f → Comp ∘ map {{FF}} (map {{GF}} f) ∘ unComp }

instance ⊙Zip : {{FZ : Zip F}} {{GZ : Zip G}} → Zip (F ⊙ G)
⊙Zip {{FZ}} {{GZ}} = record { 
   pure = Comp ∘ Zip.pure FZ ∘ Zip.pure GZ;
   zipWith   = λ f → Comp ∘ zipWith {{FZ}} (zipWith {{GZ}} f) ∘ unComp ⊗ unComp;
   unzipWith = λ f → Comp ⊗ Comp ∘ unzipWith {{FZ}} (unzipWith {{GZ}} f) ∘ unComp }


scan⊙ : {{FZ : Zip F}} {{M : Monoid A}} 
        {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        → (F ⊙ G) A → (F ⊙ G) A × A
scan⊙ {{FZ}} {{_}} {{_}} {{GF}} (Comp x) =
   (ffst (Comp ∘ zipWith (mapAdd {{GF}}) ∘ swap) ∘ assocl ∘ fsnd scan ∘ Zip.unzipWith FZ scan) x

instance ⊙Scan : {{FZ : Zip F}} {{FF : Functor F}} {{GF : Functor G}}
                 {{FS : Scan F}} {{GS : Scan G}} → Scan (F ⊙ G)
⊙Scan = record { scan = scan⊙ }

-- Depth indexed top down tree --------------------------------------

TN↓ : Nat → Set → Set
TN↓ zero = id₁
TN↓ (suc n) = Pair ⊙ TN↓ n

TN↑ : Nat → Set → Set
TN↑ zero = id₁
TN↑ (suc n) = TN↑ n ⊙ Pair

Bush : Nat → Set → Set
Bush zero = Pair
Bush (suc n) = Bush n ⊙ Bush n

--- Tests ------------------------------------

tscan : Pair (Pair (Pair Nat)) × Nat
tscan = scan (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8)))

-- tscan2a tscan2b : (Nat ⊎ Pair Nat) × Nat
-- tscan2a = scan (Inl 3)
-- tscan2b = scan (Inr (4 , 5))

ptree0 : (Pair ⊙ Pair) Nat
ptree0 = Comp ((1 , 2) , (3 , 4))

ptree1 : (Pair ⊙ (Pair ⊙ Pair)) Nat
ptree1 = Comp (Comp ((1 , 2) , (3 , 4)) , Comp ((5 , 6) , (7 , 8)))

ptree2 : ((Pair ⊙ Pair) ⊙ Pair) Nat
ptree2 = Comp (Comp (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8))))

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
