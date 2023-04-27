module Scan2 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Basics


variable
   A B C D : Set
   F G : Set → Set

-- Basic stuff ------------------------------

id₁ : ∀ {a} {A : Set a} → A → A
id₁ x = x

instance 𝟙Functor : Functor (const 𝟙)
𝟙Functor = record { map = λ _ _ → Unit }

instance IdFunctor : Functor id₁
IdFunctor = record { map = id }

data _⊎_ (A B : Set) : Set where
   Inl : A → A ⊎ B
   Inr : B → A ⊎ B


instance AddNat : Monoid Nat
AddNat = record { ε = 0; _∙_ = _+_ }

-- scanning and zipping
-- NB. zipping and unzipping is needed for scanning compositions of functors.
-- Applicative does provide something which *look* like a zip, but it is not
-- guaranteed to work like a zip (be shape preserving, interact with unzip,
-- map, fst and snd in the expected way). Hence the Zip type class. Not that
-- we can always unzip a functor by mapping twice, but there might be a better
-- way for some types.

record Scan (F : Set → Set) : Set₁ where
   field
      scan : {{M : Monoid A}} → F A → F A × A

record Zip (F : Set → Set) : Set₁ where
   field
      zipWith   : (A → B → C) → F A × F B → F C
      unzipWith : (A → B × C) → F A → F B × F C
      pure      : A → F A

-- Let's open the type classes so far -------

open Functor {{...}}
open Monoid {{...}}
open Scan {{...}}
open Zip {{...}}


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
IdZip = record { pure = id; zipWith = uncurry; unzipWith = id }

-- instances for product -----------------------

Product : (Set → Set) → (Set → Set) → Set → Set
Product F G A = F A × G A

Pair : Set → Set
Pair A = A × A

instance ×Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (Product F G)
×Functor = record { map = map× } where
   map× : {{FF : Functor F}} {{GF : Functor G}} → (A → B) → Product F G A → Product F G B
   map× f = map f ⊗ map f


instance ×Zip : {{FZ : Zip F}} {{GZ : Zip G}} → Zip (Product F G)
×Zip = record { pure = pure ▲ pure;
                zipWith = λ f → zipWith f ⊗ zipWith f ∘ transp;
                unzipWith = λ f → transp ∘ unzipWith f ⊗ unzipWith f }



mapAdd : {{M : Monoid A}} {{FF : Functor F}} → A × F A → F A
mapAdd = uncurry (map ∘ _∙_)

scan× : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        {{M : Monoid A}} → Product F G A → Product F G A × A
scan× = ffst (mapAdd ⊗ mapAdd ∘ transp ∘ swap) ∘ assocl ∘ fsnd scanP ∘ transp ∘ scan ⊗ scan
   where scanP : {{M : Monoid A}} → Pair A → Pair A × A
         scanP (x , y) = (ε , x) , (x ∙ y)

instance ×Scan : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}} → Scan (Product F G)
×Scan = record { scan = scan× }

-- Tools and instances for coproducts -------------------------------------------

_⊕_ : (A → C) → (B → D) → A ⊎ B → C ⊎ D
(f ⊕ g) (Inl x) = Inl (f x)
(f ⊕ g) (Inr y) = Inr (g y)

Sum : (Set → Set) → (Set → Set) → Set → Set
Sum F G A = F A ⊎ G A

instance ⊎Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (Sum F G)
⊎Functor = record { map = mapSum } where
   mapSum : {A B : Set} {F G : Set → Set} {{FF : Functor F}} {{GF : Functor G}}
            → (A → B) → Sum F G A → Sum F G B
   mapSum f = map f ⊕ map f

scan+ : {{FS : Scan F}} {{GS : Scan G}} {{M : Monoid A}} → Sum F G A → Sum F G A × A
scan+ (Inl x) = ffst Inl (scan x)
scan+ (Inr y) = ffst Inr (scan y)

instance +Scan : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}} → Scan (Sum F G)
+Scan = record { scan = scan+ }

-- defining a Zip instance for Sums is going to be a problem because we can't
-- zip a left-value with a right-value. This means we can't use a Sum type as the
-- outer functor in a composition of functors and expect to be able to scan it.
-- We would need index the sum type somehow, similar to how we can index a list
-- type by length to verify that two lists are zippable.

-- Composition of functors ---------------------------------------------------

data _⊙_ (F G : Set → Set) (A : Set) : Set where
   Comp : F (G A) → (F ⊙ G) A

unComp : (F ⊙ G) A → F (G A)
unComp (Comp x) = x

instance ⊙Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (F ⊙ G)
⊙Functor = record { map = map∘ } where
   map∘ : {{FF : Functor F}} {{GF : Functor G}} → (A → B) → (F ⊙ G) A → (F ⊙ G) B
   map∘ {{FF}} {{GF}} f (Comp x) = Comp (Functor.map FF (Functor.map GF f) x)

instance ⊙Zip : {{FZ : Zip F}} {{GZ : Zip G}} → Zip (F ⊙ G)
⊙Zip {{FZ}} {{GZ}} = record { 
   pure = Comp ∘ Zip.pure FZ ∘ Zip.pure GZ;
   zipWith   = λ f → Comp ∘ Zip.zipWith FZ (curry (Zip.zipWith GZ f)) ∘ unComp ⊗ unComp;
   unzipWith = λ f → Comp ⊗ Comp ∘ Zip.unzipWith FZ (Zip.unzipWith GZ f) ∘ unComp }


scan⊙ : {{FZ : Zip F}} {{M : Monoid A}} 
        {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        → (F ⊙ G) A → (F ⊙ G) A × A
scan⊙ {{FZ}} {{_}} {{_}} {{GF}} (Comp x) =
   (ffst (Comp ∘ zipWith (Functor.map GF ∘ _∙_) ∘ swap) ∘ assocl ∘ fsnd scan ∘ Zip.unzipWith FZ scan) x

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

Tbush : Nat → Set → Set
Tbush zero = Pair
Tbush (suc n) = Tbush n ⊙ Tbush n

--- Tests ------------------------------------

tscan : Pair (Pair (Pair Nat)) × Nat
tscan = scan (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8)))

tscan2a tscan2b : (Nat ⊎ Pair Nat) × Nat
tscan2a = scan (Inl 3)
tscan2b = scan (Inr (4 , 5))

ptree0 : (Pair ⊙ Pair) Nat
ptree0 = Comp ((1 , 2) , (3 , 4))

ptree1 : (Pair ⊙ (Pair ⊙ Pair)) Nat
ptree1 = Comp (Comp ((1 , 2) , (3 , 4)) , Comp ((5 , 6) , (7 , 8)))

ptree2 : ((Pair ⊙ Pair) ⊙ Pair) Nat
ptree2 = Comp (Comp (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8))))

-- something funny going on here that prevents these from working.
-- It seems that with n an unspecified Nat, Agda can not tell which instance 
-- of Zip to use, even though it will eventually need to be ×Zip or ⊙Zip.

-- iota↓ : (n : Nat) → {{_ : Monoid Nat}} {{_ : Functor (TN↓ n)}} {{_ : Zip (TN↓ n)}} → TN↓ n Nat
-- iota↓ n = fst (scan (id {TN↓ n Nat} (pure 1)))
-- iota : {{FS : Scan F}} {{FZ : Zip F}} → (F : Set → Set) → F Nat
-- iota _ = fst ⦉ scan ⦉ pure 1
