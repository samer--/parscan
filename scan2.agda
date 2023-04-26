-- {-# OPTIONS --overlapping-instances --instance-search-depth 6 #-}
module Scan2 where

open import Agda.Builtin.Nat
open import Agda.Builtin.List


infixr 4 _⊗_
infixr 9 _∘_
infixr 5 _:<_
infixr 1 _⦉_
infixl 1 _⦊_

variable
   A B C D : Set
   F G : Set → Set

-- Basic stuff ------------------------------

id : {A : Set} → A → A
id x = x

id₁ : ∀ {a} {A : Set a} → A → A
id₁ x = x

_∘_ : ∀ {a} {A B C : Set a} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

_⦉_ : (A → B) → A → B
f ⦉ x = f x

_⦊_ : A → (A → B) → B
x ⦊ f = f x

const : ∀ {a} {A B : Set a} → A → B → A
const x _ = x

record Functor (F : Set → Set) : Set₁ where
   field
      map : (A → B) → F A → F B

data 𝟙 : Set where
   Unit : 𝟙

instance 𝟙Functor : Functor (const 𝟙)
𝟙Functor = record { map = λ _ _ → Unit }

instance IdFunctor : Functor id₁
IdFunctor = record { map = id }

data _×_ (A B : Set) : Set where
   _,_ : A → B → A × B

data _⊎_ (A B : Set) : Set where
   Inl : A → A ⊎ B
   Inr : B → A ⊎ B

-- Monoid -------------------------------------

record Monoid (M : Set) : Set where
   infixr 4 _∙_
   field
      ε   : M
      _∙_ : M → M → M

instance AddNat : Monoid Nat
AddNat = record { ε = 0; _∙_ = _+_ }

-- MulNat : Monoid Nat
-- MulNat = record { ε = 1; _∙_ = _*_ }

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

-- Tools and instances for products ----------------------------

uncurry : (A → B → C) → A × B → C
uncurry f (x , y) = f x y

curry : (A × B → C) → A → B → C
curry f x y = f (x , y)

fst : A × B → A
fst (x , _) = x

snd : A × B → B
snd (_ , y) = y

swap : A × B → B × A
swap (x , y) = y , x

assocl : (A × (B × C)) → ((A × B) × C)
assocl (a , (b , c)) = ((a , b) , c)

transp : (A × B) × (C × D) → (A × C) × (B × D)
transp ((a , b) , (c , d)) = ((a , c) , (b , d))

ffst : (A → C) → A × B → C × B
ffst f (x , y) = f x , y

fsnd : (B → C) → A × B → A × C
fsnd f (x , y) = x , f y

_⊗_ : (A → C) → (B → D) → A × B → C × D
(f ⊗ g) (x , y) = (f x , g y)

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
×Zip = record { pure = λ x → pure x , pure x;
                zipWith = λ f → (zipWith f ⊗ zipWith f) ∘ transp;
                unzipWith = λ f → transp ∘ (unzipWith f ⊗ unzipWith f) }



mapAdd : {{M : Monoid A}} {{FF : Functor F}} → A × F A → F A
mapAdd = uncurry (map ∘ _∙_)

scan× : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        {{M : Monoid A}} → Product F G A → Product F G A × A
scan× = ffst ((mapAdd ⊗ mapAdd) ∘ transp ∘ swap) ∘ assocl ∘ fsnd scanP ∘ transp ∘ (scan ⊗ scan)
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

instance ⊙Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (F ⊙ G)
⊙Functor = record { map = map∘ } where
   map∘ : {{FF : Functor F}} {{GF : Functor G}} → (A → B) → (F ⊙ G) A → (F ⊙ G) B
   map∘ {{FF}} {{GF}} f (Comp x) = Comp (Functor.map FF (Functor.map GF f) x)

scan⊙ : {{FZ : Zip F}} {{M : Monoid A}} 
        {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}}
        → (F ⊙ G) A → (F ⊙ G) A × A
scan⊙ {{FZ}} {{_}} {{_}} {{GF}} (Comp x) =
   (ffst (Comp ∘ zipWith (Functor.map GF ∘ _∙_) ∘ swap) ∘ assocl ∘ fsnd scan ∘ Zip.unzipWith FZ scan) x

instance ⊙Scan : {{FZ : Zip F}} {{FF : Functor F}} {{GF : Functor G}}
                 {{FS : Scan F}} {{GS : Scan G}} → Scan (F ⊙ G)
⊙Scan = record { scan = scan⊙ }

-- List --------- ------------------------------------------------

-- this sure is a weird way to build a list type...
data List1 (A : Set) : Set where
   L1 : 𝟙 ⊎ (A × List1 A) → List1 A

nil : {A : Set} → List1 A
nil = L1 (Inl Unit)

_:<_ : {A : Set} → A → List1 A → List1 A
h :< t = L1 (Inr (h , t))

instance List1Monoid : {A : Set} → Monoid (List1 A)
List1Monoid = record { ε = L1 (Inl Unit); _∙_ = append } where
   append : List1 A → List1 A → List1 A
   append (L1 (Inl Unit)) x = x
   append (L1 (Inr (h , t))) x = L1 (Inr (h , append t x))

mapList1 : (A → B) → List1 A → List1 B
instance List1Functor : Functor List1
List1Functor = record { map = mapList1 }

{-# TERMINATING #-}
mapList1 f (L1 x) = L1 (map f x)

-- Top down tree ------------------------------------------------

data Tree↓ (A : Set) : Set where
   T↓ : A ⊎ Pair (Tree↓ A) → Tree↓ A

instance Tree↓Functor : Functor Tree↓
{-# TERMINATING #-}
mapTree↓ : (A → B) → Tree↓ A → Tree↓ B
mapTree↓ f (T↓ x) = T↓ (map f x)
Tree↓Functor = record { map = mapTree↓ }

-- Bottom up tree -----------------------------------------------

data Tree↑ (A : Set) : Set where
   T↑ : A ⊎ (Tree↑ ⊙ Pair) A → Tree↑ A

instance Tree↑Functor : Functor Tree↑
{-# TERMINATING #-}
mapTree↑ : (A → B) → Tree↑ A → Tree↑ B
mapTree↑ f (T↑ x) = T↑ (map f x)
Tree↑Functor = record { map = mapTree↑ }

-- Depth indexed top down tree --------------------------------------

TN↓ : Nat → Set → Set
TN↓ zero = id₁
TN↓ (suc n) = Pair ⊙ TN↓ n

TN↑ : Nat → Set → Set
TN↑ zero = id₁
TN↑ (suc n) = TN↑ n ⊙ Pair

Tbash : Nat → Set → Set
Tbash zero = Pair
Tbash (suc n) = Tbash n ⊙ Tbash n

-- data Pair (A : Set) : Set where
--    _#_ : A → A → Pair A

-- mapP : {A B : Set} → (A → B) → Pair A → Pair B
-- mapP f (x # y) = f x # f y

-- scanU : {A : Set} → {{M : Monoid A}} → U A → U A × A
-- scanU _ = Unit , ε

-- instance PairFunctor : Functor Pair
-- PairFunctor = record { map = mapP }

-- unzipP : {A B : Set} → Pair (A × B) → Pair A × Pair B
-- unzipP ((x1 , y1) # (x2 , y2)) = ((x1 # x2), (y1 # y2))

-- unzipWithP : {A B C : Set} → (C → A × B) → Pair C → Pair A × Pair B
-- unzipWithP f = unzipP ∘ map f

-- zipWithP : {A B C : Set} → (A → B → C) → (Pair A × Pair B) → Pair C
-- zipWithP f ((x1 # x2) , (y1 # y2)) = (f x1 y1 # f x2 y2)

-- constP : {A : Set} → A → Pair A
-- constP x = x # x

-- instance
--    PairZip : Zip Pair
--    PairZip = record { zipWith = zipWithP; unzipWith = unzipWithP; pure = constP }

--    PairScan : Scan Pair
--    PairScan = record { scan = scanP }
----------------------------------------------------------------------

{-
module TopDown where
   mapT : {n : Nat} → {A B : Set} → (A → B) → T A n → T B n
   mapT f (L x) = L (f x)
   mapT f (B tp) = B (map (mapT f) tp)

   pureT : {A : Set} → (x : A) → (n : Nat) → T Nat n
   pureT x zero = L x
   -- pureT x (suc n) = B (constP (pureT x n))

   scanT : {A : Set} → {{M : Monoid A}} → {n : Nat} → T A n → T A n × A
   scanT (L x) = L ε , x
   scanT (B tp) = (ffst (B ∘ zipWith (map ∘ _∙_) ∘ swap) ∘ assocl ∘ fsnd scan ∘ unzipWith scanT) tp


module BottomUp where
   mapT : {n : Nat} → {A B : Set} → (A → B) → T A n → T B n
   mapT f (L x) = L (f x)
   mapT f (B t) = B (mapT (map f) t)

   pureT : {A : Set} → A → (n : Nat) → T Nat n
   pureT x zero = L x
   pureT x (suc n) = B (twice (pureT x n)) where
       twice : {A : Set} {n : Nat} → T A n → T (Pair A) n
       twice (L x) = L (x # x)
       twice (B a) = B (twice a)

   unzipWithT : {n : Nat} → {A B C : Set} → (C → A × B) → T C n → T A n × T B n
   unzipWithT f (L z) = (L ⊗ L) (f z)
   unzipWithT f (B t) = (B ⊗ B) (unzipWithT (unzipWith f) t)

   zipWithT : {n : Nat} → {A B C : Set} → (A → B → C) → T A n × T B n → T C n
   zipWithT f ((L x) , (L y)) = L (f x y)
   zipWithT f ((B a) , (B b)) = B (zipWithT (curry (zipWith f)) (a , b))

   instance TFunctor : {n : Nat} → Functor (λ A → T A n)
   TFunctor {n} = record { map = mapT {n} }

   instance TZip : {n : Nat} → Zip (λ A → T A n)
   TZip {n} = record { zipWith = zipWithT; unzipWith = unzipWithT }

   scanT : {A : Set} → {{M : Monoid A}} → {n : Nat} → T A n → T A n × A
   scanT (L x) = L ε , x
   scanT (B t) = (ffst (B ∘ zipWith (map ∘ _∙_) ∘ swap) ∘ assocl ∘ fsnd scanT ∘ unzipWith scan) t

-}

--- Tests ------------------------------------

tscan : Pair (Pair (Pair Nat)) × Nat
tscan = scan (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8)))

tscan2a tscan2b : (Nat ⊎ Pair Nat) × Nat
tscan2a = scan (Inl 3)
tscan2b = scan (Inr (4 , 5))

singleton : {A : Set} → A → List1 A
singleton x = x :< nil

listscan : Sum id₁ Pair (List1 Nat) × List1 Nat
listscan = scan (map singleton (Inr (3 , 4)))

ptree0 : (Pair ⊙ Pair) Nat
ptree0 = Comp ((1 , 2) , (3 , 4))

ptree1 : (Pair ⊙ (Pair ⊙ Pair)) Nat
ptree1 = Comp (Comp ((1 , 2) , (3 , 4)) , Comp ((5 , 6) , (7 , 8)))

ptree2 : ((Pair ⊙ Pair) ⊙ Pair) Nat
ptree2 = Comp (Comp (((1 , 2) , (3 , 4)) , ((5 , 6) , (7 , 8))))
