module Scan where

open import Agda.Builtin.Nat
open import Agda.Builtin.List


infixr 4 _⊗_
infixr 9 _∘_

id : {A : Set} → A → A
id x = x

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

record Monoid (M : Set) : Set where
   infixr 4 _∙_
   field
      ε   : M
      _∙_ : M → M → M
      
AddNat : Monoid Nat
AddNat = record { ε = 0; _∙_ = _+_ }

MulNat : Monoid Nat
MulNat = record { ε = 1; _∙_ = _*_ }

record Functor (F : Set → Set) : Set₁ where
   field
      map : {A B : Set} → (A → B) → F A → F B


data _×_ (A B : Set) : Set where
   _,_ : A → B → A × B

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y

curry : {A B C : Set} → (A × B → C) → A → B → C
curry f x y = f (x , y)

fst : {A B : Set} → A × B → A
fst (x , _) = x

snd : {A B : Set} → A × B → B
snd (_ , y) = y

swap : {A B : Set} → A × B → B × A
swap (x , y) = y , x

assocl : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl (a , (b , c)) = ((a , b) , c)

ffst : {A B C : Set} → (A → C) → A × B → C × B
ffst f (x , y) = f x , y

fsnd : {A B C : Set} → (B → C) → A × B → A × C
fsnd f (x , y) = x , f y

_⊗_ : {A B C D : Set} →  (A → C) → (B → D) → A × B → C × D
_⊗_ f  g (x , y) = f x , g y

record Zip (F : Set → Set) : Set₁ where
   field
      zipWith : {A B C : Set} → (A → B → C) → F A × F B → F C
      unzipWith : {A B C : Set} → (A → B × C) → F A → F B × F C

record Scan (F : Set → Set) : Set₁ where
   field
      scan : {A : Set} → {{M : Monoid A}} → F A → F A × A

data Pair (A : Set) : Set where
   _#_ : A → A → Pair A

mapP : {A B : Set} → (A → B) → Pair A → Pair B
mapP f (x # y) = f x # f y

instance 
   PairFunctor : Functor Pair 
   PairFunctor = record { map = mapP }

unzipP : {A B : Set} → Pair (A × B) → Pair A × Pair B
unzipP ((x1 , y1) # (x2 , y2)) = ((x1 # x2), (y1 # y2))

unzipWithP : {A B C : Set} → (C → A × B) → Pair C → Pair A × Pair B
unzipWithP f = let open Functor {{...}} in unzipP ∘ map f 

zipWithP : {A B C : Set} → (A → B → C) → (Pair A × Pair B) → Pair C
zipWithP f ((x1 # x2) , (y1 # y2)) = (f x1 y1 # f x2 y2)

scanP : {A : Set} → {{M : Monoid A}} → Pair A → Pair A × A
scanP (x # y) = let open Monoid {{...}} in ((ε # x) , (x ∙ y))

instance 
   PairZip : Zip Pair
   PairZip = record { zipWith = zipWithP; unzipWith = unzipWithP }

   PairScan : Scan Pair
   PairScan = record { scan = scanP }

----------------------------------------------------------------------

module Direct where
   data Tree (A : Set) : Nat → Set where
      L : A → Tree A 0
      _^_ : {n : Nat} → Tree A n → Tree A n → Tree A (suc n)
   -- tree4 = (LL 1 & LL 2) & (LL 3 & LL 4)

   mapTree : {A B : Set} → {n : Nat} → (A → B) → Tree A n → Tree B n
   mapTree f (L x) = L (f x)
   mapTree f (a ^ b) = mapTree f a ^ mapTree f b

   scan : {n : Nat} → Tree Nat n → Tree Nat n × Nat
   scan (L x) = L 0 , x
   scan (a ^ b) = combine (scan a) (scan b) where
      combine : {n : Nat} → Tree Nat n × Nat → Tree Nat n × Nat → Tree Nat (suc n) × Nat 
      combine (a1 , asum) (b1 , bsum) = (a1 ^ mapTree (asum +_) b1) , (asum + bsum)

   iota : (n : Nat) → Tree Nat n
   iota n = fst (iota' n) where
      iota' : (n : Nat) → Tree Nat n × Nat
      iota' zero = L 1 , 1
      iota' (suc n) = double (iota' n) where
         double : {n : Nat} → Tree Nat n × Nat → Tree Nat (suc n) × Nat
         double (t , b) = ((t ^ mapTree (b +_) t) , (2 * b))

---------------------------------------------------------------------

module TopDown where
   open Monoid {{...}}
   open Functor {{...}}
   open Zip {{...}}
   open Scan {{...}}

   data T (A : Set) : Nat → Set where
      L : A → T A 0
      B : {n : Nat} → Pair (T A n) → T A (suc n)

   mapT : {n : Nat} → {A B : Set} → (A → B) → T A n → T B n
   mapT f (L x) = L (f x)
   mapT f (B tp) = B (map (mapT f) tp)

   instance TFunctor : {n : Nat} → Functor (λ A → T A n)
   TFunctor {n} = record { map = mapT {n} }

   scanT : {A : Set} → {{M : Monoid A}} → {n : Nat} → T A n → T A n × A
   scanT (L x) = L ε , x
   scanT (B tp) = (ffst (B ∘ zipWith (map ∘ _∙_) ∘ swap) ∘ assocl ∘ fsnd scan ∘ unzipWith scanT) tp

   iota : (n : Nat) → T Nat n
   iota n = fst (iota' n) where
      iota' : (n : Nat) → T Nat n × Nat
      iota' zero = L 1 , 1
      iota' (suc n) = double (iota' n) where
         double : {n : Nat} → T Nat n × Nat → T Nat (suc n) × Nat
         double (t , b) = (B (t # map (b +_) t) , (2 * b))


module BottomUp where
   open Monoid {{...}}
   open Functor {{...}}
   open Zip {{...}}
   open Scan {{...}}

   data T (A : Set) : Nat → Set where
      L : A → T A 0
      B : {n : Nat} → T (Pair A) n → T A (suc n)

   mapT : {n : Nat} → {A B : Set} → (A → B) → T A n → T B n
   mapT f (L x) = L (f x)
   mapT f (B t) = B (mapT (map f) t)

   -- unzipT : {n : Nat} → {A B : Set} → T (A × B) n → T A n × T B n
   -- unzipT (L (x , y)) = L x , L y
   -- unzipT (B t) = (B ⊗ B) (unzipT (map unzipP t))

   unzipWithT : {n : Nat} → {A B C : Set} → (C → A × B) → T C n → T A n × T B n
   unzipWithT f (L z) = (L ⊗ L) (f z)
   unzipWithT f (B t) = (B ⊗ B) (unzipWithT (unzipWith f) t)

   -- zipT : {n : Nat} → {A B : Set} → T A n → T B n → T (A × B) n
   -- zipT (L x) (L y) = L (x , y)
   -- zipT (B a) (B b) = B (map (uncurry zipP) (zipT a b))

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

   iota : (n : Nat) → T Nat n
   iota n = fst (iota' n) where
      iota' : (n : Nat) → T Nat n × Nat
      iota' zero = L 1 , 1
      iota' (suc n) = double (iota' n) where
         beside : {A : Set} {n : Nat} → T A n → T A n → T (Pair A) n
         beside (L x) (L y) = L (x # y)
         beside (B a) (B b) = B (beside a b)

         double : {n : Nat} → T Nat n × Nat → T Nat (suc n) × Nat
         double (t , b) = (B (beside t (map (b +_) t)), (2 * b))
