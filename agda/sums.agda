-- This module contains an ordinary sum type and a 'tagged' sum type which
-- has an extra index which keeps track of which 'side' value we have (left
-- or right). This means that function that operate on these can contrain 
-- 'sidedness' (chirality??) of the inputs and outputs.

open import Agda.Builtin.Bool
open import Basics

variable
   A B C D : Set
   F G : Set → Set

open Functor {{...}}

module Plain where
   data _⊎_ (A B : Set) : Set where
      Inl : A → A ⊎ B
      Inr : B → A ⊎ B

   _⊕_ : (A → C) → (B → D) → A ⊎ B → C ⊎ D
   (f ⊕ g) (Inl x) = Inl (f x)
   (f ⊕ g) (Inr y) = Inr (g y)

   Sum : (Set → Set) → (Set → Set) → Set → Set
   Sum F G A = F A ⊎ G A

   instance ⊎Functor : {{FF : Functor F}} {{GF : Functor G}} → Functor (Sum F G)
   ⊎Functor = record { map = mapSum } where
      mapSum : {{FF : Functor F}} {{GF : Functor G}} → (A → B) → Sum F G A → Sum F G B
      mapSum f = map f ⊕ map f

   -- scan+ : {{FS : Scan F}} {{GS : Scan G}} {{M : Monoid A}} → Sum F G A → Sum F G A × A
   -- scan+ (Inl x) = ffst Inl (scan x)
   -- scan+ (Inr y) = ffst Inr (scan y)

   -- instance +Scan : {{FF : Functor F}} {{GF : Functor G}} {{FS : Scan F}} {{GS : Scan G}} → Scan (Sum F G)
   -- +Scan = record { scan = scan+ }

   -- defining a Zip instance for Sums is going to be a problem because we can't
   -- zip a left-value with a right-value. This means we can't use a Sum type as the
   -- outer functor in a composition of functors and expect to be able to scan it.
   -- We would need index the sum type somehow, similar to how we can index a list
   -- type by length to verify that two lists are zippable.

-- Indexed sum ---------------------------------------------

module Indexed where
   data IU : Bool → (A B : Set) → Set where
      Inl : A → IU false A B
      Inr : B → IU true  A B

   _⊕_ : {t : Bool} → (A → C) → (B → D) → IU t A B → IU t C D
   (f ⊕ g) (Inl x) = Inl (f x)
   (f ⊕ g) (Inr y) = Inr (g y)

   Sum : Bool → (Set → Set) → (Set → Set) → Set → Set
   Sum t F G A = IU t (F A) (G A)

   instance IUFunctor : {{t : Bool}} {{FF : Functor F}} {{GF : Functor G}} → Functor (Sum t F G)
   IUFunctor = record { map = mapSum } where
      mapSum : {{t : Bool}} {{FF : Functor F}} {{GF : Functor G}} → (A → B) → Sum t F G A → Sum t F G B
      mapSum f = map f ⊕ map f

