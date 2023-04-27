module Basics where

infixr 9 _⊗_
infixr 8 _∘_
infixr 1 _⦉_
infixl 1 _⦊_

private 
   variable
      A B C D : Set

id : {A : Set} → A → A
id x = x

_∘_ : ∀ {a} {A B C : Set a} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

_⦉_ : (A → B) → A → B
f ⦉ x = f x

_⦊_ : A → (A → B) → B
x ⦊ f = f x

const : ∀ {a} {A B : Set a} → A → B → A
const x _ = x

data 𝟙 : Set where
   Unit : 𝟙

data _×_ (A B : Set) : Set where
   _,_ : A → B → A × B

-- Tools making use of products ----------------------------

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
(f ⊗ g) (x , y) = f x , g y

_▲_ : (A → B) → (A → C) → A → B × C
(f ▲ g) x = f x , g x

-- some type classes ----------------------

record Functor (F : Set → Set) : Set₁ where
   field
      map : (A → B) → F A → F B

record Monoid (M : Set) : Set where
   infixr 4 _∙_
   field
      ε   : M
      _∙_ : M → M → M

