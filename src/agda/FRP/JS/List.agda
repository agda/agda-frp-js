open import FRP.JS.Nat using ( ℕ ; zero ; suc )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )

module FRP.JS.List where

infixr 4 _∷_ _++_
infixr 2 _≟[_]_

data List {α} (A : Set α) : Set α where
  [] : List A
  _∷_ : (a : A) → (as : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

[_] : ∀ {α} {A : Set α} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {α} {A : Set α} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {α β} {A : Set α} {B : Set β} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {α β} {A : Set α} {B : Set β} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

buildAppend : ∀ {α} {A : Set α} → List A → (ℕ → A) → ℕ → List A
buildAppend as f zero    = as
buildAppend as f (suc n) = buildAppend (f n ∷ as) f n

build : ∀ {α} {A : Set α} → (ℕ → A) → ℕ → List A
build = buildAppend []

length : ∀ {α} {A : Set α} → List A → ℕ
length = foldr (λ a n → suc n) zero

lookup : ∀ {α} {A : Set α} → List A → ℕ → Maybe A
lookup []       x       = nothing
lookup (a ∷ as) zero    = just a
lookup (a ∷ as) (suc n) = lookup as n

_≟[_]_ : ∀ {α β} {A : Set α} {B : Set β} → List A → (A → B → Bool) → List B → Bool
[]       ≟[ p ] []       = true
(a ∷ as) ≟[ p ] (b ∷ bs) = (p a b) ∧ (as ≟[ p ] bs)
_        ≟[ p ] _        = false

