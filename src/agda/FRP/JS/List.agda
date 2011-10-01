{-# OPTIONS --universe-polymorphism #-}

open import FRP.JS.Nat using ( ℕ ; zero ; suc )

module FRP.JS.List where

data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : (a : A) → (as : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

buildAppend : ∀ {a} {A : Set a} → List A → (ℕ → A) → ℕ → List A
buildAppend as f zero    = as
buildAppend as f (suc n) = buildAppend (f n ∷ as) f n

build : ∀ {a} {A : Set a} → (ℕ → A) → ℕ → List A
build = buildAppend []
