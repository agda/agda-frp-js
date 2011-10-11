open import FRP.JS.List using ( List ; [] ; _∷_ ; build ) renaming ( length to llength )
open import FRP.JS.Char using ( Char ) renaming ( _<_ to _<C_ ; _≟_ to _≟C_ )
open import FRP.JS.Nat using ( ℕ )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ ; _∨_ )

module FRP.JS.String where

infixr 5 _++_
infix 4 _≟_

open import FRP.JS.Primitive public using ( String )

private
 primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primStringToList : String → List Char

_++_ : String → String → String
_++_ = primStringAppend

{-# COMPILED_JS _++_ function(x) { return function(y) { return x + y; }; } #-}

_≟_ : String → String → Bool
_≟_ = primStringEquality

{-# COMPILED_JS _≟_ function(x) { return function(y) { return x === y; }; } #-}

buildChars : (ℕ → Char) → ℕ → List Char
buildChars = build

toList : String → List Char
toList = primStringToList

{-# COMPILED_JS toList function(s) { 
  return exports.buildChars(function(n) { return s.charAt(n); },s.length);
} #-}

length : String → ℕ
length s = llength (toList s)

{-# COMPILED_JS length function(s) { return s.length; } #-}

_<*_ : List Char → List Char → Bool
as       <* []       = false
[]       <* (b ∷ bs) = true
(a ∷ as) <* (b ∷ bs) = (a <C b) ∨ ((a ≟C b) ∧ (as <* bs))

_<_ : String → String → Bool
s < t = toList s <* toList t

{-# COMPILED_JS _<_ function(x) { return function(y) { return x < y; }; } #-}

_≤_ : String → String → Bool
s ≤ t = (s ≟ t) ∨ (s < t)

{-# COMPILED_JS _≤_ function(x) { return function(y) { return x <= y; }; } #-}
