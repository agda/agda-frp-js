open import FRP.JS.Nat using ( ℕ ) renaming ( _<_ to _<N_ ; _≤_ to _≤N_ )
open import FRP.JS.Bool using ( Bool ; true ; false )

module FRP.JS.Char where

infix 4 _==_ _<_

open import FRP.JS.Primitive public using ( Char )

private
 primitive
  primCharToNat    : Char → ℕ
  primCharEquality : Char → Char → Bool

toNat : Char → ℕ
toNat = primCharToNat

{-# COMPILED_JS toNat function(c) { return c.charCodeAt(0); } #-}

_==_ : Char → Char → Bool
_==_ = primCharEquality

{-# COMPILED_JS _==_ function(c) { return function(d) { return c === d; }; } #-}

_<_ : Char → Char → Bool
c < d = toNat c <N toNat d

{-# COMPILED_JS _<_ function(c) { return function(d) { return c < d; }; } #-}

_≤_ : Char → Char → Bool
c ≤ d = toNat c ≤N toNat d

{-# COMPILED_JS _≤_ function(c) { return function(d) { return c <= d; }; } #-}
