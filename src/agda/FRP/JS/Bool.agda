module FRP.JS.Bool where

open import FRP.JS.Primitive public using ( Bool ; true ; false )

not : Bool → Bool
not true  = false
not false = true

{-# COMPILED_JS not function(x) { return !x; } #-}

_≟_ : Bool → Bool → Bool
true  ≟ b = b
false ≟ b = not b

{-# COMPILED_JS _≟_ function(x) { return function(y) { return x === y; }; } #-}

if_then_else_ : ∀ {α} {A : Set α} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

{-# COMPILED_JS if_then_else_ function(a) { return function(A) { return function(x) {
  if (x) { return function(t) { return function(f) { return t; }; }; }
  else { return function(t) { return function(f) { return f; }; }; }
}; }; } #-}

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

{-# COMPILED_JS _∧_ function(x) { return function(y) { return x && y; }; } #-}

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

{-# COMPILED_JS _∨_ function(x) { return function(y) { return x || y; }; } #-}

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

_≠_ = _xor_

{-# COMPILED_JS _xor_ function(x) { return function(y) { return x !== y; }; } #-}
{-# COMPILED_JS _≠_ function(x) { return function(y) { return x !== y; }; } #-}
