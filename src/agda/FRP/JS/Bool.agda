{-# OPTIONS --universe-polymorphism #-}

import FRP.JS.Level

module FRP.JS.Bool where

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_JS Bool function(x,v) { if (x) { return v["true"](); } else { return v["false"](); } } #-}
{-# COMPILED_JS true true #-}
{-# COMPILED_JS false false #-}

not : Bool → Bool
not true  = false
not false = true

{-# COMPILED_JS not function(x) { return !x; } #-}

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

{-# COMPILED_JS _xor_ function(x) { return function(y) { return x ^ y; }; } #-}
