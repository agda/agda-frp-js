open import FRP.JS.Bool using ( Bool ; _∨_ )
open import FRP.JS.Float using ( ℝ ) renaming ( _/_ to _/r_ )
open import FRP.JS.Primitive using ( ℕ ; String )

module FRP.JS.Int where

open import FRP.JS.Primitive public using ( ℤ )

private
 primitive
  primIntegerPlus     : ℤ -> ℤ -> ℤ
  primIntegerMinus    : ℤ -> ℤ -> ℤ
  primIntegerTimes    : ℤ -> ℤ -> ℤ
  primIntegerDiv      : ℤ -> ℤ -> ℤ
  primIntegerMod      : ℤ -> ℤ -> ℤ
  primIntegerEquality : ℤ -> ℤ -> Bool
  primIntegerLess     : ℤ -> ℤ -> Bool
  primIntegerToFloat  : ℤ -> ℝ
  primIntegerAbs      : ℤ -> ℕ
  primShowInteger     : ℤ -> String

_+_   = primIntegerPlus
_-_   = primIntegerMinus
_*_   = primIntegerTimes
_%_   = primIntegerMod
_==_  = primIntegerEquality
_<_   = primIntegerLess
float = primIntegerToFloat
abs   = primIntegerAbs
show  = primShowInteger

{-# COMPILED_JS _+_   function(x) { return function(y) { return x + y; }; } #-}
{-# COMPILED_JS _-_   function(x) { return function(y) { return x - y; }; } #-}
{-# COMPILED_JS _*_   function(x) { return function(y) { return x * y; }; } #-}
{-# COMPILED_JS _%_   function(x) { return function(y) { if (x < 0) { return (x % y) + x; } else { return x % y; } }; } #-}
{-# COMPILED_JS _==_  function(x) { return function(y) { return x === y; }; } #-}
{-# COMPILED_JS _<_   function(x) { return function(y) { return x < y; }; } #-}
{-# COMPILED_JS float function(x) { return x; } #-}
{-# COMPILED_JS abs   function(x) { return Math.abs(x); } #-}
{-# COMPILED_JS show  function(x) { return x.toString(); } #-}

_/_ : ℤ → ℤ → ℝ
x / y = float x /r float y

_≤_ : ℤ → ℤ → Bool
x ≤ y = (x < y) ∨ (x == y)

{-# COMPILED_JS _/_ function(x) { return function(y) { return x / y; }; } #-}
{-# COMPILED_JS _≤_ function(x) { return function(y) { return x <= y; }; } #-}
