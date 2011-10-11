open import FRP.JS.Bool using ( Bool ; _∨_ ; not )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe )
open import FRP.JS.Float using ( ℝ ) renaming ( _/?_ to _/?r_ )
open import FRP.JS.Primitive using ( ℕ ; String )

module FRP.JS.Int where

infixr 4 _≤_ _<_ _≟_
infixl 6 _+_ _-_
infixl 7 _*_ _/_ _/?_

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
  primNatToInteger    : ℕ → ℤ
  primFloatDiv        : ℝ → ℝ → ℝ

_+_   = primIntegerPlus
_-_   = primIntegerMinus
_*_   = primIntegerTimes
_%_   = primIntegerMod
_≟_  = primIntegerEquality
_<_   = primIntegerLess
float = primIntegerToFloat
abs   = primIntegerAbs
show  = primShowInteger

{-# COMPILED_JS _+_   function(x) { return function(y) { return x + y; }; } #-}
{-# COMPILED_JS _-_   function(x) { return function(y) { return x - y; }; } #-}
{-# COMPILED_JS _*_   function(x) { return function(y) { return x * y; }; } #-}
{-# COMPILED_JS _%_   function(x) { return function(y) { if (x < 0) { return (x % y) + x; } else { return x % y; } }; } #-}
{-# COMPILED_JS _≟_  function(x) { return function(y) { return x === y; }; } #-}
{-# COMPILED_JS _<_   function(x) { return function(y) { return x < y; }; } #-}
{-# COMPILED_JS float function(x) { return x; } #-}
{-# COMPILED_JS abs   function(x) { return Math.abs(x); } #-}
{-# COMPILED_JS show  function(x) { return x.toString(); } #-}

+0 = primNatToInteger 0
+1 = primNatToInteger 1
-1 = +0 - +1

-_ : ℤ → ℤ
- x = +0 - x

_≤_ : ℤ → ℤ → Bool
x ≤ y = (x < y) ∨ (x ≟ y)

_≠_ : ℤ → ℤ → Bool
x ≠ y = not (x ≟ y)

_/_ : (x y : ℤ) → {y≠0 : True (y ≠ +0)} → ℝ
x / y = primFloatDiv (float x) (float y)

_/?_ : ℤ → ℤ → Maybe ℝ
x /? y = (float x) /?r (float y)

{-# COMPILED_JS _/_ function(x) { return function(y) { return x / y; }; } #-}
{-# COMPILED_JS _≤_ function(x) { return function(y) { return x <= y; }; } #-}
{-# COMPILED_JS _≠_ function(x) { return function(y) { return x !== y; }; } #-}
{-# COMPILED_JS _/_  function(x) { return function(y) { return function() { return x / y; }; }; } #-}
{-# COMPILED_JS _/?_  function(x) { return function(y) { if (y === 0) { return null; } else { return x / y; } }; } #-}
