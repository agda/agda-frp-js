open import FRP.JS.Bool using ( Bool ; true ; false ; not ; _∨_ )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.Primitive using ( ℤ ; String )

module FRP.JS.Float where

infixr 4 _≤_ _<_ _≟_ _≠_
infixl 6 _+_ _-_
infixl 7 _*_ _/_ _/?_

open import FRP.JS.Primitive public using ( ℝ )

primitive
  primFloatPlus      : ℝ -> ℝ -> ℝ
  primFloatMinus     : ℝ -> ℝ -> ℝ
  primFloatTimes     : ℝ -> ℝ -> ℝ
  primFloatDiv       : ℝ -> ℝ -> ℝ
  primFloatLess      : ℝ -> ℝ -> Bool
  primFloor          : ℝ -> ℤ
  primCeiling        : ℝ -> ℤ
  primExp            : ℝ -> ℝ
  primLog            : ℝ -> ℝ
  primSin            : ℝ -> ℝ
  primShowFloat      : ℝ -> String
  primShowInteger    : ℤ → String
  primIntegerToFloat : ℤ → ℝ

_+_   = primFloatPlus
_-_   = primFloatMinus
_*_   = primFloatTimes
_<_   = primFloatLess
⌊_⌋   = primFloor
⌈_⌉   = primCeiling
exp   = primExp
log   = primLog
sin   = primSin

{-# COMPILED_JS _+_   function(x) { return function(y) { return x + y; }; } #-}
{-# COMPILED_JS _-_   function(x) { return function(y) { return x - y; }; } #-}
{-# COMPILED_JS _*_   function(x) { return function(y) { return x * y; }; } #-}
{-# COMPILED_JS _<_   function(x) { return function(y) { return x < y; }; } #-}
{-# COMPILED_JS ⌊_⌋   Math.floor #-}
{-# COMPILED_JS ⌈_⌉   Math.ceil #-}
{-# COMPILED_JS exp   Math.exp #-}
{-# COMPILED_JS log   Math.log #-}
{-# COMPILED_JS sin   Math.sin #-}

-_ : ℝ → ℝ
- x = 0.0 - x

_≠_ : ℝ → ℝ → Bool
(x ≠ y) = (x < y) ∨ (y < x)

_≟_ : ℝ → ℝ → Bool
(x ≟ y) = not (x ≠ y)

_≤_ : ℝ → ℝ → Bool
(x ≤ y) = not (y < x)

-- Some hoop-jumping to avoid division by zero, so we don't end up with
-- Infinity, -Infinity or NaN.

_/_ : (x y : ℝ) → {y≠0 : True (y ≠ 0.0)} → ℝ
x / y = primFloatDiv x y

_/?_ : ℝ → ℝ → Maybe ℝ
x /? 0.0 = nothing
x /? y   = just (primFloatDiv x y)

show : ℝ → String
show x 
 with (x ≟ primIntegerToFloat ⌊ x ⌋)
... | true  = primShowInteger ⌊ x ⌋
... | false = primShowFloat x

{-# COMPILED_JS -_   function(x) { return -x; } #-}
{-# COMPILED_JS _≠_ function(x) { return function(y) { return x !== y; }; } #-}
{-# COMPILED_JS _≟_ function(x) { return function(y) { return x === y; }; } #-}
{-# COMPILED_JS _≤_  function(x) { return function(y) { return x <= y; }; } #-}
{-# COMPILED_JS _/_  function(x) { return function(y) { return function() { return x / y; }; }; } #-}
{-# COMPILED_JS _/?_  function(x) { return function(y) { if (y === 0) { return null; } else { return x / y; } }; } #-}
{-# COMPILED_JS show  function(x) { return x.toString(); } #-}


