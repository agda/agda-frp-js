open import FRP.JS.Bool using ( Bool ; not ; _∨_ )
open import FRP.JS.Primitive using ( ℤ ; String )

module FRP.JS.Float where

open import FRP.JS.Primitive public using ( ℝ )

-- Note that ℝ includes -Infinity, NaN and Infinity
-- which are the results of -1.0/0.0, 0.0/0.0 and 1.0/0.0
-- respectively.

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

_+_   = primFloatPlus
_-_   = primFloatMinus
_*_   = primFloatTimes
_/_   = primFloatDiv
_<_   = primFloatLess
⌊_⌋   = primFloor
⌈_⌉   = primCeiling
exp   = primExp
log   = primLog
sin   = primSin
show  = primShowFloat

{-# COMPILED_JS _+_   function(x) { return function(y) { return x + y; }; } #-}
{-# COMPILED_JS _-_   function(x) { return function(y) { return x - y; }; } #-}
{-# COMPILED_JS _*_   function(x) { return function(y) { return x * y; }; } #-}
{-# COMPILED_JS _/_   function(x) { return function(y) { return x / y; }; } #-}
{-# COMPILED_JS _<_   function(x) { return function(y) { return x < y; }; } #-}
{-# COMPILED_JS ⌊_⌋   Math.floor #-}
{-# COMPILED_JS ⌈_⌉   Math.ceil #-}
{-# COMPILED_JS exp   Math.exp #-}
{-# COMPILED_JS log   Math.log #-}
{-# COMPILED_JS sin   Math.sin #-}
{-# COMPILED_JS show  function(x) { return x.toString(); } #-}

-_ : ℝ → ℝ
- x = 0.0 - x

_!=_ : ℝ → ℝ → Bool
(x != y) = (x < y) ∨ (y < x)

_==_ : ℝ → ℝ → Bool
(x == y) = not (x != y)

{-# COMPILED_JS -_ function(x) { return -x; } #-}
{-# COMPILED_JS _!=_ function(x) { return function(y) { return x !== y; }; } #-}
{-# COMPILED_JS _==_ function(x) { return function(y) { return x === y; }; } #-}
