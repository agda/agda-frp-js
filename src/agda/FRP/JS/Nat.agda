open import FRP.JS.Float using ( ℝ ) renaming ( _/?_ to _/?r_ )
open import FRP.JS.Int using ( ℤ ; _-_ ) renaming ( float to floatz ; show to showz )
open import FRP.JS.Primitive using ( String )
open import FRP.JS.Bool using ( Bool ; _∨_ ; not )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe )

module FRP.JS.Nat where

infixr 4 _≤_ _<_ _≟_ _≠_
infixl 6 _+_ _∸_
infixl 7 _*_ _/_ _/?_

open import FRP.JS.Primitive public using ( ℕ ; zero ; suc )

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}
{-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}

_∸_ : ℕ → ℕ → ℕ
zero  ∸ n     = zero
suc m ∸ zero  = suc m
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}
{-# COMPILED_JS _∸_ function (x) { return function (y) { return Math.max(0,x-y); }; } #-}

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

{-# BUILTIN NATTIMES _*_ #-}
{-# COMPILED_JS _*_ function (x) { return function (y) { return x*y; }; } #-}

private
 primitive
  primNatEquality : ℕ → ℕ → Bool
  primNatLess : ℕ → ℕ → Bool
  primNatToInteger : ℕ → ℤ
  primFloatDiv : ℝ → ℝ → ℝ

_≟_ = primNatEquality
_<_ = primNatLess
+_ = primNatToInteger

{-# COMPILED_JS _≟_ function (x) { return function (y) { return x === y; }; } #-}
{-# COMPILED_JS _<_ function (x) { return function (y) { return x < y; }; } #-}
{-# COMPILED_JS +_ function (x) { return x; } #-}

float : ℕ → ℝ
float x = floatz (+ x)

show : ℕ → String
show x = showz (+ x)

-_ : ℕ → ℤ
-_ x = (+ 0) - (+ x)

_≤_ : ℕ → ℕ → Bool
x ≤ y = (x < y) ∨ (x ≟ y)

_≠_ : ℕ → ℕ → Bool
x ≠ y = not (x ≟ y)

_/_ : (x y : ℕ) → {y≠0 : True (y ≠ 0)} → ℝ
x / y = primFloatDiv (float x) (float y)

_/?_ : ℕ → ℕ → Maybe ℝ
x /? y = (float x) /?r (float y)

{-# COMPILED_JS float function (x) { return x; } #-}
{-# COMPILED_JS show function (x) { return x.toString(); } #-}
{-# COMPILED_JS -_ function (x) { return -x; } #-}
{-# COMPILED_JS _≤_ function (x) { return function (y) { return x <= y; }; } #-}
{-# COMPILED_JS _≠_ function (x) { return function (y) { return x !== y; }; } #-}
{-# COMPILED_JS _/_  function(x) { return function(y) { return function() { return x / y; }; }; } #-}
{-# COMPILED_JS _/?_  function(x) { return function(y) { if (y === 0) { return null; } else { return x / y; } }; } #-}
