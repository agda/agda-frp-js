open import FRP.JS.Bool using ( Bool ; _∨_ )

module FRP.JS.Nat where

infixr 4 _≤_ _<_ _==_
infixl 6 _+_
infixl 7 _*_

-- Data.Nat doesn't have bindings for JavaScript, so we define ℕ here.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

{-# COMPILED_JS ℕ function (x,v) {
  if (x < 1) { return v.zero(); } else { return v.suc(x-1); }
} #-}
{-# COMPILED_JS zero 0 #-}
{-# COMPILED_JS suc function (x) { return x+1; } #-}


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

_==_ : ℕ → ℕ → Bool
_==_ = primNatEquality

{-# COMPILED_JS _==_ function (x) { return function (y) { return x===y; }; } #-}

_<_ : ℕ → ℕ → Bool
_<_ = primNatLess

{-# COMPILED_JS _<_ function (x) { return function (y) { return x<y; }; } #-}

_≤_ : ℕ → ℕ → Bool
x ≤ y = (x < y) ∨ (x == y)

{-# COMPILED_JS _≤_ function (x) { return function (y) { return x<=y; }; } #-}
