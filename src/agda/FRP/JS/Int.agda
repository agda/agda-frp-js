open import FRP.JS.Nat using ( ℕ )
open import FRP.JS.Bool using ( Bool )
open import FRP.JS.String using ( String )

module FRP.JS.Int where

postulate
  ℤ : Set

{-# BUILTIN INTEGER ℤ #-}

private
 primitive
  primIntegerPlus     : ℤ -> ℤ -> ℤ
  primIntegerMinus    : ℤ -> ℤ -> ℤ
  primIntegerTimes    : ℤ -> ℤ -> ℤ
  primIntegerDiv      : ℤ -> ℤ -> ℤ
  primIntegerMod      : ℤ -> ℤ -> ℤ
  primIntegerEquality : ℤ -> ℤ -> Bool
  primIntegerLess     : ℤ -> ℤ -> Bool
  primNatToInteger    : ℕ -> ℤ
  primShowInteger     : ℤ -> String

_+_  = primIntegerPlus
_-_  = primIntegerMinus
_*_  = primIntegerTimes
_%_  = primIntegerMod
_==_ = primIntegerEquality
_<_  = primIntegerLess
+_   = primNatToInteger
show = primShowInteger

{-# COMPILED_JS _+_  function(x) { return function(y) { return x + y; }; } #-}
{-# COMPILED_JS _-_  function(x) { return function(y) { return x - y; }; } #-}
{-# COMPILED_JS _*_  function(x) { return function(y) { return x * y; }; } #-}
{-# COMPILED_JS _%_  function(x) { return function(y) { if (x < 0) { return (x % y) + x; } else { return x % y; } }; } #-}
{-# COMPILED_JS _==_ function(x) { return function(y) { return x === y; }; } #-}
{-# COMPILED_JS _<_  function(x) { return function(y) { return x < y; }; } #-}
{-# COMPILED_JS +_   function(x) { return x; } #-}
{-# COMPILED_JS show function(x) { return x.toString(); } #-}

+0 : ℤ
+0 = (+ 0)

-_ : ℕ → ℤ
-_ x = (+ 0) - (+ x)

{-# COMPILED_JS +0 0 #-}
{-# COMPILED_JS -_  function(x) { return -x; } #-}
