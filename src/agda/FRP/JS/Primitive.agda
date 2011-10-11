open import FRP.JS.Level using ()

module FRP.JS.Primitive where

-- We define the primitive types here, to avoid cyclic module dependencies

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_JS Bool function(x,v) { if (x) { return v["true"](); } else { return v["false"](); } } #-}
{-# COMPILED_JS true true #-}
{-# COMPILED_JS false false #-}

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

postulate
  Char String ℝ ℤ : Set

{-# BUILTIN CHAR    Char #-}
{-# BUILTIN STRING  String #-}
{-# BUILTIN FLOAT   ℝ #-}
{-# BUILTIN INTEGER ℤ #-}
