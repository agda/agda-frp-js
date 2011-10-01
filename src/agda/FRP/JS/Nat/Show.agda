open import FRP.JS.Nat using ( ℕ ; _≤_ )
open import FRP.JS.String using ( String )
open import FRP.JS.True using ( True )

module FRP.JS.Nat.Show where

postulate
  showInBase : (base : ℕ)
     {base≥2 : True (2 ≤ base)}
     {base≤16 : True (base ≤ 16)} →
     ℕ → String
  show : ℕ → String

{-# COMPILED_JS showInBase function (b) { 
  return function() { return function() { return function(n) { 
    return n.toString(b); 
  }; }; };
} #-}

{-# COMPILED_JS show function(n) { return n.toString(); } #-}
