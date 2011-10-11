open import FRP.JS.Nat using ( ℕ ; _*_ )
open import FRP.JS.String using ( String )
open import FRP.JS.RSet using ( ⟦_⟧ ; ⟨_⟩ )
open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.Delay using ( Delay ; _ms ) renaming ( _+_ to _+d_ ; _∸_ to _∸d_ )

module FRP.JS.Time where

open import FRP.JS.Time.Core public using ( Time ; epoch )

postulate
  toUTCString : Time → String
  every : Delay → ⟦ Beh ⟨ Time ⟩ ⟧

{-# COMPILED_JS toUTCString function(t) { return require("agda.frp").date(t).toUTCString(); } #-}
{-# COMPILED_JS every function(d) { return function(t) { return require("agda.frp").every(d); }; } #-}

_+_ : Time → Delay → Time
epoch t + d = epoch (t +d d)

{-# COMPILED_JS _+_ function(d) { return function(e) { return d + e; }; } #-}

_∸_ : Time → Time → Delay
epoch t ∸ epoch u = t ∸d u

{-# COMPILED_JS _∸_ function(d) { return function(e) { return Math.min(0, d - e); }; } #-}
