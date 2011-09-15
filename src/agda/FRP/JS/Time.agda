open import FRP.JS.Nat using ( ℕ ; _*_ )
open import FRP.JS.String using ( String )
open import FRP.JS.RSet using ( ⟦_⟧ ; ⟨_⟩ )
open import FRP.JS.Behaviour using ( Beh )

module FRP.JS.Time where

open import FRP.JS.Time.Core public using ( Time ; Delay ; _ms )

postulate
  toUTCString : Time → String
  every : Delay → ⟦ Beh ⟨ Time ⟩ ⟧

{-# COMPILED_JS toUTCString function(t) { return require("agda.frp").date(t).toUTCString(); } #-}
{-# COMPILED_JS every function(d) { return function(t) { return require("agda.frp").every(d); }; } #-}

_sec : ℕ → Delay
n sec = (n * 1000) ms

_min : ℕ → Delay
n min = (n * 60000) ms

{-# COMPILED_JS _sec function(t) { return t * 1000; } #-}
{-# COMPILED_JS _min function(t) { return t * 60000; } #-}
