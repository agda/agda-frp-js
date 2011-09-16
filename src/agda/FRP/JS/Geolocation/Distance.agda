open import FRP.JS.Nat using ( ℕ )
open import FRP.JS.String using ( String )

module FRP.JS.Geolocation.Distance where

postulate
  Distance : Set
  _m : ℕ → Distance
  toString : Distance → String

{-# COMPILED_JS _m function(x) { return x; } #-}
{-# COMPILED_JS toString function(x) { return x.toString(); } #-}
