open import FRP.JS.Nat using ( ℕ )
open import FRP.JS.String using ( String )

module FRP.JS.Geolocation.Angle where

postulate
  Angle : Set
  _° : ℕ → Angle
  _′ : ℕ → Angle
  _″ : ℕ → Angle
  _+_ : Angle → Angle → Angle
  toString : Angle → String

{-# COMPILED_JS _° function(x) { return ((x + 180) % 360) - 180; } #-}
{-# COMPILED_JS _′ function(x) { return (((x / 60) + 180) % 360) - 180; } #-}
{-# COMPILED_JS _″ function(x) { return (((x / 3600) + 180) % 360) - 180; } #-}
{-# COMPILED_JS _+_ function(x) { return function (y) { return x + y; }; } #-}
{-# COMPILED_JS toString function(x) { return x.toString(); } #-}
