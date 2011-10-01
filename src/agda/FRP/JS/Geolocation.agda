-- Partial Agda bindings for the W3C Geolocation API
-- http://dev.w3.org/geo/api/spec-source.html
-- Not supporting the "read once" API or any of the options yet.

open import FRP.JS.Behaviour using ( Beh ; map )
open import FRP.JS.Geolocation.Coords using ( Coords )
open import FRP.JS.Maybe using ( Maybe )
open import FRP.JS.RSet using ( ⟦_⟧ ; ⟨_⟩ )

module FRP.JS.Geolocation where

postulate
  geolocation : ⟦ Beh ⟨ Maybe Coords ⟩ ⟧

{-# COMPILED_JS geolocation require("agda.frp").geolocation #-}
