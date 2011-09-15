open import FRP.JS.RSet using ( ⟦_⟧ )
open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.DOM using ( DOM )

module FRP.JS.Main where

postulate
  Main : Set
  reactimate : ⟦ Beh DOM ⟧ → Main

{-# COMPILED_JS reactimate require("agda.frp").reactimate #-}
