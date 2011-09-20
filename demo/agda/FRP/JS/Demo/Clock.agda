open import FRP.JS.Behaviour using ( Beh ; map )
open import FRP.JS.DOM using ( DOM ; text ; element )
open import FRP.JS.RSet using ( ⟦_⟧ )
open import FRP.JS.Time using ( toUTCString ; every ; _sec )

module FRP.JS.Demo.Clock where

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = text (map toUTCString (every (1 sec)))