open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.DOM using ( DOM )
open import FRP.JS.RSet using ( ⟦_⟧ )
open import FRP.JS.Demo.Calculator.View using ( view )

module FRP.JS.Demo.Calculator where

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = view