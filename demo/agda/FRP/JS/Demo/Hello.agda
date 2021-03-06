open import FRP.JS.Behaviour using ( Beh ; [_] )
open import FRP.JS.DOM using ( DOM ; text )
open import FRP.JS.RSet using ( ⟦_⟧ )

module FRP.JS.Demo.Hello where

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = text ["Hello, world."]
