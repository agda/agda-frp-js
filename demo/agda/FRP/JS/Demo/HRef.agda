open import FRP.JS.Behaviour using ( Beh ; [_] )
open import FRP.JS.DOM using ( DOM ; element ; attr ; text ; _++_ )
open import FRP.JS.RSet using ( ⟦_⟧ )

module FRP.JS.Demo.HRef where

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = element ("a") 
  ( attr "href" ["http://bell-labs.com/"] ++
    text ["A hyperlink."] )
