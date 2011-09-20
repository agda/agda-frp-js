open import FRP.JS.Behaviour using ( Beh ; [_] ; hold )
open import FRP.JS.Event using ( tag )
open import FRP.JS.DOM using ( DOM ; text ; element ; listen ; click ; _++_ )
open import FRP.JS.RSet using ( ⟦_⟧ )

module FRP.JS.Demo.Button where

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = text lab ++ but where
  but = element "button" (text ["OK"])
  lab = hold "Press me: " (tag "Pressed: " (listen click but))
