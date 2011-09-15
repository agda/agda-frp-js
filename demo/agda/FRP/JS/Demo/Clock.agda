open import FRP.JS.Behaviour using ( Beh ; map )
open import FRP.JS.DOM using ( DOM ; text ; element )
open import FRP.JS.RSet using ( ⟦_⟧ )
open import FRP.JS.Time using ( toUTCString ; every ; _sec )
open import FRP.JS.Main using ( Main ; reactimate )

module FRP.JS.Demo.Clock where

clock : ⟦ Beh DOM ⟧
clock = element "p" (text (map toUTCString (every (1 sec))))

main : Main
main = reactimate clock
