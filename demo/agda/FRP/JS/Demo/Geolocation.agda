open import FRP.JS.Behaviour using ( Beh ; map ; [_] )
open import FRP.JS.DOM using ( DOM ; text ; _++_ )
open import FRP.JS.RSet using ( ⟦_⟧ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.String using ( String )
open import FRP.JS.Geolocation using ( geolocation )
open import FRP.JS.Geolocation.Coords using ( Coords ; toString )

module FRP.JS.Demo.Geolocation where

show : Maybe Coords → String
show nothing       = "unknown"
show (just coords) = toString coords

main : ⟦ Beh DOM ⟧
main = 
  text ["Current location: "] ++
  text (map show geolocation) ++
  text ["."]