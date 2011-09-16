open import FRP.JS.Geolocation.Angle using ( Angle ) renaming ( toString to toString° )
open import FRP.JS.String using ( String ; _++_ )

module FRP.JS.Geolocation.Coords where

-- Not including the optional fields yet.

record Coords : Set where
  field
    latitude : Angle
    longitude : Angle

open Coords public

toString : Coords → String
toString c = toString° (latitude c) ++ "," ++ toString° (longitude c)
