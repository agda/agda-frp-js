open import FRP.JS.String using ( String )
open import FRP.JS.Time using ( Time )

module FRP.JS.Date where

postulate
  Date : Set
  fromTime : Time → Date
  toTime : Date → Time
  toString : Date → String
  toUTCString : Date → String

{-# COMPILED_JS fromTime require("agda-frp-time").date #-}
{-# COMPILED_JS toTime function(d) { return d.getTime(); } #-}
{-# COMPILED_JS toString function(d) { return d.toString(); } #-}
{-# COMPILED_JS toUTCString function(d) { return d.toUTCString(); } #-}

