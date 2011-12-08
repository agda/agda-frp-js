open import FRP.JS.Delay using ( Delay )

module FRP.JS.Time.Core where

record Time : Set where
  constructor epoch
  field toDelay : Delay

{-# COMPILED_JS Time function(x,v) { return v.epoch(x); } #-}
{-# COMPILED_JS epoch function(d) { return d; } #-}
