open import FRP.JS.Delay using ( Delay )

module FRP.JS.Time.Core where

data Time : Set where
  epoch : Delay → Time

{-# COMPILED_JS Time function(x,v) { return v.epoch(x); } #-}
{-# COMPILED_JS epoch function(d) { return d; } #-}
