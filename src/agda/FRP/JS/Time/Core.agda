open import FRP.JS.Nat using ( ℕ ; _*_ )
open import FRP.JS.String using ( String )

module FRP.JS.Time.Core where

postulate
  Time : Set
  Delay : Set
  _ms : ℕ → Delay

{-# COMPILED_JS _ms function (x) { return x; } #-}
