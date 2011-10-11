open import FRP.JS.Nat using ( ℕ ; float ) renaming ( _+_ to _+n_ ; _∸_ to _∸n_ ; _*_ to _*n_ )
open import FRP.JS.Float using ( ℝ ) renaming ( _/_ to _/r_ )

module FRP.JS.Delay where

data Delay : Set where
  _ms : ℕ → Delay

{-# COMPILED_JS Delay function(x,v) { return v["_ms"](x); } #-}
{-# COMPILED_JS _ms function(d) { return d; } #-}

_+_ : Delay → Delay → Delay
(d ms) + (e ms) = (d +n e) ms

{-# COMPILED_JS _+_ function(d) { return function(e) { return d + e; }; } #-}

_∸_ : Delay → Delay → Delay
(d ms) ∸ (e ms) = (d ∸n e) ms

{-# COMPILED_JS _∸_ function(d) { return function(e) { return Math.min(0, d - e); }; } #-}

_*_ : ℕ → Delay → Delay
n * (d ms) = (n *n d) ms

{-# COMPILED_JS _*_ function(n) { return function(d) { return n * d; }; } #-}

_/_ : Delay → Delay → ℝ
(d ms) / (e ms) = float d /r float d

{-# COMPILED_JS _*_ function(n) { return function(d) { return n * d; }; } #-}

_sec : ℕ → Delay
n sec = n * (1000 ms)

{-# COMPILED_JS _sec function(t) { return t * 1000; } #-}

_min : ℕ → Delay
n min = n * (60000 ms)

{-# COMPILED_JS _min function(t) { return t * 60000; } #-}
