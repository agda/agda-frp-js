open import FRP.JS.Nat using ( ℕ ; float ) renaming 
  ( _+_ to _+n_ ; _∸_ to _∸n_ ; _*_ to _*n_ ; _≟_ to _≟n_ ; _≠_ to _≠n_
  ; _/_ to _/n_ ; _/?_ to _/?n_ ; _≤_ to _≤n_ ; _<_ to _<n_ )
open import FRP.JS.Float using ( ℝ )
open import FRP.JS.Bool using ( Bool )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe )

module FRP.JS.Delay where

record Delay : Set where
  constructor _ms
  field toℕ : ℕ

{-# COMPILED_JS Delay function(x,v) { return v["_ms"](x); } #-}
{-# COMPILED_JS _ms function(d) { return d; } #-}

_≟_ : Delay → Delay → Bool
(d ms) ≟ (e ms) = d ≟n e

{-# COMPILED_JS _≟_ function(d) { return function(e) { return d === e; }; } #-}

_≠_ : Delay → Delay → Bool
(d ms) ≠ (e ms) = d ≠n e

{-# COMPILED_JS _≠_ function(d) { return function(e) { return d !== e; }; } #-}

_≤_ : Delay → Delay → Bool
(d ms) ≤ (e ms) = d ≤n e

{-# COMPILED_JS _≤_ function(d) { return function(e) { return d <= e; }; } #-}

_<_ : Delay → Delay → Bool
(d ms) < (e ms) = d <n e

{-# COMPILED_JS _<_ function(d) { return function(e) { return d < e; }; } #-}

_+_ : Delay → Delay → Delay
(d ms) + (e ms) = (d +n e) ms

{-# COMPILED_JS _+_ function(d) { return function(e) { return d + e; }; } #-}

_∸_ : Delay → Delay → Delay
(d ms) ∸ (e ms) = (d ∸n e) ms

{-# COMPILED_JS _∸_ function(d) { return function(e) { return Math.min(0, d - e); }; } #-}

_*_ : ℕ → Delay → Delay
n * (d ms) = (n *n d) ms

{-# COMPILED_JS _*_ function(n) { return function(d) { return n * d; }; } #-}

_/_ : ∀ (d e : Delay) → {e≠0 : True (e ≠ 0 ms)} → ℝ
_/_ (d ms) (e ms) {e≠0} = _/n_ d e {e≠0}

{-# COMPILED_JS _/_ function(d) { return function(e) { return function() { return d / e; }; }; } #-}

_/?_ : Delay → Delay → Maybe ℝ
(d ms) /? (e ms) = d /?n e

{-# COMPILED_JS _/?_ function(d) { return function(e) { if (e === 0) { return null; } else { return d / e; } }; } #-}

_sec : ℕ → Delay
n sec = n * (1000 ms)

{-# COMPILED_JS _sec function(t) { return t * 1000; } #-}

_min : ℕ → Delay
n min = n * (60000 ms)

{-# COMPILED_JS _min function(t) { return t * 60000; } #-}
