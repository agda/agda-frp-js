open import FRP.JS.Nat using ( ℕ ; _+_ ; _≤_ ; _<_ ; _≟_ )
open import FRP.JS.True using ( True ; False )

module FRP.JS.Nat.Properties where

postulate
  ≤-impl-≯ : ∀ {m n} → True (m ≤ n) → False (n < m)
  ≤≠-impl-< : ∀ {m n} → True (m ≤ n) → False (m ≟ n) → True (m < n)
  <-impl-s≤ : ∀ {m n} → True (m < n) → True (1 + m ≤ n)
  ≤-bot : ∀ {n} → True (0 ≤ n)
