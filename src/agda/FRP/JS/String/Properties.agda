open import FRP.JS.String using ( _<_ )
open import FRP.JS.True using ( True )

module FRP.JS.String.Properties where

postulate
  <-trans : ∀ {k l m} → True (k < l) → True (l < m) → True (k < m)
