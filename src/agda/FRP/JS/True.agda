{-# OPTIONS --universe-polymorphism #-}

open import FRP.JS.Bool using ( Bool ; true ; false ; if_then_else_ ; not ; _∧_ )

module FRP.JS.True where

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

contradiction : ∀ {α} {A : Set α} → ⊥ → A
contradiction ()

True : Bool → Set
True true = ⊤
True false = ⊥

False : Bool → Set
False b = True b → ⊥

∧-intro : ∀ {a b} → True a → True b → True (a ∧ b)
∧-intro {false}         () b
∧-intro {true}  {false} tt ()
∧-intro {true}  {true}  tt tt = tt

∧-elim₁ : ∀ {a b} → True (a ∧ b) → True a
∧-elim₁ {false} ()
∧-elim₁ {true}  b  = tt

∧-elim₂ : ∀ {a b} → True (a ∧ b) → True b
∧-elim₂ {false} ()
∧-elim₂ {true}  b  = b

data Dec (b : Bool) : Set where
  yes : True b → Dec b
  no  : False b → Dec b

{-# COMPILED_JS Dec function(x,v) {
  if (x) { return v.yes(null); } else { return v.no(null); } 
} #-}
{-# COMPILED_JS yes true #-}
{-# COMPILED_JS no false #-}

dec : ∀ b → Dec b
dec true  = yes tt
dec false = no contradiction
