open import FRP.JS.RSet using ( RSet ; ⟦_⟧ ; _⇒_ )
open import FRP.JS.Time using ( Time )

module FRP.JS.Product where

-- We define _∧_ directly, rather than as λ t → (A t × B t)
-- in order to make _∧_ invertable. (If we used the obvious defn,
-- (A ∧ B) would only be invertable if A and B were invertable.

infixr 2 _∧_
infixr 4 _,_

data _∧_ (A B : RSet) (t : Time) : Set where
  _,_ : A t → B t → (A ∧ B) t

proj₁ : ∀ {A B} → ⟦ A ∧ B ⇒ A ⟧
proj₁ (a , b) = a

proj₂ : ∀ {A B} → ⟦ A ∧ B ⇒ B ⟧
proj₂ (a , b) = b

swap : ∀ {A B} →  ⟦ A ∧ B ⇒ B ∧ A ⟧
swap (a , b) = (b , a)
