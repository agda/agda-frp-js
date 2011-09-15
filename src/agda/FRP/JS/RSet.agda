open import FRP.JS.Time.Core using ( Time )

module FRP.JS.RSet where

infixr 4 _⇒_

RSet : Set₁
RSet = Time → Set

_⇒_ : RSet → RSet → RSet
(A ⇒ B) t = A t → B t

⟨_⟩ : Set → RSet
⟨ A ⟩ t = A

⟦_⟧ : RSet → Set
⟦ A ⟧ = ∀ {t} → A t
