open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; subst ; cong )

module FRP.JS.Model.List where

infixr 4 _++_

postulate
  ≡-irrel : ∀ {A : Set} {a b : A} → .(a ≡ b) → (a ≡ b)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : ∀ {A} → List A → List A → List A
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

++-unit : ∀ {A} (as : List A) → (as ++ []) ≡ as
++-unit []       = refl
++-unit (a ∷ as) = cong (_∷_ a) (++-unit as)

++-assoc : ∀ {A} (as bs cs : List A) → ((as ++ bs) ++ cs) ≡ (as ++ (bs ++ cs))
++-assoc []       bs cs = refl
++-assoc (a ∷ as) bs cs = cong (_∷_ a) (++-assoc as bs cs)
