open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; cong )

module FRP.JS.Model.List where

infixr 4 _+_ _++_

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

record Seq (A : Set) : Set where
  constructor seq
  field
    list : List A
    fun : List A → List A
    .ok : fun ≡ _++_ list

open Seq public using () renaming (list to [_])

id : ∀ {A : Set} → A → A
id a = a

ε : ∀ {A} → Seq A
ε = seq [] id refl

⟨_⟩ : ∀ {A} → A → Seq A
⟨ a ⟩ = seq (a ∷ []) (_∷_ a) refl

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

∘✓ : ∀ {A f g} (as bs : List A) → (f ≡ _++_ as) → (g ≡ _++_ bs) → ((f ∘ g) ≡ _++_ (f bs))
∘✓ []       bs refl refl = refl
∘✓ (a ∷ as) bs refl refl = cong (_∘_ (_∷_ a)) (∘✓ as bs refl refl)

_+_ : ∀ {A} → Seq A → Seq A → Seq A
(seq as f f✓) + (seq bs g g✓) = seq (f bs) (f ∘ g) (∘✓ as bs f✓ g✓)

_◁_ : ∀ {A} → A → Seq A → Seq A
a ◁ as = ⟨ a ⟩ + as

+-unit₁ : ∀ {A} (as : Seq A) → ((ε + as) ≡ as)
+-unit₁ as = refl

+-assoc : ∀ {A} (as bs cs : Seq A) → ((as + bs) + cs) ≡ (as + (bs + cs))
+-assoc as bs cs = refl

data Case {A : Set} : Seq A → Set where
  [] : Case ε
  _∷_ : ∀ a as → Case (a ◁ as)

case : ∀ {A} (as : Seq A) → Case as
case (seq as       f                f✓) with ≡-irrel f✓
case (seq []       .(_++_ [])       f✓) | refl = []
case (seq (a ∷ as) .(_++_ (a ∷ as)) f✓) | refl = a ∷ (seq as (_++_ as) refl)

ids : ∀ {A} → Seq A → Seq A
ids as with case as
ids .(a ◁ as) | a ∷ as = a ◁ ids as
ids .ε        | []     = ε

data _∈_ {A} (a : A) : List A → Set where
  here : ∀ {as} → a ∈ (a ∷ as)
  there : ∀ {b bs} → a ∈ bs → a ∈ (b ∷ bs)

weakening : ∀ {A a} (as bs cs : Seq A) → (a ∈ [ as + cs ]) → (a ∈ [ as + bs + cs ])
weakening as        bs        cs a∈as+cs         with case as
weakening .(a ◁ as) bs        cs here            | (a ∷ as)      = here
weakening .(a ◁ as) bs        cs (there a∈as+cs) | (a ∷ as)      = there (weakening as bs cs a∈as+cs)
weakening .ε        bs        cs a∈cs            | [] with case bs
weakening .ε        .(b ◁ bs) cs a∈cs            | [] | (b ∷ bs) = there (weakening ε bs cs a∈cs)
weakening .ε        .ε        cs a∈cs            | [] | []       = a∈cs
