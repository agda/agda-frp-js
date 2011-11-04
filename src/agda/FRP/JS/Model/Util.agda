open import FRP.JS.Level using ( _⊔_ )

module FRP.JS.Model.Util where

infixr 5 _,_
infixr 4 _∘_

id : ∀ {A : Set} → A → A
id a = a

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

data ⊥ {α} : Set α where

record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A × B = Σ A (λ a → B)

data _≡_ {α} {A : Set α} (a : A) : A → Set α where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

sym :  ∀ {α} {A : Set α} {a b : A} →
  (a ≡ b) → (b ≡ a)
sym refl = refl

trans :  ∀ {α} {A : Set α} {a b c : A} →
  (a ≡ b) → (b ≡ c) → (a ≡ c)
trans refl refl = refl

subst :  ∀ {α β} {A : Set α} (B : A → Set β) {a b} →
  (a ≡ b) → B a → B b
subst B refl b = b

subst₂ :  ∀ {α β γ} {A : Set α} {B : Set β} (C : A → B → Set γ) {a b c d} →
  (a ≡ b) → (c ≡ d) → C a c → C b d
subst₂ C refl refl c = c

cong : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) {a b} →
  (a ≡ b) → (f a ≡ f b)
cong f refl = refl

cong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} (f : A → B → C) {a b c d} →
  (a≡b : a ≡ b) → (c ≡ d) → (f a c ≡ f b d)
cong₂ f refl refl = refl

δcong₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : Set γ} (f : ∀ a → B a → C) {a b c d} →
  (a≡b : a ≡ b) → (subst B a≡b c ≡ d) → (f a c ≡ f b d)
δcong₂ f refl refl = refl

private
  primitive
    primTrustMe : ∀ {α} {A : Set α} {a b : A} → (a ≡ b)

≡-relevant : ∀ {α} {A : Set α} {a b : A} → .(a ≡ b) → (a ≡ b)
≡-relevant a≡b = primTrustMe

-- Equational reasoning, specialized to ≡

infix  4 _IsRelatedTo_
infix  2 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_

data _IsRelatedTo_ {α} {A : Set α} (a b  : A) : Set α where
  relTo : (a≡b : a ≡ b) → a IsRelatedTo b

begin_ : ∀ {α} {A : Set α} {a b : A} → a IsRelatedTo b → a ≡ b
begin relTo a≡b = a≡b

_≡⟨_⟩_ : ∀ {α} {A : Set α} a {b c : A} → a ≡ b → b IsRelatedTo c → a IsRelatedTo c
_ ≡⟨ a≡b ⟩ relTo b≡c = relTo (trans a≡b b≡c)

_∎ : ∀ {α} {A : Set α} (a : A) → a IsRelatedTo a
_∎ _ = relTo refl
