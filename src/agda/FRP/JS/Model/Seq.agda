open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; subst ; cong ; cong₂ ; id ; _∘_ ; ≡-relevant )
open import FRP.JS.Model.List using ( List ; [] ; _∷_ ; _++_ ; ++-unit )

module FRP.JS.Model.Seq where

infixr 4 _+_

-- Seq A is isomorphic to List A, but has associativity of concatenation
-- up to beta reduction, not just up to propositional equality.

record Seq (A : Set) : Set where
  constructor seq
  field
    as : List A
    fun : List A → List A
    .ok : fun ≡ _++_ as

open Seq public using () renaming (as to ⟨_⟩ )

-- Convert any list into a Seq

[_] : ∀ {A} → List A → Seq A
[ as ] = seq as (_++_ as) refl

-- Empty list

∅ : ∀ {A} → Seq A
∅ = [ [] ]

-- Concatenation

∘✓ : ∀ {A f g} (as bs : List A) → (f ≡ _++_ as) → (g ≡ _++_ bs) → ((f ∘ g) ≡ _++_ (f bs))
∘✓ []       bs refl refl = refl
∘✓ (a ∷ as) bs refl refl = cong (_∘_ (_∷_ a)) (∘✓ as bs refl refl)

_+_ : ∀ {A} → Seq A → Seq A → Seq A
(seq as f f✓) + (seq bs g g✓) = seq (f bs) (f ∘ g) (∘✓ as bs f✓ g✓)

-- Cons

_◁_ : ∀ {A} → A → Seq A → Seq A
a ◁ as = [ a ∷ [] ] + as

-- Case analysis

-- Slightly annoyingly, we have two forms of case analysis,
-- one of which gives stronger guarantees, and one which reduces more often

-- First, the stronger one
-- Note that this uses ≡-relevant, which in turn uses trustMe,
-- which does not reduce to refl.

data Case+ {A : Set} : Seq A → Set where
  [] : Case+ ∅
  _∷_ : ∀ a as → Case+ (a ◁ as)

case+ : ∀ {A} (as : Seq A) → Case+ as
case+ (seq as       f  f✓) with ≡-relevant f✓
case+ (seq []       ._ f✓) | refl = []
case+ (seq (a ∷ as) ._ f✓) | refl = a ∷ (seq as (_++_ as) refl)

-- Then the weaker one
-- No use of ≡-relevant, so it reduces, but it doesn't give very strong
-- guarantees.

data Case {A : Set} : Seq A → Set where
  [] : ∀ {f} .{f✓} → Case (seq [] f f✓)
  _∷_ : ∀ a as {f} .{f✓} → Case (seq (a ∷ ⟨ as ⟩) f f✓)

case : ∀ {A} (as : Seq A) → Case as
case (seq []       f f✓) = [] {f = f} {f✓ = f✓}
case (seq (a ∷ as) f f✓) = _∷_ a [ as ] {f} {f✓}

-- Case supports inductive definitions, for example:

ids : ∀ {A} → Seq A → Seq A
ids as with case as
ids ._ | a ∷ as = a ◁ ids as
ids ._ | []     = ∅

-- Ismorphism between Seq and List which respects +

iso : ∀ {A} (as : Seq A) → [ ⟨ as ⟩ ] ≡ as
iso (seq as f  f✓) with ≡-relevant f✓
iso (seq as ._ f✓) | refl = refl

iso⁻¹ : ∀ {A} (as : List A) → ⟨ [ as ] ⟩ ≡ as
iso⁻¹ as = refl

iso-resp-+ : ∀ {A} (as bs : Seq A) → (⟨ as + bs ⟩) ≡ (⟨ as ⟩ ++ ⟨ bs ⟩)
iso-resp-+ (seq as f  f✓) (seq bs g g✓) with ≡-relevant f✓
iso-resp-+ (seq as ._ f✓) (seq bs g g✓) | refl = refl

-- Left unit and associtivity are true up to beta-reduction

+-unit₁ : ∀ {A} (as : Seq A) → ((∅ + as) ≡ as)
+-unit₁ as = refl

+-assoc : ∀ {A} (as bs cs : Seq A) → ((as + bs) + cs) ≡ (as + (bs + cs))
+-assoc as bs cs = refl

-- Right unit is only true up to propositional equality

+-unit₂ : ∀ {A} (as : Seq A) → ((as + ∅) ≡ as)
+-unit₂ as = 
  (trans (sym (iso (as + ∅))) 
    (trans (cong [_] (iso-resp-+ as ∅)) 
      (trans (cong [_] (++-unit ⟨ as ⟩))
        (iso as))))

-- We could make +-unit₂ true up to beta-reduction by making as
-- irrelevant in the definition of Seq.  This is sound, because we
-- know that as ≡ f [], but it is expensive as it means f [] will be
-- applied repeatedly rather than being memoized.
