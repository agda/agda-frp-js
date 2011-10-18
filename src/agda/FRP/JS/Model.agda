open import FRP.JS.Level using ( Level ; _⊔_ ) renaming ( zero to o ; suc to ↑ )
open import FRP.JS.Time using ( Time ; _≟_ ; _≤_ ; _<_ )
open import FRP.JS.True using ( True )
open import FRP.JS.Nat using ( ℕ ; zero ; suc )

module FRP.JS.Model where

-- Preliminaries

infixr 4 _+_

record ⊤ {α} : Set α where
  constructor tt

open ⊤ public

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

postulate
  ≤-refl : ∀ t → True (t ≤ t)
  ≤-trans : ∀ t u v → True (t ≤ u) → True (u ≤ v) → True (t ≤ v)

-- Relations on Set

_∋_↔_ : ∀ α → Set α → Set α → Set (↑ α)
α ∋ A ↔ B = A → B → Set α

-- RSets and relations on RSet

RSet : ∀ α → Set (↑ α)
RSet α = Time → Set α

RSet₀ = RSet o
RSet₁ = RSet (↑ o)

_∋_⇔_ : ∀ α → RSet α → RSet α → Set (↑ α)
α ∋ A ⇔ B = ∀ t → (α ∋ A t ↔ B t)

--- Level sequences

data Levels : Set where
  ε : Levels
  _,_ : ∀ (αs : Levels) (α : Level) → Levels

max : Levels → Level
max ε = o
max (αs , α) = max αs ⊔ α

-- Sequences of Sets

Sets : ∀ αs → Set (↑ (max αs))
Sets ε        = ⊤
Sets (αs , α) = Sets αs × Set α

⟨_∋_⟩ : ∀ αs → Sets αs → Set (max αs)
⟨ ε ∋ tt ⟩ = ⊤
⟨ (αs , α) ∋ (As , A) ⟩ = ⟨ αs ∋ As ⟩ × A

_∋_↔*_ : ∀ αs → Sets αs → Sets αs → Set (↑ (max αs))
ε        ∋ tt       ↔* tt       = ⊤
(αs , α) ∋ (As , A) ↔* (Bs , B) = (αs ∋ As ↔* Bs) × (α ∋ A ↔ B)

⟨_∋_⟩² : ∀ αs {As Bs} → (αs ∋ As ↔* Bs) → (max αs ∋ ⟨ αs ∋ As ⟩ ↔ ⟨ αs ∋ Bs ⟩)
⟨ ε        ∋ tt       ⟩² tt       tt       = ⊤
⟨ (αs , α) ∋ (ℜs , ℜ) ⟩² (as , a) (bs , b) = (⟨ αs ∋ ℜs ⟩² as bs) × (ℜ a b)

-- Sequences of RSets

RSets : ∀ αs → Set (↑ (max αs))
RSets ε        = ⊤
RSets (αs , α) = RSets αs × RSet α

_∋_⇔*_ : ∀ αs → RSets αs → RSets αs → Set (↑ (max αs))
ε        ∋ tt       ⇔* tt       = ⊤
(αs , α) ∋ (As , A) ⇔* (Bs , B) = (αs ∋ As ⇔* Bs) × (α ∋ A ⇔ B)

-- Concatenation of sequences

_+_ : Levels → Levels → Levels
αs + ε        = αs
αs + (βs , β) = (αs + βs) , β

_∋_++_∋_ : ∀ αs → RSets αs → ∀ βs → RSets βs → RSets (αs + βs)
αs ∋ As ++ ε        ∋ tt       = As
αs ∋ As ++ (βs , β) ∋ (Bs , B) = ((αs ∋ As ++ βs ∋ Bs) , B)

_∋_++²_∋_ : ∀ αs {As Bs} → (αs ∋ As ⇔* Bs) → ∀ βs {Cs Ds} → (βs ∋ Cs ⇔* Ds) → 
  ((αs + βs) ∋ (αs ∋ As ++ βs ∋ Cs) ⇔* (αs ∋ Bs ++ βs ∋ Ds))
αs ∋ ℜs ++² ε        ∋ tt       = ℜs
αs ∋ ℜs ++² (βs , β) ∋ (ℑs , ℑ) = ((αs ∋ ℜs ++² βs ∋ ℑs) , ℑ)

-- Intervals

_[_,_] : ∀ {α} → RSet α → Time → Time → Set α
A [ s , u ] = ∀ t → True (s ≤ t) → True (t ≤ u) → A t

_[_,_]² : ∀ {α A B} → (α ∋ A ⇔ B) → ∀ s u → (α ∋ A [ s , u ] ↔ B [ s , u ])
(ℜ [ s , u ]²) σ τ = ∀ t s≤t t≤u → ℜ t (σ t s≤t t≤u) (τ t s≤t t≤u)

-- Type variables

data TVar : Levels → Set₁ where
  zero : ∀ {αs α} → TVar (αs , α)
  suc : ∀ {αs α} → (τ : TVar αs) → TVar (αs , α)

τlevel : ∀ {αs} → TVar αs → Level
τlevel (zero {α = α}) = α
τlevel (suc τ) = τlevel τ

τ⟦_⟧ : ∀ {αs} (τ : TVar αs) → RSets αs → RSet (τlevel τ)
τ⟦ zero ⟧  (As , A) = A
τ⟦ suc τ ⟧ (As , A) = τ⟦ τ ⟧ As

τ⟦_⟧² : ∀ {αs As Bs} (τ : TVar αs) (ℜs : αs ∋ As ⇔* Bs) → (τlevel τ ∋ τ⟦ τ ⟧ As ⇔ τ⟦ τ ⟧ Bs)
τ⟦ zero ⟧²  (ℜs , ℜ) t a b = ℜ t a b
τ⟦ suc τ ⟧² (ℜs , ℜ) t a b = τ⟦ τ ⟧² ℜs t a b

-- Types

data Typ (αs : Levels) : Set₁ where
  ⟨_⟩ : (A : Set) → Typ αs
  _∧_ _⇒_ _⊵_ : (T : Typ αs) → (U : Typ αs) → Typ αs
  tvar : (τ : TVar αs) → Typ αs
  univ : ∀ α → (T : Typ (αs , α)) → Typ αs

tlevel : ∀ {αs} → Typ αs → Level
tlevel ⟨ A ⟩      = o
tlevel (T ∧ U)    = tlevel T ⊔ tlevel U
tlevel (T ⇒ U)    = tlevel T ⊔ tlevel U
tlevel (T ⊵ U)    = tlevel T ⊔ tlevel U
tlevel (tvar τ)   = τlevel τ
tlevel (univ α T) = ↑ α ⊔ tlevel T

T⟦_⟧ : ∀ {αs} (T : Typ αs) → RSets αs → RSet (tlevel T)
T⟦ ⟨ A ⟩ ⟧    As t = A
T⟦ T ∧ U ⟧    As t = T⟦ T ⟧ As t × T⟦ U ⟧ As t
T⟦ T ⇒ U ⟧    As t = T⟦ T ⟧ As t → T⟦ U ⟧ As t
T⟦ T ⊵ U ⟧    As t = ∀ u → True (t ≤ u) → T⟦ T ⟧ As [ t , u ] → T⟦ U ⟧ As u
T⟦ tvar τ ⟧   As t = τ⟦ τ ⟧ As t
T⟦ univ α T ⟧ As t = ∀ (A : RSet α) → T⟦ T ⟧ (As , A) t

T⟦_⟧² : ∀ {αs As Bs} (T : Typ αs) (ℜs : αs ∋ As ⇔* Bs) → (tlevel T ∋ T⟦ T ⟧ As ⇔ T⟦ T ⟧ Bs)
T⟦ ⟨ A ⟩ ⟧²    ℜs t a       b       = a ≡ b
T⟦ T ∧ U ⟧²    ℜs t (a , b) (c , d) = T⟦ T ⟧² ℜs t a c × T⟦ U ⟧² ℜs t b d
T⟦ T ⇒ U ⟧²    ℜs t f       g       = ∀ {a b} → T⟦ T ⟧² ℜs t a b → T⟦ U ⟧² ℜs t (f a) (g b)
T⟦ T ⊵ U ⟧²    ℜs t f       g       = ∀ u t≤u {σ τ} → (T⟦ T ⟧² ℜs [ t , u ]²) σ τ → T⟦ U ⟧² ℜs u (f u t≤u σ) (g u t≤u τ)
T⟦ tvar τ ⟧²   ℜs t v       w       = τ⟦ τ ⟧² ℜs t v w
T⟦ univ α T ⟧² ℜs t f       g       = ∀ {A B} (ℜ : α ∋ A ⇔ B) → T⟦ T ⟧² (ℜs , ℜ) t (f A) (g B)

-- Contexts

data Ctxt (αs : Levels) : Set₁ where
  ε : Ctxt αs
  _,_at_ : (Γ : Ctxt αs) (T : Typ αs) (t : Time) → Ctxt αs

clevels : ∀ {αs} → Ctxt αs → Levels
clevels ε            = ε
clevels (Γ , T at t) = (clevels Γ , tlevel T)

Γ⟦_⟧ : ∀ {αs} (Γ : Ctxt αs) → RSets αs → Sets (clevels Γ)
Γ⟦ ε ⟧          As = tt
Γ⟦ Γ , T at t ⟧ As = (Γ⟦ Γ ⟧ As , T⟦ T ⟧ As t)

Γ⟦_⟧² : ∀ {αs As Bs} (Γ : Ctxt αs) (ℜs : αs ∋ As ⇔* Bs) → (clevels Γ ∋ Γ⟦ Γ ⟧ As ↔* Γ⟦ Γ ⟧ Bs)
Γ⟦ ε ⟧²          ℜs = tt
Γ⟦ Γ , T at t ⟧² ℜs = (Γ⟦ Γ ⟧² ℜs , T⟦ T ⟧² ℜs t)

-- Weakening of type variables

τweaken : ∀ {αs} α βs → TVar (αs + βs) → TVar ((αs , α) + βs)
τweaken α ε        τ       = suc τ
τweaken α (βs , β) zero    = zero
τweaken α (βs , β) (suc τ) = suc (τweaken α βs τ)

⟦τweaken⟧ : ∀ {αs} α βs (τ : TVar (αs + βs)) As A Bs t → 
  τ⟦ τ ⟧ (αs ∋ As ++ βs ∋ Bs) t → τ⟦ τweaken α βs τ ⟧ ((αs , α) ∋ (As , A) ++ βs ∋ Bs) t
⟦τweaken⟧ α ε        τ       As A Bs       t a = a
⟦τweaken⟧ α (βs , β) zero    As A Bs       t a = a
⟦τweaken⟧ α (βs , β) (suc τ) As A (Bs , B) t a = ⟦τweaken⟧ α βs τ As A Bs t a

⟦τweaken⁻¹⟧ : ∀ {αs} α βs (τ : TVar (αs + βs)) As A Bs t → 
  τ⟦ τweaken α βs τ ⟧ ((αs , α) ∋ (As , A) ++ βs ∋ Bs) t → τ⟦ τ ⟧ (αs ∋ As ++ βs ∋ Bs) t
⟦τweaken⁻¹⟧ α ε        τ       As A Bs       t a = a
⟦τweaken⁻¹⟧ α (βs , β) zero    As A Bs       t a = a
⟦τweaken⁻¹⟧ α (βs , β) (suc τ) As A (Bs , B) t a = ⟦τweaken⁻¹⟧ α βs τ As A Bs t a

⟦τweaken⟧² : ∀ {αs} α βs (τ : TVar (αs + βs)) {As Bs A B Cs Ds} ℜs ℜ ℑs t {a b} →
  τ⟦ τ ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t a b → 
  τ⟦ τweaken α βs τ ⟧² ((αs , α) ∋ (ℜs , ℜ) ++² βs ∋ ℑs) t (⟦τweaken⟧ α βs τ As A Cs t a) (⟦τweaken⟧ α βs τ Bs B Ds t b)
⟦τweaken⟧² α ε        τ       ℜs ℜ ℑs       t aℜb = aℜb
⟦τweaken⟧² α (βs , β) zero    ℜs ℜ ℑs       t aℜb = aℜb
⟦τweaken⟧² α (βs , β) (suc τ) ℜs ℜ (ℑs , ℑ) t aℜb = ⟦τweaken⟧² α βs τ ℜs ℜ ℑs t aℜb

⟦τweaken⁻¹⟧² : ∀ {αs} α βs (τ : TVar (αs + βs)) {As Bs A B Cs Ds} ℜs ℜ ℑs t {a b} →
  τ⟦ τweaken α βs τ ⟧² ((αs , α) ∋ (ℜs , ℜ) ++² βs ∋ ℑs) t a b →
  τ⟦ τ ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t (⟦τweaken⁻¹⟧ α βs τ As A Cs t a) (⟦τweaken⁻¹⟧ α βs τ Bs B Ds t b)
⟦τweaken⁻¹⟧² α ε        τ       ℜs ℜ ℑs       t aℜb = aℜb
⟦τweaken⁻¹⟧² α (βs , β) zero    ℜs ℜ ℑs       t aℜb = aℜb
⟦τweaken⁻¹⟧² α (βs , β) (suc τ) ℜs ℜ (ℑs , ℑ) t aℜb = ⟦τweaken⁻¹⟧² α βs τ ℜs ℜ ℑs t aℜb

-- Weakening of types

tweaken : ∀ {αs} α βs → Typ (αs + βs) → Typ ((αs , α) + βs)
tweaken α βs ⟨ A ⟩      = ⟨ A ⟩
tweaken α βs (T ∧ U)    = tweaken α βs T ∧ tweaken α βs U
tweaken α βs (T ⇒ U)    = tweaken α βs T ⇒ tweaken α βs U
tweaken α βs (T ⊵ U)    = tweaken α βs T ⊵ tweaken α βs U
tweaken α βs (tvar τ)   = tvar (τweaken α βs τ)
tweaken α βs (univ β T) = univ β (tweaken α (βs , β) T)

mutual

  ⟦tweaken⟧ : ∀ {αs} α βs (T : Typ (αs + βs)) As A Bs t → 
    T⟦ T ⟧ (αs ∋ As ++ βs ∋ Bs) t → 
    T⟦ tweaken α βs T ⟧ ((αs , α) ∋ (As , A) ++ βs ∋ Bs) t
  ⟦tweaken⟧ α βs ⟨ B ⟩      As A Bs t a       = a
  ⟦tweaken⟧ α βs (T ∧ U)    As A Bs t (a , b) = (⟦tweaken⟧ α βs T As A Bs t a , ⟦tweaken⟧ α βs U As A Bs t b)
  ⟦tweaken⟧ α βs (T ⇒ U)    As A Bs t f       = λ a → ⟦tweaken⟧ α βs U As A Bs t (f (⟦tweaken⁻¹⟧ α βs T As A Bs t a))
  ⟦tweaken⟧ α βs (T ⊵ U)    As A Bs t f       = λ v t≤v σ → ⟦tweaken⟧ α βs U As A Bs v (f v t≤v (λ u t≤u u≤v → ⟦tweaken⁻¹⟧ α βs T As A Bs u (σ u t≤u u≤v)))
  ⟦tweaken⟧ α βs (tvar τ)   As A Bs t a       = ⟦τweaken⟧ α βs τ As A Bs t a
  ⟦tweaken⟧ α βs (univ β T) As A Bs t f       = λ B → ⟦tweaken⟧ α (βs , β) T As A (Bs , B) t (f B)

  ⟦tweaken⁻¹⟧ : ∀ {αs} α βs (T : Typ (αs + βs)) As A Bs t → 
    T⟦ tweaken α βs T ⟧ ((αs , α) ∋ (As , A) ++ βs ∋ Bs) t →
    T⟦ T ⟧ (αs ∋ As ++ βs ∋ Bs) t
  ⟦tweaken⁻¹⟧ α βs ⟨ B ⟩      As A Bs t a       = a
  ⟦tweaken⁻¹⟧ α βs (T ∧ U)    As A Bs t (a , b) = (⟦tweaken⁻¹⟧ α βs T As A Bs t a , ⟦tweaken⁻¹⟧ α βs U As A Bs t b)
  ⟦tweaken⁻¹⟧ α βs (T ⇒ U)    As A Bs t f       = λ a → ⟦tweaken⁻¹⟧ α βs U As A Bs t (f (⟦tweaken⟧ α βs T As A Bs t a))
  ⟦tweaken⁻¹⟧ α βs (T ⊵ U)    As A Bs t f       = λ v t≤v σ → ⟦tweaken⁻¹⟧ α βs U As A Bs v (f v t≤v (λ u t≤u u≤v → ⟦tweaken⟧ α βs T As A Bs u (σ u t≤u u≤v)))
  ⟦tweaken⁻¹⟧ α βs (tvar τ)   As A Bs t a       = ⟦τweaken⁻¹⟧ α βs τ As A Bs t a
  ⟦tweaken⁻¹⟧ α βs (univ β T) As A Bs t f       = λ B → ⟦tweaken⁻¹⟧ α (βs , β) T As A (Bs , B) t (f B)

mutual

  ⟦tweaken⟧² : ∀ {αs} α βs (T : Typ (αs + βs)) {As Bs A B Cs Ds} ℜs ℜ ℑs t {a b} →
    T⟦ T ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t a b → 
    T⟦ tweaken α βs T ⟧² ((αs , α) ∋ (ℜs , ℜ) ++² βs ∋ ℑs) t (⟦tweaken⟧ α βs T As A Cs t a) (⟦tweaken⟧ α βs T Bs B Ds t b)
  ⟦tweaken⟧² α βs ⟨ B ⟩      ℜs ℜ ℑs t aℜb         = aℜb
  ⟦tweaken⟧² α βs (T ∧ U)    ℜs ℜ ℑs t (aℜb , cℜd) = (⟦tweaken⟧² α βs T ℜs ℜ ℑs t aℜb , ⟦tweaken⟧² α βs U ℜs ℜ ℑs t cℜd)
  ⟦tweaken⟧² α βs (T ⇒ U)    ℜs ℜ ℑs t fℜg         = λ aℜb → ⟦tweaken⟧² α βs U ℜs ℜ ℑs t (fℜg (⟦tweaken⁻¹⟧² α βs T ℜs ℜ ℑs t aℜb))
  ⟦tweaken⟧² α βs (T ⊵ U)    ℜs ℜ ℑs t fℜg         = λ v t≤v σℜτ → ⟦tweaken⟧² α βs U ℜs ℜ ℑs v (fℜg v t≤v (λ u t≤u u≤v → ⟦tweaken⁻¹⟧² α βs T ℜs ℜ ℑs u (σℜτ u t≤u u≤v)))
  ⟦tweaken⟧² α βs (tvar τ)   ℜs ℜ ℑs t aℜb         = ⟦τweaken⟧² α βs τ ℜs ℜ ℑs t aℜb
  ⟦tweaken⟧² α βs (univ β T) ℜs ℜ ℑs t fℜg         = λ ℑ → ⟦tweaken⟧² α (βs , β) T ℜs ℜ (ℑs , ℑ) t (fℜg ℑ)

  ⟦tweaken⁻¹⟧² : ∀ {αs} α βs (T : Typ (αs + βs)) {As Bs A B Cs Ds} ℜs ℜ ℑs t {a b} →
    T⟦ tweaken α βs T ⟧² ((αs , α) ∋ (ℜs , ℜ) ++² βs ∋ ℑs) t a b →
    T⟦ T ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t (⟦tweaken⁻¹⟧ α βs T As A Cs t a) (⟦tweaken⁻¹⟧ α βs T Bs B Ds t b)
  ⟦tweaken⁻¹⟧² α βs ⟨ B ⟩      ℜs ℜ ℑs t aℜb         = aℜb
  ⟦tweaken⁻¹⟧² α βs (T ∧ U)    ℜs ℜ ℑs t (aℜb , cℜd) = (⟦tweaken⁻¹⟧² α βs T ℜs ℜ ℑs t aℜb , ⟦tweaken⁻¹⟧² α βs U ℜs ℜ ℑs t cℜd)
  ⟦tweaken⁻¹⟧² α βs (T ⇒ U)    ℜs ℜ ℑs t fℜg         = λ aℜb → ⟦tweaken⁻¹⟧² α βs U ℜs ℜ ℑs t (fℜg (⟦tweaken⟧² α βs T ℜs ℜ ℑs t aℜb))
  ⟦tweaken⁻¹⟧² α βs (T ⊵ U)    ℜs ℜ ℑs t fℜg         = λ v t≤v σℜτ → ⟦tweaken⁻¹⟧² α βs U ℜs ℜ ℑs v (fℜg v t≤v (λ u t≤u u≤v → ⟦tweaken⟧² α βs T ℜs ℜ ℑs u (σℜτ u t≤u u≤v)))
  ⟦tweaken⁻¹⟧² α βs (tvar τ)   ℜs ℜ ℑs t aℜb         = ⟦τweaken⁻¹⟧² α βs τ ℜs ℜ ℑs t aℜb
  ⟦tweaken⁻¹⟧² α βs (univ β T) ℜs ℜ ℑs t fℜg         = λ ℑ → ⟦tweaken⁻¹⟧² α (βs , β) T ℜs ℜ (ℑs , ℑ) t (fℜg ℑ)

-- Weakening of contexts

cweaken : ∀ {αs} α → Ctxt αs → Ctxt (αs , α)
cweaken α ε            = ε
cweaken α (Γ , T at t) = (cweaken α Γ , tweaken α ε T at t)
  
⟦cweaken⟧ : ∀ {αs} α (Γ : Ctxt αs) As A → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧ As ⟩ → ⟨ clevels (cweaken α Γ) ∋ Γ⟦ cweaken α Γ ⟧ (As , A) ⟩
⟦cweaken⟧ α ε            As A tt       = tt
⟦cweaken⟧ α (Γ , T at t) As A (as , a) = (⟦cweaken⟧ α Γ As A as , ⟦tweaken⟧ α ε T As A tt t a)

⟦cweaken⟧² : ∀ {αs} α (Γ : Ctxt αs) {As Bs A B} ℜs ℜ {as bs} → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧² ℜs ⟩² as bs →
  ⟨ clevels (cweaken α Γ) ∋ Γ⟦ cweaken α Γ ⟧² (ℜs , ℜ) ⟩² (⟦cweaken⟧ α Γ As A as) (⟦cweaken⟧ α Γ Bs B bs)
⟦cweaken⟧² α ε            ℜs ℜ tt            = tt
⟦cweaken⟧² α (Γ , T at t) ℜs ℜ (asℜbs , aℜb) = (⟦cweaken⟧² α Γ ℜs ℜ asℜbs , ⟦tweaken⟧² α ε T ℜs ℜ tt t aℜb)

-- Substitution into type variables

τsubst : ∀ {αs} (T : Typ αs) βs → TVar ((αs , tlevel T) + βs) → Typ (αs + βs)
τsubst T ε        zero    = T
τsubst T ε        (suc τ) = tvar τ
τsubst T (βs , β) zero    = tvar zero
τsubst T (βs , β) (suc τ) = tweaken β ε (τsubst T βs τ)

⟦τsubst⟧ : ∀ {αs} (T : Typ αs) βs (τ : TVar ((αs , tlevel T) + βs)) As Bs t →
  τ⟦ τ ⟧ ((αs , tlevel T) ∋ (As , T⟦ T ⟧ As) ++ βs ∋ Bs) t → 
  T⟦ τsubst T βs τ ⟧ (αs ∋ As ++ βs ∋ Bs) t
⟦τsubst⟧      T ε        zero    As Bs       t a = a
⟦τsubst⟧      T ε        (suc τ) As Bs       t a = a
⟦τsubst⟧      T (βs , β) zero    As Bs       t a = a 
⟦τsubst⟧ {αs} T (βs , β) (suc τ) As (Bs , B) t a = 
  ⟦tweaken⟧ β ε (τsubst T βs τ) (αs ∋ As ++ βs ∋ Bs) B tt t 
    (⟦τsubst⟧ T βs τ As Bs t a)

⟦τsubst⁻¹⟧ : ∀ {αs} (T : Typ αs) βs (τ : TVar ((αs , tlevel T) + βs)) As Bs t →
  T⟦ τsubst T βs τ ⟧ (αs ∋ As ++ βs ∋ Bs) t →
  τ⟦ τ ⟧ ((αs , tlevel T) ∋ (As , T⟦ T ⟧ As) ++ βs ∋ Bs) t
⟦τsubst⁻¹⟧      T ε        zero    As Bs       t a = a
⟦τsubst⁻¹⟧      T ε        (suc τ) As Bs       t a = a
⟦τsubst⁻¹⟧      T (βs , β) zero    As Bs       t a = a 
⟦τsubst⁻¹⟧ {αs} T (βs , β) (suc τ) As (Bs , B) t a = 
  ⟦τsubst⁻¹⟧ T βs τ As Bs t 
    (⟦tweaken⁻¹⟧ β ε (τsubst T βs τ) (αs ∋ As ++ βs ∋ Bs) B tt t a)

⟦τsubst⟧² : ∀ {αs} (T : Typ αs) βs (τ : TVar ((αs , tlevel T) + βs)) {As Bs Cs Ds} ℜs ℑs t {a b} →
  τ⟦ τ ⟧² ((αs , tlevel T) ∋ (ℜs , T⟦ T ⟧² ℜs) ++² βs ∋ ℑs) t a b →
  T⟦ τsubst T βs τ ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t (⟦τsubst⟧ T βs τ As Bs t a) (⟦τsubst⟧ T βs τ Cs Ds t b)
⟦τsubst⟧²      T ε        zero    ℜs ℑs       t aℜb = aℜb
⟦τsubst⟧²      T ε        (suc τ) ℜs ℑs       t aℜb = aℜb
⟦τsubst⟧²      T (βs , β) zero    ℜs ℑs       t aℜb = aℜb 
⟦τsubst⟧² {αs} T (βs , β) (suc τ) ℜs (ℑs , ℑ) t aℜb = 
  ⟦tweaken⟧² β ε (τsubst T βs τ) (αs ∋ ℜs ++² βs ∋ ℑs) ℑ tt t 
    (⟦τsubst⟧² T βs τ ℜs ℑs t aℜb)

⟦τsubst⁻¹⟧² : ∀ {αs} (T : Typ αs) βs (τ : TVar ((αs , tlevel T) + βs)) {As Bs Cs Ds} ℜs ℑs t {a b} →
  T⟦ τsubst T βs τ ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t a b →
  τ⟦ τ ⟧² ((αs , tlevel T) ∋ (ℜs , T⟦ T ⟧² ℜs) ++² βs ∋ ℑs) t (⟦τsubst⁻¹⟧ T βs τ As Bs t a) (⟦τsubst⁻¹⟧ T βs τ Cs Ds t b)
⟦τsubst⁻¹⟧²      T ε        zero    ℜs ℑs       t aℜb = aℜb
⟦τsubst⁻¹⟧²      T ε        (suc τ) ℜs ℑs       t aℜb = aℜb
⟦τsubst⁻¹⟧²      T (βs , β) zero    ℜs ℑs       t aℜb = aℜb 
⟦τsubst⁻¹⟧² {αs} T (βs , β) (suc τ) ℜs (ℑs , ℑ) t aℜb = 
  ⟦τsubst⁻¹⟧² T βs τ ℜs ℑs t 
    (⟦tweaken⁻¹⟧² β ε (τsubst T βs τ) (αs ∋ ℜs ++² βs ∋ ℑs) ℑ tt t aℜb)

-- Substitution into types

tsubst : ∀ {αs} (T : Typ αs) βs → Typ ((αs , tlevel T) + βs) → Typ (αs + βs)
tsubst T βs ⟨ A ⟩      = ⟨ A ⟩
tsubst T βs (U ∧ V)    = tsubst T βs U ∧ tsubst T βs V
tsubst T βs (U ⇒ V)    = tsubst T βs U ⇒ tsubst T βs V
tsubst T βs (U ⊵ V)    = tsubst T βs U ⊵ tsubst T βs V
tsubst T βs (tvar τ)   = τsubst T βs τ
tsubst T βs (univ β U) = univ β (tsubst T (βs , β) U)

mutual

  ⟦tsubst⟧ : ∀ {αs} (T : Typ αs) βs (U : Typ ((αs , tlevel T) + βs)) As Bs t →
    T⟦ U ⟧ ((αs , tlevel T) ∋ (As , T⟦ T ⟧ As) ++ βs ∋ Bs) t → 
    T⟦ tsubst T βs U ⟧ (αs ∋ As ++ βs ∋ Bs) t
  ⟦tsubst⟧ T βs ⟨ A ⟩      As Bs t a       = a
  ⟦tsubst⟧ T βs (U ∧ V)    As Bs t (a , b) = (⟦tsubst⟧ T βs U As Bs t a , ⟦tsubst⟧ T βs V As Bs t b)
  ⟦tsubst⟧ T βs (U ⇒ V)    As Bs t f       = λ a → ⟦tsubst⟧ T βs V As Bs t (f (⟦tsubst⁻¹⟧ T βs U As Bs t a))
  ⟦tsubst⟧ T βs (U ⊵ V)    As Bs t f       = λ v t≤v σ → ⟦tsubst⟧ T βs V As Bs v (f v t≤v (λ u t≤u u≤v → ⟦tsubst⁻¹⟧ T βs U As Bs u (σ u t≤u u≤v)))
  ⟦tsubst⟧ T βs (tvar τ)   As Bs t a       = ⟦τsubst⟧ T βs τ As Bs t a
  ⟦tsubst⟧ T βs (univ β U) As Bs t f       = λ B → ⟦tsubst⟧ T (βs , β) U As (Bs , B) t (f B)

  ⟦tsubst⁻¹⟧ : ∀ {αs} (T : Typ αs) βs (U : Typ ((αs , tlevel T) + βs)) As Bs t →
    T⟦ tsubst T βs U ⟧ (αs ∋ As ++ βs ∋ Bs) t →
    T⟦ U ⟧ ((αs , tlevel T) ∋ (As , T⟦ T ⟧ As) ++ βs ∋ Bs) t
  ⟦tsubst⁻¹⟧ T βs ⟨ A ⟩      As Bs t a       = a
  ⟦tsubst⁻¹⟧ T βs (U ∧ V)    As Bs t (a , b) = (⟦tsubst⁻¹⟧ T βs U As Bs t a , ⟦tsubst⁻¹⟧ T βs V As Bs t b)
  ⟦tsubst⁻¹⟧ T βs (U ⇒ V)    As Bs t f       = λ a → ⟦tsubst⁻¹⟧ T βs V As Bs t (f (⟦tsubst⟧ T βs U As Bs t a))
  ⟦tsubst⁻¹⟧ T βs (U ⊵ V)    As Bs t f       = λ v t≤v σ → ⟦tsubst⁻¹⟧ T βs V As Bs v (f v t≤v (λ u t≤u u≤v → ⟦tsubst⟧ T βs U As Bs u (σ u t≤u u≤v)))
  ⟦tsubst⁻¹⟧ T βs (tvar τ)   As Bs t a       = ⟦τsubst⁻¹⟧ T βs τ As Bs t a
  ⟦tsubst⁻¹⟧ T βs (univ β U) As Bs t f       = λ B → ⟦tsubst⁻¹⟧ T (βs , β) U As (Bs , B) t (f B)

mutual

  ⟦tsubst⟧² : ∀ {αs} (T : Typ αs) βs (U : Typ ((αs , tlevel T) + βs)) {As Bs Cs Ds} ℜs ℑs t {a b} →
    T⟦ U ⟧² ((αs , tlevel T) ∋ (ℜs , T⟦ T ⟧² ℜs) ++² βs ∋ ℑs) t a b →
    T⟦ tsubst T βs U ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t (⟦tsubst⟧ T βs U As Bs t a) (⟦tsubst⟧ T βs U Cs Ds t b)
  ⟦tsubst⟧² T βs ⟨ A ⟩      ℜs ℑs t aℜb         = aℜb
  ⟦tsubst⟧² T βs (U ∧ V)    ℜs ℑs t (aℜb , cℜd) = (⟦tsubst⟧² T βs U ℜs ℑs t aℜb , ⟦tsubst⟧² T βs V ℜs ℑs t cℜd)
  ⟦tsubst⟧² T βs (U ⇒ V)    ℜs ℑs t fℜg         = λ aℜb → ⟦tsubst⟧² T βs V ℜs ℑs t (fℜg (⟦tsubst⁻¹⟧² T βs U ℜs ℑs t aℜb))
  ⟦tsubst⟧² T βs (U ⊵ V)    ℜs ℑs t fℜg         = λ v t≤v σℜτ → ⟦tsubst⟧² T βs V ℜs ℑs v (fℜg v t≤v (λ u t≤u u≤v → ⟦tsubst⁻¹⟧² T βs U ℜs ℑs u (σℜτ u t≤u u≤v)))
  ⟦tsubst⟧² T βs (tvar τ)   ℜs ℑs t aℜb         = ⟦τsubst⟧² T βs τ ℜs ℑs t aℜb
  ⟦tsubst⟧² T βs (univ β U) ℜs ℑs t fℜg         = λ ℑ → ⟦tsubst⟧² T (βs , β) U ℜs (ℑs , ℑ) t (fℜg ℑ)

  ⟦tsubst⁻¹⟧² : ∀ {αs} (T : Typ αs) βs (U : Typ ((αs , tlevel T) + βs)) {As Bs Cs Ds} ℜs ℑs t {a b} →
    T⟦ tsubst T βs U ⟧² (αs ∋ ℜs ++² βs ∋ ℑs) t a b →
    T⟦ U ⟧² ((αs , tlevel T) ∋ (ℜs , T⟦ T ⟧² ℜs) ++² βs ∋ ℑs) t (⟦tsubst⁻¹⟧ T βs U As Bs t a) (⟦tsubst⁻¹⟧ T βs U Cs Ds t b)
  ⟦tsubst⁻¹⟧² T βs ⟨ A ⟩      ℜs ℑs t aℜb         = aℜb
  ⟦tsubst⁻¹⟧² T βs (U ∧ V)    ℜs ℑs t (aℜb , cℜd) = (⟦tsubst⁻¹⟧² T βs U ℜs ℑs t aℜb , ⟦tsubst⁻¹⟧² T βs V ℜs ℑs t cℜd)
  ⟦tsubst⁻¹⟧² T βs (U ⇒ V)    ℜs ℑs t fℜg         = λ aℜb → ⟦tsubst⁻¹⟧² T βs V ℜs ℑs t (fℜg (⟦tsubst⟧² T βs U ℜs ℑs t aℜb))
  ⟦tsubst⁻¹⟧² T βs (U ⊵ V)    ℜs ℑs t fℜg         = λ v t≤v σℜτ → ⟦tsubst⁻¹⟧² T βs V ℜs ℑs v (fℜg v t≤v (λ u t≤u u≤v → ⟦tsubst⟧² T βs U ℜs ℑs u (σℜτ u t≤u u≤v)))
  ⟦tsubst⁻¹⟧² T βs (tvar τ)   ℜs ℑs t aℜb         = ⟦τsubst⁻¹⟧² T βs τ ℜs ℑs t aℜb
  ⟦tsubst⁻¹⟧² T βs (univ β U) ℜs ℑs t fℜg         = λ ℑ → ⟦tsubst⁻¹⟧² T (βs , β) U ℜs (ℑs , ℑ) t (fℜg ℑ)

-- Variables

data Var {αs} (T : Typ αs) (t : Time) : (Γ : Ctxt αs) → Set₁ where
  zero : ∀ {Γ : Ctxt αs} → Var T t (Γ , T at t)
  suc : ∀ {Γ : Ctxt αs} {U : Typ αs} {u} → Var T t Γ → Var T t (Γ , U at u)

v⟦_⟧ : ∀ {αs} {Γ : Ctxt αs} {T : Typ αs} {t} → Var T t Γ → ∀ As → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧ As ⟩ → T⟦ T ⟧ As t
v⟦ zero ⟧  As (as , a) = a
v⟦ suc v ⟧ As (as , a) = v⟦ v ⟧ As as

v⟦_⟧² : ∀ {αs As Bs} {Γ : Ctxt αs} {T : Typ αs} {t} (τ : Var T t Γ) (ℜs : αs ∋ As ⇔* Bs) → 
  ∀ {as bs} → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧² ℜs ⟩² as bs → T⟦ T ⟧² ℜs t (v⟦ τ ⟧ As as) (v⟦ τ ⟧ Bs bs)
v⟦ zero ⟧²  ℜs (asℜbs , aℜb) = aℜb
v⟦ suc v ⟧² ℜs (asℜbs , aℜb) = v⟦ v ⟧² ℜs asℜbs

-- Expressions

data Exp : ∀ {αs} → Ctxt αs → Typ αs → RSet₁ where
  const : ∀ {αs Γ A t} → (a : A) → Exp {αs} Γ ⟨ A ⟩ t
  pair : ∀ {αs Γ T U t} → (e : Exp Γ T t) → (f : Exp Γ U t) → Exp {αs} Γ (T ∧ U) t
  fst : ∀ {αs Γ T U t} → (e : Exp Γ (T ∧ U) t) → Exp {αs} Γ T t
  snd : ∀ {αs Γ T U t} → (e : Exp Γ (T ∧ U) t) → Exp {αs} Γ U t
  abs : ∀ {αs Γ T U t} → (e : Exp (Γ , T at t) U t) → Exp {αs} Γ (T ⇒ U) t
  app : ∀ {αs Γ T U t} → (f : Exp Γ (T ⇒ U) t) → (e : Exp Γ T t) → Exp {αs} Γ U t
  var : ∀ {αs Γ T t} → (v : Var T t Γ) → Exp {αs} Γ T t
  tabs : ∀ {αs Γ} α {T t} → (e : Exp (cweaken α Γ) T t) → Exp {αs} Γ (univ α T) t
  tapp : ∀ {αs Γ t} (T : Typ αs) {U} → (e : Exp Γ (univ (tlevel T) U) t) → Exp {αs} Γ (tsubst T ε U) t

e⟦_⟧ : ∀ {αs} {Γ : Ctxt αs} {T : Typ αs} {t} → Exp Γ T t → ∀ As → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧ As ⟩ → T⟦ T ⟧ As t
e⟦ const a ⟧                  As as = a
e⟦ pair e f ⟧                 As as = (e⟦ e ⟧ As as , e⟦ f ⟧ As as)
e⟦ fst e ⟧                    As as = proj₁ (e⟦ e ⟧ As as)
e⟦ snd e ⟧                    As as = proj₂ (e⟦ e ⟧ As as)
e⟦ abs e ⟧                    As as = λ a → e⟦ e ⟧ As (as , a)
e⟦ app f e ⟧                  As as = e⟦ f ⟧ As as (e⟦ e ⟧ As as)
e⟦ var v ⟧                    As as = v⟦ v ⟧ As as
e⟦ tabs {Γ = Γ} α e ⟧         As as = λ A → e⟦ e ⟧ (As , A) (⟦cweaken⟧ α Γ As A as)
e⟦ tapp {t = t} T {U = U} e ⟧ As as = ⟦tsubst⟧ T ε U As tt t (e⟦ e ⟧ As as (T⟦ T ⟧ As))

e⟦_⟧² : ∀ {αs As Bs} {Γ : Ctxt αs} {T : Typ αs} {t} (e : Exp Γ T t) (ℜs : αs ∋ As ⇔* Bs) → 
  ∀ {as bs} → ⟨ clevels Γ ∋ Γ⟦ Γ ⟧² ℜs ⟩² as bs → T⟦ T ⟧² ℜs t (e⟦ e ⟧ As as) (e⟦ e ⟧ Bs bs)
e⟦ const a ⟧²                  ℜs asℜbs = refl
e⟦ pair e f ⟧²                 ℜs asℜbs = (e⟦ e ⟧² ℜs asℜbs , e⟦ f ⟧² ℜs asℜbs)
e⟦ fst e ⟧²                    ℜs asℜbs = proj₁ (e⟦ e ⟧² ℜs asℜbs)
e⟦ snd e ⟧²                    ℜs asℜbs = proj₂ (e⟦ e ⟧² ℜs asℜbs)
e⟦ abs e ⟧²                    ℜs asℜbs = λ aℜb → e⟦ e ⟧² ℜs (asℜbs , aℜb)
e⟦ app f e ⟧²                  ℜs asℜbs = e⟦ f ⟧² ℜs asℜbs (e⟦ e ⟧² ℜs asℜbs)
e⟦ var v ⟧²                    ℜs asℜbs = v⟦ v ⟧² ℜs asℜbs
e⟦ tabs {Γ = Γ} α e ⟧²         ℜs asℜbs = λ ℜ → e⟦ e ⟧² (ℜs , ℜ) (⟦cweaken⟧² α Γ ℜs ℜ asℜbs)
e⟦ tapp {t = t} T {U = U} e ⟧² ℜs asℜbs = ⟦tsubst⟧² T ε U ℜs tt t (e⟦ e ⟧² ℜs asℜbs (T⟦ T ⟧² ℜs))

-- Surface level types

data STyp : Set₁ where
  ⟨_⟩ : (A : Set) → STyp
  _∧_ _⇒_ : (T : STyp) → (U : STyp) → STyp
  □ : (T : STyp) → STyp

-- Translation of surface level types into types

⟪_⟫ : STyp → Typ (ε , o)
⟪ ⟨ A ⟩ ⟫ = ⟨ A ⟩
⟪ T ∧ U ⟫ = ⟪ T ⟫ ∧ ⟪ U ⟫
⟪ T ⇒ U ⟫ = ⟪ T ⟫ ⇒ ⟪ U ⟫
⟪ □ T ⟫   = tvar zero ⊵ ⟪ T ⟫

T⟪_⟫ : STyp → RSet₀
T⟪ ⟨ A ⟩ ⟫ t = A
T⟪ T ∧ U ⟫ t = T⟪ T ⟫ t × T⟪ U ⟫ t
T⟪ T ⇒ U ⟫ t = T⟪ T ⟫ t → T⟪ U ⟫ t
T⟪ □ T ⟫   t = ∀ u → True (t ≤ u) → T⟪ T ⟫ u

World : RSet₀
World t = ⊤

mutual

  trans : ∀ T {t} → T⟪ T ⟫ t → T⟦ ⟪ T ⟫ ⟧ (tt , World) t
  trans ⟨ A ⟩   a       = a
  trans (T ∧ U) (a , b) = (trans T a , trans U b)
  trans (T ⇒ U) f       = λ a → trans U (f (trans⁻¹ T a))
  trans (□ T)   σ       = λ u t≤u τ → trans T (σ u t≤u)

  trans⁻¹ : ∀ T {t} → T⟦ ⟪ T ⟫ ⟧ (tt , World) t → T⟪ T ⟫ t
  trans⁻¹ ⟨ A ⟩   a       = a
  trans⁻¹ (T ∧ U) (a , b) = (trans⁻¹ T a , trans⁻¹ U b)
  trans⁻¹ (T ⇒ U) f       = λ a → trans⁻¹ U (f (trans T a))
  trans⁻¹ (□ T)   σ       = λ u t≤u → trans⁻¹ T (σ u t≤u _)

-- Causality

_at_∋_≈[_∵_]_ : ∀ T t → T⟪ T ⟫ t → ∀ u → True (t ≤ u) → T⟪ T ⟫ t → Set
⟨ A ⟩   at t ∋ a       ≈[ u ∵ t≤u ] b       = a ≡ b
(T ∧ U) at t ∋ (a , b) ≈[ u ∵ t≤u ] (c , d) = (T at t ∋ a ≈[ u ∵ t≤u ] c) × (U at t ∋ b ≈[ u ∵ t≤u ] d)
(T ⇒ U) at t ∋ f       ≈[ u ∵ t≤u ] g       = ∀ {a b} → (T at t ∋ a ≈[ u ∵ t≤u ] b) → (U at t ∋ f a ≈[ u ∵ t≤u ] g b)
(□ T)   at s ∋ σ       ≈[ u ∵ s≤u ] τ       = ∀ t s≤t t≤u → (T at t ∋ σ t s≤t ≈[ u ∵ t≤u ] τ t s≤t)

Causal : ∀ T U t → T⟪ T ⇒ U ⟫ t → Set
Causal T U t f = ∀ u t≤u {a b} → (T at t ∋ a ≈[ u ∵ t≤u ] b) → (U at t ∋ f a ≈[ u ∵ t≤u ] f b)

-- Parametricity implies causality

ℜ[_] : Time → (o ∋ World ⇔ World)
ℜ[ u ] t tt tt = True (t ≤ u)

mutual

  ℜ-impl-≈ : ∀ T t u t≤u {a b} →
    T⟦ ⟪ T ⟫ ⟧² (tt , ℜ[ u ]) t a b →
    (T at t ∋ trans⁻¹ T a ≈[ u ∵ t≤u ] trans⁻¹ T b)
  ℜ-impl-≈ ⟨ A ⟩   t u t≤u aℜb         = aℜb
  ℜ-impl-≈ (T ∧ U) t u t≤u (aℜc , bℜd) = (ℜ-impl-≈ T t u t≤u aℜc , ℜ-impl-≈ U t u t≤u bℜd)
  ℜ-impl-≈ (T ⇒ U) t u t≤u fℜg         = λ a≈b → ℜ-impl-≈ U t u t≤u (fℜg (≈-impl-ℜ T t u t≤u a≈b))
  ℜ-impl-≈ (□ T)   s v s≤v σℜτ         = λ u s≤u u≤v → ℜ-impl-≈ T u v u≤v (σℜτ u s≤u (λ t s≤t t≤u → ≤-trans t u v t≤u u≤v))

  ≈-impl-ℜ : ∀ T t u t≤u {a b} →
    (T at t ∋ a ≈[ u ∵ t≤u ] b) →
    T⟦ ⟪ T ⟫ ⟧² (tt , ℜ[ u ]) t (trans T a) (trans T b)
  ≈-impl-ℜ ⟨ A ⟩   t u t≤u a≈b         = a≈b
  ≈-impl-ℜ (T ∧ U) t u t≤u (a≈c , b≈d) = (≈-impl-ℜ T t u t≤u a≈c , ≈-impl-ℜ U t u t≤u b≈d)
  ≈-impl-ℜ (T ⇒ U) t u t≤u f≈g         = λ aℜb → ≈-impl-ℜ U t u t≤u (f≈g (ℜ-impl-≈ T t u t≤u aℜb))
  ≈-impl-ℜ (□ T)   s v s≤v σ≈τ         = λ u s≤u ρ → ≈-impl-ℜ T u v (ρ u s≤u (≤-refl u)) (σ≈τ u s≤u (ρ u s≤u (≤-refl u)))

-- Every expression is causal

e⟪_at_∋_⟫ : ∀ T t → Exp ε ⟪ T ⟫ t → T⟪ T ⟫ t
e⟪ T at t ∋ e ⟫ = trans⁻¹ T (e⟦ e ⟧ (tt , World) tt)

causality : ∀ T U t f → Causal T U t e⟪ (T ⇒ U) at t ∋ f ⟫ 
causality T U t f u t≤u = ℜ-impl-≈ (T ⇒ U) t u t≤u (e⟦ f ⟧² (tt , ℜ[ u ]) tt)
