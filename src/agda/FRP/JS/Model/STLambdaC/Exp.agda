import FRP.JS.Model.STLambdaC.Typ

open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; begin_ ; _≡⟨_⟩_ ; _∎ ; _∘_ )

module FRP.JS.Model.STLambdaC.Exp 
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Var ; Ctxt ; const ; _⇝_
  ; [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫
  ; Case₃ ; case₃ ; caseˡ ; caseʳ ; caseˡ₃ ; caseʳ₃ )

data Exp (Γ : Ctxt) : Typ → Set where
  const : ∀ {T} → Const T → Exp Γ T
  abs : ∀ T {U} → Exp (T ∷ Γ) U → Exp Γ (T ⇝ U)
  app : ∀ {T U} → Exp Γ (T ⇝ U) → Exp Γ T → Exp Γ U
  var : ∀ {T} → (T ∈ Γ) → Exp Γ T

-- Shorthands

var₀ : ∀ {Γ T} → Exp (T ∷ Γ) T
var₀ {Γ} {T} = var (singleton T ≪ Γ)

-- Weakening

xweaken+ : ∀ B Γ Δ {T : Typ} → Case T B Δ → (T ∈ (B ++ Γ ++ Δ))
xweaken+ B Γ Δ (inj₁ x) = (x ≪ Γ ≪ Δ)
xweaken+ B Γ Δ (inj₂ x) = (B ≫ Γ ≫ x)

weaken+ : ∀ B Γ Δ {T} → Exp (B ++ Δ) T → Exp (B ++ Γ ++ Δ) T
weaken+ B Γ Δ (const c) = const c
weaken+ B Γ Δ (abs T M) = abs T (weaken+ (T ∷ B) Γ Δ M)
weaken+ B Γ Δ (app M N) = app (weaken+ B Γ Δ M) (weaken+ B Γ Δ N)
weaken+ B Γ Δ (var x)   = var (xweaken+ B Γ Δ (case B Δ x))

weaken* : ∀ Γ Δ {T} → Exp Δ T → Exp (Γ ++ Δ) T
weaken* = weaken+ []

weaken : ∀ {Γ} T {U} → Exp Γ U → Exp (T ∷ Γ) U
weaken {Γ} T = weaken* [ T ] Γ

-- Substitution

xsubstn+ : ∀ Γ Δ E {T U} → Case₃ U Γ [ T ] E → Exp (Δ ++ E) T → Exp (Γ ++ Δ ++ E) U
xsubstn+ Γ Δ E (inj₁ x) N = var (x ≪ Δ ≪ E)
xsubstn+ Γ Δ E (inj₂ x) N rewrite (uniq x) = weaken* Γ (Δ ++ E) N
xsubstn+ Γ Δ E (inj₃ x) N = var (Γ ≫ Δ ≫ x)

substn+ : ∀ Γ Δ E {T U} → Exp (Γ ++ T ∷ E) U → Exp (Δ ++ E) T → Exp (Γ ++ Δ ++ E) U
substn+ Γ Δ E {T} (const c) N = const c
substn+ Γ Δ E {T} (abs U M) N = abs U (substn+ (U ∷ Γ) Δ E M N)
substn+ Γ Δ E {T} (app L M) N = app (substn+ Γ Δ E L N) (substn+ Γ Δ E M N)
substn+ Γ Δ E {T} (var x)   N = xsubstn+ Γ Δ E (case₃ Γ [ T ] E x) N 

substn : ∀ {Γ T U} → Exp (T ∷ Γ) U → Exp Γ T → Exp Γ U
substn {Γ} = substn+ [] [] Γ

-- Weakening weakening is weakening

xweaken+-xweaken+ : ∀ Φ Ψ B Γ Δ {U} (x : Case₃ U Φ B Δ) → 
  xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) (xweaken+ (Φ ++ B) Γ Δ (caseˡ x)))
    ≡ xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ (xweaken+ Φ Ψ (B ++ Δ) (caseʳ x)))
xweaken+-xweaken+ Φ Ψ B Γ Δ (inj₁ x) =
  begin
    xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) (x ≪ B ≪ Γ ≪ Δ))
  ≡⟨ cong (xweaken+ Φ Ψ (B ++ Γ ++ Δ)) (case-≪ x (B ++ Γ ++ Δ)) ⟩
    x ≪ Ψ ≪ B ≪ Γ ≪ Δ
  ≡⟨ cong (xweaken+ (Φ ++ Ψ ++ B) Γ Δ) (sym (case-≪ (x ≪ Ψ ≪ B) Δ)) ⟩
    xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ (x ≪ Ψ ≪ B ≪ Δ))
  ∎
xweaken+-xweaken+ Φ Ψ B Γ Δ (inj₂ x) = 
  begin
    xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) (Φ ≫ x ≪ Γ ≪ Δ))
  ≡⟨ cong (xweaken+ Φ Ψ (B ++ Γ ++ Δ)) (case-≫ Φ (x ≪ Γ ≪ Δ)) ⟩
    (Φ ≫ Ψ ≫ x ≪ Γ ≪ Δ)
  ≡⟨ cong (xweaken+ (Φ ++ Ψ ++ B) Γ Δ) (sym (case-≪ (Φ ≫ Ψ ≫ x) Δ)) ⟩
    xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ (Φ ≫ Ψ ≫ x ≪ Δ))
  ∎
xweaken+-xweaken+ Φ Ψ B Γ Δ (inj₃ x) =
  begin
    xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) (Φ ≫ B ≫ Γ ≫ x))
  ≡⟨ cong (xweaken+ Φ Ψ (B ++ Γ ++ Δ)) (case-≫ Φ (B ≫ Γ ≫ x)) ⟩
    (Φ ≫ Ψ ≫ B ≫ Γ ≫ x)
  ≡⟨ cong (xweaken+ (Φ ++ Ψ ++ B) Γ Δ) (sym (case-≫ (Φ ++ Ψ ++ B) x)) ⟩
    xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ (Φ ≫ Ψ ≫ B ≫ x))
  ∎

weaken+-weaken+ : ∀ Φ Ψ B Γ Δ {U} (M : Exp (Φ ++ B ++ Δ) U) →
  weaken+ Φ Ψ (B ++ Γ ++ Δ) (weaken+ (Φ ++ B) Γ Δ M)
    ≡ weaken+ (Φ ++ Ψ ++ B) Γ Δ (weaken+ Φ Ψ (B ++ Δ) M)
weaken+-weaken+ Φ Ψ B Γ Δ (const c) =
  refl
weaken+-weaken+ Φ Ψ B Γ Δ (abs T M) = 
  cong (abs {Φ ++ Ψ ++ B ++ Γ ++ Δ} T) (weaken+-weaken+ (T ∷ Φ) Ψ B Γ Δ M)
weaken+-weaken+ Φ Ψ B Γ Δ (app M N) = 
  cong₂ app (weaken+-weaken+ Φ Ψ B Γ Δ M) (weaken+-weaken+ Φ Ψ B Γ Δ N)
weaken+-weaken+ Φ Ψ B Γ Δ (var x) =
  cong var (begin
    xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) 
      (xweaken+ (Φ ++ B) Γ Δ (case (Φ ++ B) Δ x)))
  ≡⟨ cong (xweaken+ Φ Ψ (B ++ Γ ++ Δ) ∘ case Φ (B ++ Γ ++ Δ) ∘ xweaken+ (Φ ++ B) Γ Δ)
       (sym (caseˡ₃ Φ B Δ x)) ⟩
    xweaken+ Φ Ψ (B ++ Γ ++ Δ) (case Φ (B ++ Γ ++ Δ) 
      (xweaken+ (Φ ++ B) Γ Δ (caseˡ (case₃ Φ B Δ x))))
  ≡⟨ xweaken+-xweaken+ Φ Ψ B Γ Δ (case₃ Φ B Δ x) ⟩
    xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ
      (xweaken+ Φ Ψ (B ++ Δ) (caseʳ (case₃ Φ B Δ x))))
  ≡⟨ cong (xweaken+ (Φ ++ Ψ ++ B) Γ Δ ∘ case (Φ ++ Ψ ++ B) Δ ∘ xweaken+ Φ Ψ (B ++ Δ))
       (caseʳ₃ Φ B Δ x) ⟩
    xweaken+ (Φ ++ Ψ ++ B) Γ Δ (case (Φ ++ Ψ ++ B) Δ (xweaken+ Φ Ψ (B ++ Δ) (case Φ (B ++ Δ) x)))
  ∎)
