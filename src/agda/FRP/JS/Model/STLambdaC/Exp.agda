import FRP.JS.Model.STLambdaC.Typ

open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; begin_ ; _≡⟨_⟩_ ; _∎ ; _∘_ )

module FRP.JS.Model.STLambdaC.Exp 
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Var ; Ctxt ; const ; _⇝_
  ; [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; _⋙_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫ ; case-⋙
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

xsubstn : ∀ Δ E {T U} → Case U [ T ] E → Exp (Δ ++ E) T → Exp (Δ ++ E) U
xsubstn Δ E (inj₁ x) N = subst (Exp (Δ ++ E)) (sym (uniq x)) N
xsubstn Δ E (inj₂ x) N = var (Δ ≫ x)

xsubstn+ : ∀ Γ Δ E {T U} → Case U Γ (T ∷ E) → Exp (Δ ++ E) T → Exp (Γ ++ Δ ++ E) U
xsubstn+ Γ Δ E (inj₁ x) N = var (x ≪ Δ ≪ E)
xsubstn+ Γ Δ E (inj₂ x) N = weaken* Γ (Δ ++ E) (xsubstn Δ E (case [ _ ] E x) N)

substn+ : ∀ Γ Δ E {T U} → Exp (Γ ++ T ∷ E) U → Exp (Δ ++ E) T → Exp (Γ ++ Δ ++ E) U
substn+ Γ Δ E {T} (const c) N = const c
substn+ Γ Δ E {T} (abs U M) N = abs U (substn+ (U ∷ Γ) Δ E M N)
substn+ Γ Δ E {T} (app L M) N = app (substn+ Γ Δ E L N) (substn+ Γ Δ E M N)
substn+ Γ Δ E {T} (var x)   N = xsubstn+ Γ Δ E (case Γ (T ∷ E) x) N 

substn : ∀ {Γ T U} → Exp (T ∷ Γ) U → Exp Γ T → Exp Γ U
substn {Γ} = substn+ [] [] Γ

-- Weakening var₀ is var₀

weaken+-var₀ : ∀ B Γ Δ {T} → 
  weaken+ (T ∷ B) Γ Δ (var₀ {B ++ Δ}) ≡ var₀ {B ++ Γ ++ Δ}
weaken+-var₀ B Γ Δ {T} = 
  cong var (cong (xweaken+ (T ∷ B) Γ Δ) (case-≪ (singleton T ≪ B) Δ))

-- Weakening commutes with weakening

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

-- Weakening commutes with substitution

subst-natural : ∀ {A : Set} {B C : A → Set} (f : ∀ a → B a → C a) {a₁ a₂} a₁≡a₂ b →
  f a₂ (subst B a₁≡a₂ b) ≡ subst C a₁≡a₂ (f a₁ b)
subst-natural f refl b = refl

weaken+-xsubstn : ∀ Φ Ψ Γ Δ {T U} (x : Case₃ U [ T ] Φ Ψ) N → 
  weaken+ (Δ ++ Φ) Γ Ψ (xsubstn Δ (Φ ++ Ψ) {T} {U} (caseʳ x) N)
    ≡ xsubstn Δ (Φ ++ Γ ++ Ψ) 
        (case [ T ] (Φ ++ Γ ++ Ψ) (xweaken+ (T ∷ Φ) Γ Ψ (caseˡ x))) 
        (weaken+ (Δ ++ Φ) Γ Ψ N)
weaken+-xsubstn Φ Ψ Γ Δ {T} (inj₁ x) N =
  begin
    weaken+ (Δ ++ Φ) Γ Ψ (subst (Exp (Δ ++ Φ ++ Ψ)) (sym (uniq x)) N)
  ≡⟨ subst-natural (λ T → weaken+ (Δ ++ Φ) Γ Ψ) (sym (uniq x)) N ⟩
    subst (Exp (Δ ++ Φ ++ Γ ++ Ψ)) (sym (uniq x)) (weaken+ (Δ ++ Φ) Γ Ψ N)
  ≡⟨ cong (λ X → xsubstn Δ (Φ ++ Γ ++ Ψ) X (weaken+ (Δ ++ Φ) Γ Ψ N)) 
       (sym (case-≪ x (Φ ++ Γ ++ Ψ))) ⟩
    xsubstn Δ (Φ ++ Γ ++ Ψ) 
      (case [ T ] (Φ ++ Γ ++ Ψ) (x ≪ Φ ≪ Γ ≪ Ψ))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎
weaken+-xsubstn Φ Ψ Γ Δ {T} (inj₂ x) N = 
  begin
    var (xweaken+ (Δ ++ Φ) Γ Ψ (case (Δ ++ Φ) Ψ (Δ ≫ x ≪ Ψ)))
  ≡⟨ cong (var ∘ xweaken+ (Δ ++ Φ) Γ Ψ) (case-≪ (Δ ≫ x) Ψ) ⟩
    var (Δ ≫ x ≪ Γ ≪ Ψ)
  ≡⟨ cong (λ X → xsubstn Δ (Φ ++ Γ ++ Ψ) X (weaken+ (Δ ++ Φ) Γ Ψ N))
       (sym (case-≫ [ T ] (x ≪ Γ ≪ Ψ))) ⟩
     xsubstn Δ (Φ ++ Γ ++ Ψ) 
        (case [ T ] (Φ ++ Γ ++ Ψ) ([ T ] ≫ x ≪ Γ ≪ Ψ))
        (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎
weaken+-xsubstn Φ Ψ Γ Δ {T} (inj₃ x) N =
  begin
    var (xweaken+ (Δ ++ Φ) Γ Ψ (case (Δ ++ Φ) Ψ (Δ ≫ Φ ≫ x)))
  ≡⟨ cong (var ∘ xweaken+ (Δ ++ Φ) Γ Ψ) (case-≫ (Δ ++ Φ) x) ⟩
    var (Δ ≫ Φ ≫ Γ ≫ x)
  ≡⟨ cong (λ X → xsubstn Δ (Φ ++ Γ ++ Ψ) X (weaken+ (Δ ++ Φ) Γ Ψ N))
       (sym (case-≫ [ T ] (Φ ≫ Γ ≫ x))) ⟩
     xsubstn Δ (Φ ++ Γ ++ Ψ) 
        (case [ T ] (Φ ++ Γ ++ Ψ) ([ T ] ≫ Φ ≫ Γ ≫ x))
        (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎

xweaken+-⋙ : ∀ B Γ Δ E {T} (x : Case T Γ E) →
  xweaken+ (B ++ Γ) Δ E (B ⋙ x)
    ≡ (B ≫ xweaken+ Γ Δ E x)
xweaken+-⋙ B Γ Δ E (inj₁ x) = refl
xweaken+-⋙ B Γ Δ E (inj₂ x) = refl

xweaken+-≫ : ∀ B Γ Δ E {T} (x : T ∈ (Γ ++ E)) →
  xweaken+ (B ++ Γ) Δ E (case (B ++ Γ) E (B ≫ x))
    ≡ (B ≫ xweaken+ Γ Δ E (case Γ E x))
xweaken+-≫ B Γ Δ E x = 
  begin
    xweaken+ (B ++ Γ) Δ E (case (B ++ Γ) E (B ≫ x))
  ≡⟨ cong (xweaken+ (B ++ Γ) Δ E) (sym (case-⋙ B Γ E x)) ⟩
    xweaken+ (B ++ Γ) Δ E (B ⋙ case Γ E x)
  ≡⟨ xweaken+-⋙ B Γ Δ E (case Γ E x) ⟩
    (B ≫ xweaken+ Γ Δ E (case Γ E x))
  ∎

weaken²-xsubstn : ∀ Φ Ψ B Γ Δ {T U} (x : U ∈ (T ∷ Φ ++ Ψ)) N → 
  weaken+ (B ++ Δ ++ Φ) Γ Ψ (weaken* B (Δ ++ Φ ++ Ψ)
    (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) x) N))
    ≡ xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
        (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (case (B ++ T ∷ Φ) Ψ (B ≫ x)))) 
        (weaken+ (Δ ++ Φ) Γ Ψ N)
weaken²-xsubstn Φ Ψ B Γ Δ {T} x N = 
  begin
    weaken+ (B ++ Δ ++ Φ) Γ Ψ (weaken* B (Δ ++ Φ ++ Ψ)
      (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) x) N))
  ≡⟨ sym (weaken+-weaken+ [] B (Δ ++ Φ) Γ Ψ (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) x) N)) ⟩
    weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (weaken+ (Δ ++ Φ) Γ Ψ
      (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) x) N))
  ≡⟨ cong (λ X → weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (weaken+ (Δ ++ Φ) Γ Ψ (xsubstn Δ (Φ ++ Ψ) X N)))
       (sym (caseʳ₃ [ T ] Φ Ψ x)) ⟩
    weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (weaken+ (Δ ++ Φ) Γ Ψ
      (xsubstn Δ (Φ ++ Ψ) (caseʳ (case₃ [ T ] Φ Ψ x)) N))
  ≡⟨ cong (weaken* B (Δ ++ Φ ++ Γ ++ Ψ)) (weaken+-xsubstn Φ Ψ Γ Δ (case₃ [ T ] Φ Ψ x) N) ⟩
    weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (xsubstn Δ (Φ ++ Γ ++ Ψ)
       (case [ T ] (Φ ++ Γ ++ Ψ) (xweaken+ (T ∷ Φ) Γ Ψ (caseˡ (case₃ [ T ] Φ Ψ x))))
       (weaken+ (Δ ++ Φ) Γ Ψ N))
  ≡⟨ cong (λ X → weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (xsubstn Δ (Φ ++ Γ ++ Ψ)
         (case [ T ] (Φ ++ Γ ++ Ψ) (xweaken+ (T ∷ Φ) Γ Ψ X))
         (weaken+ (Δ ++ Φ) Γ Ψ N)))
       (caseˡ₃ [ T ] Φ Ψ x) ⟩
    weaken* B (Δ ++ Φ ++ Γ ++ Ψ) (xsubstn Δ (Φ ++ Γ ++ Ψ)
       (case [ T ] (Φ ++ Γ ++ Ψ) (xweaken+ (T ∷ Φ) Γ Ψ (case (T ∷ Φ) Ψ x)))
       (weaken+ (Δ ++ Φ) Γ Ψ N))
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ) X (weaken+ (Δ ++ Φ) Γ Ψ N))
       (sym (case-≫ B (xweaken+ (T ∷ Φ) Γ Ψ (case (T ∷ Φ) Ψ x)))) ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ)
      (case B (T ∷ Φ ++ Γ ++ Ψ) (B ≫ xweaken+ (T ∷ Φ) Γ Ψ (case (T ∷ Φ) Ψ x)))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ) (case B (T ∷ Φ ++ Γ ++ Ψ) X) (weaken+ (Δ ++ Φ) Γ Ψ N))
       (sym (xweaken+-≫ B (T ∷ Φ) Γ Ψ x)) ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
      (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (case (B ++ T ∷ Φ) Ψ (B ≫ x)))) 
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎

weaken+-xsubstn+ : ∀ Φ Ψ B Γ Δ {T U} (x : Case₃ U B (T ∷ Φ) Ψ) N → 
  weaken+ (B ++ Δ ++ Φ) Γ Ψ (xsubstn+ B Δ (Φ ++ Ψ) {T} {U} (caseʳ x) N)
    ≡ xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
        (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (caseˡ x))) 
        (weaken+ (Δ ++ Φ) Γ Ψ N)
weaken+-xsubstn+ Φ Ψ B Γ Δ {T} (inj₁ x) N =
  begin
    var (xweaken+ (B ++ Δ ++ Φ) Γ Ψ (case (B ++ Δ ++ Φ) Ψ (x ≪ Δ ≪ Φ ≪ Ψ)))
  ≡⟨ cong (var ∘ xweaken+ (B ++ Δ ++ Φ) Γ Ψ) (case-≪ (x ≪ Δ ≪ Φ) Ψ) ⟩
    var (x ≪ Δ ≪ Φ ≪ Γ ≪ Ψ)
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ) X (weaken+ (Δ ++ Φ) Γ Ψ N))
       (sym (case-≪ x (T ∷ Φ ++ Γ ++ Ψ))) ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
      (case B (T ∷ Φ ++ Γ ++ Ψ) (x ≪ T ∷ Φ ≪ Γ ≪ Ψ))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎
weaken+-xsubstn+ Φ Ψ B Γ Δ {T} (inj₂ x) N = 
  begin
    weaken+ (B ++ Δ ++ Φ) Γ Ψ (weaken* B (Δ ++ Φ ++ Ψ)
      (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) (x ≪ Ψ)) N))
  ≡⟨ weaken²-xsubstn Φ Ψ B Γ Δ (x ≪ Ψ) N ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
      (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (case (B ++ T ∷ Φ) Ψ (B ≫ x ≪ Ψ))))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ)
         (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ X))
         (weaken+ (Δ ++ Φ) Γ Ψ N))
       (case-≪ (B ≫ x) Ψ) ⟩
   xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
     (case B (T ∷ Φ ++ Γ ++ Ψ) (B ≫ x ≪ Γ ≪ Ψ))
     (weaken+ (Δ ++ Φ) Γ Ψ N)    
  ∎
weaken+-xsubstn+ Φ Ψ B Γ Δ {T} {U} (inj₃ x) N =
  begin
    weaken+ (B ++ Δ ++ Φ) Γ Ψ (weaken* B (Δ ++ Φ ++ Ψ)
      (xsubstn Δ (Φ ++ Ψ) (case [ T ] (Φ ++ Ψ) (T ∷ Φ ≫ x)) N))
  ≡⟨ weaken²-xsubstn Φ Ψ B Γ Δ (T ∷ Φ ≫ x) N ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
      (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (case (B ++ T ∷ Φ) Ψ (B ≫ T ∷ Φ ≫ x))))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ)
         (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ X))
         (weaken+ (Δ ++ Φ) Γ Ψ N))
       (case-≫ (B ++ T ∷ Φ) x) ⟩
   xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
     (case B (T ∷ Φ ++ Γ ++ Ψ) (B ≫ T ∷ Φ ≫ Γ ≫ x))
     (weaken+ (Δ ++ Φ) Γ Ψ N)    
  ∎

weaken+-substn+ : ∀ Φ Ψ B Γ Δ {T U} M N → 
  weaken+ (B ++ Δ ++ Φ) Γ Ψ (substn+ B Δ (Φ ++ Ψ) {T} {U} M N)
    ≡ substn+ B Δ (Φ ++ Γ ++ Ψ) (weaken+ (B ++ T ∷ Φ) Γ Ψ M) (weaken+ (Δ ++ Φ) Γ Ψ N)
weaken+-substn+ Φ Ψ B Γ Δ (const c) N =
  refl
weaken+-substn+ Φ Ψ B Γ Δ (abs T M) N =
  cong (abs {B ++ Δ ++ Φ ++ Γ ++ Ψ} T) (weaken+-substn+ Φ Ψ (T ∷ B) Γ Δ M N)
weaken+-substn+ Φ Ψ B Γ Δ (app L M) N =
  cong₂ app (weaken+-substn+ Φ Ψ B Γ Δ L N) (weaken+-substn+ Φ Ψ B Γ Δ M N)
weaken+-substn+ Φ Ψ B Γ Δ {T} (var x) N = 
  begin
    weaken+ (B ++ Δ ++ Φ) Γ Ψ (xsubstn+ B Δ (Φ ++ Ψ) (case B (T ∷ Φ ++ Ψ) x) N)
  ≡⟨ cong (λ X → weaken+ (B ++ Δ ++ Φ) Γ Ψ (xsubstn+ B Δ (Φ ++ Ψ) X N))
       (sym (caseʳ₃ B (T ∷ Φ) Ψ x)) ⟩
    weaken+ (B ++ Δ ++ Φ) Γ Ψ (xsubstn+ B Δ (Φ ++ Ψ) (caseʳ (case₃ B (T ∷ Φ) Ψ x)) N)
  ≡⟨ weaken+-xsubstn+ Φ Ψ B Γ Δ (case₃ B (T ∷ Φ) Ψ x) N ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ)
      (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (caseˡ (case₃ B (T ∷ Φ) Ψ x))))
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ≡⟨ cong (λ X → xsubstn+ B Δ (Φ ++ Γ ++ Ψ)
         (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ X))
         (weaken+ (Δ ++ Φ) Γ Ψ N))
       (caseˡ₃ B (T ∷ Φ) Ψ x) ⟩
    xsubstn+ B Δ (Φ ++ Γ ++ Ψ) 
      (case B (T ∷ Φ ++ Γ ++ Ψ) (xweaken+ (B ++ T ∷ Φ) Γ Ψ (case (B ++ T ∷ Φ) Ψ x))) 
      (weaken+ (Δ ++ Φ) Γ Ψ N)
  ∎

weaken+-substn : ∀ B Γ Δ {T U} M N → 
  weaken+ B Γ Δ (substn {B ++ Δ} {T} {U} M N)
    ≡ substn {B ++ Γ ++ Δ} (weaken+ (T ∷ B) Γ Δ M) (weaken+ B Γ Δ N)
weaken+-substn = λ B Γ Δ → weaken+-substn+ B Δ [] Γ []
