import FRP.JS.Model.STLambdaC.Typ

open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; cong ; cong₂ ; subst ; subst-natural ; begin_ ; _≡⟨_⟩_ ; _∎ ; _∘_ ; ⊥ )

module FRP.JS.Model.STLambdaC.Exp 
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Var ; Ctxt ; const ; _⇝_
  ; [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; _⋙_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫ ; case-⋙
  ; Case₃ ; case₃ ; caseˡ ; caseʳ ; caseˡ₃ ; caseʳ₃ ; case⁻¹ ; case-iso )

-- Syntax

data Exp (Γ : Ctxt) : Typ → Set where
  const : ∀ {T} → Const T → Exp Γ T
  abs : ∀ T {U} → Exp (T ∷ Γ) U → Exp Γ (T ⇝ U)
  app : ∀ {T U} → Exp Γ (T ⇝ U) → Exp Γ T → Exp Γ U
  var : ∀ {T} → (T ∈ Γ) → Exp Γ T

-- Shorthand

var₀ : ∀ {Γ T} → Exp (T ∷ Γ) T
var₀ {Γ} {T} = var (singleton T ≪ Γ)

var₁ : ∀ {Γ T U} → Exp (U ∷ (T ∷ Γ)) T
var₁ {Γ} {T} {U} = var ([ U ] ≫ singleton T ≪ Γ)

var₂ : ∀ {Γ T U V} → Exp (V ∷ (U ∷ (T ∷ Γ))) T
var₂ {Γ} {T} {U} {V} = var ([ V ] ≫ [ U ] ≫ singleton T ≪ Γ)

-- Andreas Abel suggested defining substitution and renaming together, citing:
--
--   Conor McBride
--   Type Preserving Renaming and Substitution
--
--   Thorsten Altenkirch and Bernhard Reus
--   Monadic Presentations of Lambda Terms Using Generalized Inductive Types
--
-- http://www2.tcs.ifi.lmu.de/~abel/ParallelSubstitution.agda

-- The idea is to define two kinds, for expressions and variables,
-- such that the kind of variables is contained in the kind of
-- expressions (so admits recursion).

mutual

  data Kind : Set where
    var : Kind
    exp : ∀ {k} → IsVar k → Kind

  data IsVar : Kind → Set where
    var : IsVar var

Thing : Kind → Ctxt → Typ → Set
Thing var       Γ T = (T ∈ Γ)
Thing (exp var) Γ T = Exp Γ T
 
Substn : Kind → Ctxt → Ctxt → Set
Substn k Γ Δ = ∀ {T} → (T ∈ Δ) → Thing k Γ T

-- Convert between variables, things and expressions

thing : ∀ {k Γ T} → (T ∈ Γ) → Thing k Γ T
thing {var}     x = x
thing {exp var} x = var x

expr : ∀ {k Γ T} → Thing k Γ T → Exp Γ T
expr {var}     x = var x
expr {exp var} M = M

-- Extensional equivalence on substitutions (note: not assuming extensionality)

_≈_ : ∀ {k Γ Δ} → Substn k Γ Δ → Substn k Γ Δ → Set
ρ ≈ σ = ∀ {T} x → ρ {T} x ≡ σ {T} x

-- Identity substitution

id : ∀ {k} Γ → Substn k Γ Γ
id {var}     Γ x = x
id {exp var} Γ x = var x

-- Product structure of substitutions

fst : ∀ Γ Δ → Substn var (Γ ++ Δ) Γ
fst Γ Δ x = x ≪ Δ

snd : ∀ Γ Δ → Substn var (Γ ++ Δ) Δ
snd Γ Δ x = Γ ≫ x

choose : ∀ {k Γ Δ E T} → Substn k Γ Δ → Substn k Γ E → (Case T Δ E) → Thing k Γ T
choose ρ σ (inj₁ x) = ρ x
choose ρ σ (inj₂ x) = σ x

_&&&_ : ∀ {k Γ Δ E} → Substn k Γ Δ → Substn k Γ E → Substn k Γ (Δ ++ E)
(ρ &&& σ) = choose ρ σ ∘ case _ _

-- Singleton substitution

⟨_⟩ : ∀ {k Γ T} → Thing k Γ T → Substn k Γ [ T ]
⟨ M ⟩ x = subst (Thing _ _) (uniq x) M

-- Cons on substitutions

_◁_ : ∀ {k Γ Δ T} → Thing k Γ T → Substn k Γ Δ → Substn k Γ (T ∷ Δ)
M ◁ σ = ⟨ M ⟩ &&& σ

-- Applying a substitution

mutual

  substn+ : ∀ {k} B Γ Δ → Substn k Γ Δ → ∀ {T} → Exp (B ++ Δ) T → Exp (B ++ Γ) T
  substn+ B Γ Δ σ (const c) = const c
  substn+ B Γ Δ σ (abs T M) = abs T (substn+ (T ∷ B) Γ Δ σ M)
  substn+ B Γ Δ σ (app M N) = app (substn+ B Γ Δ σ M) (substn+ B Γ Δ σ N)
  substn+ B Γ Δ σ (var x)   = expr (xsubstn+ B Γ Δ σ (case B Δ x))

  xsubstn+ : ∀ {k} B Γ Δ → Substn k Γ Δ → ∀ {T} → (Case T B Δ) → Thing k (B ++ Γ) T
  xsubstn+           B Γ Δ σ (inj₁ x) = thing (x ≪ Γ)
  xsubstn+ {var}     B Γ Δ σ (inj₂ x) = B ≫ σ x
  xsubstn+ {exp var} B Γ Δ σ (inj₂ x) = substn+ [] (B ++ Γ) Γ (snd B Γ) (σ x) -- weaken* B (σ x)

-- Shorthands

substn* : ∀ {k Γ Δ} → Substn k Γ Δ → ∀ {T} → Exp Δ T → Exp Γ T
substn* {k} {Γ} {Δ} = substn+ [] Γ Δ

substn : ∀ {Γ T U} → Exp Γ T → Exp (T ∷ Γ) U → Exp Γ U
substn {Γ} M = substn* (M ◁ id Γ)

xweaken+ : ∀ B Γ Δ {T} → (T ∈ (B ++ Δ)) → (T ∈ (B ++ Γ ++ Δ))
xweaken+ B Γ Δ x = xsubstn+ B (Γ ++ Δ) Δ (snd Γ Δ) (case B Δ x)

weaken+ : ∀ B Γ Δ {T} → Exp (B ++ Δ) T → Exp (B ++ Γ ++ Δ) T
weaken+ B Γ Δ = substn+ B (Γ ++ Δ) Δ (snd Γ Δ)

weaken* : ∀ Γ {Δ T} → Exp Δ T → Exp (Γ ++ Δ) T
weaken* Γ {Δ} = weaken+ [] Γ Δ 

weakens* : ∀ {Γ Δ} E → Substn (exp var) Γ Δ → Substn (exp var) (E ++ Γ) Δ
weakens* E σ x = weaken* E (σ x)

weaken*ʳ : ∀ {Γ} Δ {T} → Exp Γ T → Exp (Γ ++ Δ) T
weaken*ʳ {Γ} Δ = weaken+ Γ Δ []

weaken : ∀ {Γ} T {U} → Exp Γ U → Exp (T ∷ Γ) U
weaken T = weaken* [ T ]

-- Composition of substitutions

_⊔_ : Kind → Kind → Kind
k ⊔ var     = k
k ⊔ exp var = exp var

_∙_ : ∀ {k l Γ Δ E} → Substn k Γ Δ → Substn l Δ E → Substn (k ⊔ l) Γ E
_∙_ {k} {var}     ρ σ = ρ ∘ σ
_∙_ {k} {exp var} ρ σ = substn* ρ ∘ σ

-- Functorial action of ++ on substitutions

par : ∀ {k Γ Δ Φ Ψ T} → Substn k Γ Φ → Substn k Δ Ψ → (Case T Φ Ψ) → Thing k (Γ ++ Δ) T
par {var}     {Γ} {Δ} ρ σ (inj₁ x) = ρ x ≪ Δ
par {var}     {Γ} {Δ} ρ σ (inj₂ x) = Γ ≫ σ x
par {exp var} {Γ} {Δ} ρ σ (inj₁ x) = weaken*ʳ Δ (ρ x)
par {exp var} {Γ} {Δ} ρ σ (inj₂ x) = weaken*  Γ (σ x)

_+++_ : ∀ {k Γ Δ Φ Ψ} → Substn k Γ Δ → Substn k Φ Ψ → Substn k (Γ ++ Φ) (Δ ++ Ψ)
(ρ +++ σ) = par ρ σ ∘ case _ _

-- Weakening a variable is a variable

weaken*-var : ∀ Γ {Δ T} (x : T ∈ Δ) →
  weaken* Γ (var x) ≡ var (Γ ≫ x)
weaken*-var Γ {Δ} x = cong (expr ∘ xsubstn+ [] (Γ ++ Δ) Δ (snd Γ Δ)) (case-≫ [] x)

weaken*ʳ-var : ∀ {Γ} Δ {T} (x : T ∈ Γ) →
  weaken*ʳ Δ (var x) ≡ var (x ≪ Δ)
weaken*ʳ-var {Γ} Δ x = cong (expr ∘ xsubstn+ Γ Δ [] (snd Δ [])) (case-≪ x [])

weaken+-var₀ : ∀ B Γ Δ {T} →
  weaken+ (T ∷ B) Γ Δ (var₀ {B ++ Δ}) ≡ var₀ {B ++ Γ ++ Δ}
weaken+-var₀ B Γ Δ {T} = 
  cong (var ∘ xsubstn+ (T ∷ B) (Γ ++ Δ) Δ (snd Γ Δ)) (case-≪ (singleton T ≪ B) Δ)

-- Substitution respects extensional equality

substn+-cong : ∀ {k} B Γ Δ {σ : Substn k Γ Δ} {ρ : Substn k Γ Δ} → 
  (σ ≈ ρ) → ∀ {T} M → substn+ B Γ Δ σ {T} M ≡ substn+ B Γ Δ ρ M
substn+-cong B Γ Δ σ≈ρ (const c) = refl
substn+-cong B Γ Δ σ≈ρ (abs T M) = cong (abs {B ++ Γ} T) (substn+-cong (T ∷ B) Γ Δ σ≈ρ M)
substn+-cong B Γ Δ σ≈ρ (app M N) = cong₂ app (substn+-cong B Γ Δ σ≈ρ M) (substn+-cong B Γ Δ σ≈ρ N)
substn+-cong B Γ Δ σ≈ρ (var x)   = cong expr (xsubstn+-cong B Γ Δ σ≈ρ (case B Δ x)) where

  xsubstn+-cong : ∀ {k} B Γ Δ {σ : Substn k Γ Δ} {ρ : Substn k Γ Δ} → 
    (σ ≈ ρ) → ∀ {T} x → xsubstn+ B Γ Δ σ {T} x ≡ xsubstn+ B Γ Δ ρ x
  xsubstn+-cong {var}     B Γ Δ σ≈ρ (inj₁ x) = refl
  xsubstn+-cong {exp var} B Γ Δ σ≈ρ (inj₁ x) = refl
  xsubstn+-cong {var}     B Γ Δ σ≈ρ (inj₂ x) = cong (_≫_ B) (σ≈ρ x)
  xsubstn+-cong {exp var} B Γ Δ σ≈ρ (inj₂ x) = cong (substn+ [] (B ++ Γ) Γ (snd B Γ)) (σ≈ρ x)

substn*-cong : ∀ {k Γ Δ} {σ : Substn k Γ Δ} {ρ : Substn k Γ Δ} → 
  (σ ≈ ρ) → ∀ {T} M → substn* σ {T} M ≡ substn* ρ M
substn*-cong {k} {Γ} {Δ} = substn+-cong [] Γ Δ

-- Identity of substitutions

xsubstn+-id : ∀ {k} B Γ {T} (x : Case T B Γ) →
  expr (xsubstn+ B Γ Γ (id {k} Γ) x) ≡ var (case⁻¹ x)
xsubstn+-id {var}     B Γ (inj₁ x) = refl
xsubstn+-id {exp var} B Γ (inj₁ x) = refl
xsubstn+-id {var}     B Γ (inj₂ x) = refl
xsubstn+-id {exp var} B Γ (inj₂ x) = weaken*-var B x

substn+-id : ∀ {k} B Γ {T} (M : Exp (B ++ Γ) T) → substn+ B Γ Γ (id {k} Γ) M ≡ M
substn+-id B Γ (const c) = refl
substn+-id B Γ (abs T M) = cong (abs {B ++ Γ} T) (substn+-id (T ∷ B) Γ M)
substn+-id B Γ (app M N) = cong₂ app (substn+-id B Γ M) (substn+-id B Γ N)
substn+-id {k} B Γ (var x)   =
  begin
    substn+ B Γ Γ (id {k} Γ) (var x)
  ≡⟨ xsubstn+-id {k} B Γ (case B Γ x) ⟩
    var (case⁻¹ (case B Γ x))
  ≡⟨ cong var (case-iso B Γ x) ⟩
    var x
  ∎

substn*-id : ∀ {k Γ T} (M : Exp Γ T) → substn* (id {k} Γ) M ≡ M
substn*-id {k} {Γ} = substn+-id [] Γ

weaken*-[] : ∀ {Γ T} (M : Exp Γ T) → weaken* [] M ≡ M
weaken*-[] M = substn*-id M

mutual
  
  -- Composition of substitutions
  
  substn+-∙ : ∀ {k l} B Γ Δ E (σ : Substn k Γ Δ) (ρ : Substn l Δ E) {T} (M : Exp (B ++ E) T) →
    (substn+ B Γ Δ σ (substn+ B Δ E ρ M) ≡ substn+ B Γ E (σ ∙ ρ) M)
  substn+-∙ B Γ Δ E ρ σ (const c) = refl
  substn+-∙ B Γ Δ E ρ σ (abs T M) = cong (abs {B ++ Γ} T) (substn+-∙ (T ∷ B) Γ Δ E ρ σ M)
  substn+-∙ B Γ Δ E ρ σ (app M N) = cong₂ app (substn+-∙ B Γ Δ E ρ σ M) (substn+-∙ B Γ Δ E ρ σ N)
  substn+-∙ B Γ Δ E ρ σ (var x)   = xsubstn+-∙ B Γ Δ E ρ σ (case B E x) where
  
    xsubstn+-∙ : ∀ {k l} B Γ Δ E (σ : Substn k Γ Δ) (ρ : Substn l Δ E) {T} (x : Case T B E) →
      (substn+ B Γ Δ σ (expr (xsubstn+ B Δ E ρ x)) ≡ expr (xsubstn+ B Γ E (σ ∙ ρ) x))
    xsubstn+-∙ {k}       {var}     B Γ Δ E σ ρ (inj₁ x) = 
      cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {var}     {exp var} B Γ Δ E σ ρ (inj₁ x) = 
      cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {exp var} {exp var} B Γ Δ E σ ρ (inj₁ x) = 
      cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {var}     {var}     B Γ Δ E σ ρ (inj₂ x) = 
      cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≫ B (ρ x))
    xsubstn+-∙ {exp var} {var}     B Γ Δ E σ ρ (inj₂ x) =
      cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≫ B (ρ x))
    xsubstn+-∙ {var}     {exp var} B Γ Δ E σ ρ (inj₂ x) = 
      begin
        substn+ B Γ Δ σ (weaken* B (ρ x))
      ≡⟨ substn+* B Γ Δ σ (weaken* B (ρ x)) ⟩
        substn* (id B +++ σ) (weaken* B (ρ x))
      ≡⟨ substn+-∙ [] (B ++ Γ) (B ++ Δ) Δ (id B +++ σ) (snd B Δ) (ρ x) ⟩
        substn* ((id B +++ σ) ∙ snd B Δ) (ρ x)
      ≡⟨ substn*-cong (λ y → cong (par (id B) σ) (case-≫ B y)) (ρ x) ⟩
        substn* (snd B Γ ∙ σ) (ρ x)
      ≡⟨ sym (substn+-∙ [] (B ++ Γ) Γ Δ (snd B Γ) σ (ρ x)) ⟩
        weaken* B (substn* σ (ρ x))
      ∎
    xsubstn+-∙ {exp var} {exp var} B Γ Δ E σ ρ (inj₂ x) = 
      begin
        substn+ B Γ Δ σ (weaken* B (ρ x))
      ≡⟨ substn+* B Γ Δ σ (weaken* B (ρ x)) ⟩
        substn* (id B +++ σ) (weaken* B (ρ x))
      ≡⟨ substn+-∙ [] (B ++ Γ) (B ++ Δ) Δ (id B +++ σ) (snd B Δ) (ρ x) ⟩
        substn* ((id B +++ σ) ∙ snd B Δ) (ρ x)
      ≡⟨ substn*-cong (λ y → cong (par (id B) σ) (case-≫ B y))(ρ x) ⟩
        substn* (snd B Γ ∙ σ) (ρ x)
      ≡⟨ sym (substn+-∙ [] (B ++ Γ) Γ Δ (snd B Γ) σ (ρ x)) ⟩
        weaken* B (substn* σ (ρ x))
      ∎
  
  substn*-∙ : ∀ {k l Γ Δ E} (σ : Substn k Γ Δ) (ρ : Substn l Δ E) {T} (M : Exp E T) →
    (substn* σ (substn* ρ M) ≡ substn* (σ ∙ ρ) M)
  substn*-∙ {k} {l} {Γ} {Δ} {E} = substn+-∙ [] Γ Δ E

  -- Proof uses the fact that substn+ is an instance of substn*

  substn++ : ∀ {k} A B Γ Δ (σ : Substn k Γ Δ) {T} (M : Exp (A ++ B ++ Δ) T) → 
    substn+ (A ++ B) Γ Δ σ M ≡ substn+ A (B ++ Γ) (B ++ Δ) (id B +++ σ) M
  substn++ A B Γ Δ σ (const c) = refl
  substn++ A B Γ Δ σ (abs T M) = cong (abs {A ++ B ++ Γ} T) (substn++ (T ∷ A) B Γ Δ σ M)
  substn++ A B Γ Δ σ (app M N) = cong₂ app (substn++ A B Γ Δ σ M) (substn++ A B Γ Δ σ N)
  substn++ A B Γ Δ σ (var x)   = cong expr (begin
      xsubstn+ (A ++ B) Γ Δ σ (case (A ++ B) Δ x)
    ≡⟨ cong (xsubstn+ (A ++ B) Γ Δ σ) (sym (caseˡ₃ A B Δ x)) ⟩
      xsubstn+ (A ++ B) Γ Δ σ (caseˡ (case₃ A B Δ x))
    ≡⟨ xsubstn++ A B Γ Δ σ (case₃ A B Δ x) ⟩
      xsubstn+ A (B ++ Γ) (B ++ Δ) (id B +++ σ) (caseʳ (case₃ A B Δ x))
    ≡⟨ cong (xsubstn+ A (B ++ Γ) (B ++ Δ) (id B +++ σ)) (caseʳ₃ A B Δ x) ⟩
      xsubstn+ A (B ++ Γ) (B ++ Δ) (id B +++ σ) (case A (B ++ Δ) x)
    ∎) where
  
    xsubstn++ : ∀ {k} A B Γ Δ (σ : Substn k Γ Δ) {T} (x : Case₃ T A B Δ) →
      xsubstn+ (A ++ B) Γ Δ σ (caseˡ x) ≡ xsubstn+ A (B ++ Γ) (B ++ Δ) (id B +++ σ) (caseʳ x)
    xsubstn++           A B Γ Δ σ (inj₁ x) = refl
    xsubstn++ {var}     A B Γ Δ σ (inj₂ x) = cong (λ X → A ≫ par (id B) σ X) (sym (case-≪ x Δ))
    xsubstn++ {exp var} A B Γ Δ σ (inj₂ x) = 
      begin
        var (A ≫ x ≪ Γ)
      ≡⟨ sym (weaken*-var A (x ≪ Γ)) ⟩
        weaken* A (var (x ≪ Γ))
      ≡⟨ cong (weaken* A) (sym (weaken*ʳ-var Γ x)) ⟩
        weaken* A (weaken*ʳ Γ (var x))
      ≡⟨ cong (weaken* A ∘ par (id B) σ) (sym (case-≪ x Δ)) ⟩
        weaken* A ((id B +++ σ) (x ≪ Δ))
      ∎
    xsubstn++ {var}     A B Γ Δ σ (inj₃ x) = cong (λ X → A ≫ par (id B) σ X) (sym (case-≫ B x))
    xsubstn++ {exp var} A B Γ Δ σ (inj₃ x) = 
      begin
        weaken* (A ++ B) (σ x)
      ≡⟨ sym (substn*-∙ (snd A (B ++ Γ)) (snd B Γ) (σ x)) ⟩
        weaken* A (weaken* B (σ x))
      ≡⟨ cong (weaken* A ∘ par (id B) σ) (sym (case-≫ B x)) ⟩
        weaken* A ((id B +++ σ) (B ≫ x))
      ∎
  
  substn+* : ∀ {k} B Γ Δ (σ : Substn k Γ Δ) {T} (M : Exp (B ++ Δ) T) → 
    substn+ B Γ Δ σ M ≡ substn* (id B +++ σ) M
  substn+* = substn++ []

-- Weakening of weakening is weakening

weaken*-++ : ∀ A B Γ {T} (M : Exp Γ T) →
  weaken* A (weaken* B M) ≡ weaken* (A ++ B) M
weaken*-++ A B Γ = substn*-∙ (snd A (B ++ Γ)) (snd B Γ)

-- Weakening commutes with weakening

weaken*-comm : ∀ A B Γ Δ {U} (M : Exp (B ++ Δ) U) →
  weaken* A (weaken+ B Γ Δ M)
    ≡ weaken+ (A ++ B) Γ Δ (weaken* A M)
weaken*-comm A B Γ Δ M = 
  begin
    weaken* A (weaken+ B Γ Δ M)
  ≡⟨ cong (substn* (snd A (B ++ Γ ++ Δ))) (substn+* B (Γ ++ Δ) Δ (snd Γ Δ) M) ⟩
    substn* (snd A (B ++ Γ ++ Δ)) (substn* (id B +++ snd Γ Δ) M)
  ≡⟨ substn*-∙ (snd A (B ++ Γ ++ Δ)) (id B +++ snd Γ Δ) M ⟩
    substn* (snd A (B ++ Γ ++ Δ) ∙ (id B +++ snd Γ Δ)) M
  ≡⟨ substn*-cong lemma₂ M ⟩
    substn* ((id (A ++ B) +++ snd Γ Δ) ∙ snd A (B ++ Δ)) M
  ≡⟨ sym (substn*-∙ (id (A ++ B) +++ snd Γ Δ) (snd A (B ++ Δ)) M) ⟩
    substn* (id (A ++ B) +++ snd Γ Δ) (substn* (snd A (B ++ Δ)) M)
  ≡⟨ sym (substn+* (A ++ B) (Γ ++ Δ) Δ (snd Γ Δ) (substn* (snd A (B ++ Δ)) M)) ⟩
    weaken+ (A ++ B) Γ Δ (weaken* A M)
  ∎ where
  
  lemma₁ : ∀ {T} (x : Case T B Δ) → 
    snd A (B ++ Γ ++ Δ) (par (id B) (snd Γ Δ) x) 
      ≡ (par (id (A ++ B)) (snd Γ Δ) (A ⋙ x))
  lemma₁ (inj₁ x) = refl
  lemma₁ (inj₂ x) = refl

  lemma₂ : (snd A (B ++ Γ ++ Δ) ∙ (id B +++ snd Γ Δ)) ≈ ((id (A ++ B) +++ snd Γ Δ) ∙ snd A (B ++ Δ))
  lemma₂ {T} x = 
    begin
      snd A (B ++ Γ ++ Δ) (par (id B) (snd Γ Δ) (case B Δ x)) 
    ≡⟨ lemma₁ (case B Δ x) ⟩
      par (id (A ++ B)) (snd Γ Δ) (A ⋙ (case B Δ x))
    ≡⟨ cong (par (id (A ++ B)) (snd Γ Δ)) (case-⋙ A B Δ x) ⟩
      par (id (A ++ B)) (snd Γ Δ) (case (A ++ B) Δ (A ≫ x))
    ∎

weaken-comm : ∀ T B Γ Δ {U} (M : Exp (B ++ Δ) U) →
  weaken T (weaken+ B Γ Δ M)
    ≡ weaken+ (T ∷ B) Γ Δ (weaken T M)
weaken-comm T = weaken*-comm [ T ]

-- Weakening distributes through susbtn

weaken-substn : ∀ B Γ Δ {T U} (M : Exp (B ++ Δ) T) (N : Exp (T ∷ B ++ Δ) U) →
  substn (weaken+ B Γ Δ M) (weaken+ (T ∷ B) Γ Δ N)
    ≡ weaken+ B Γ Δ (substn M N)
weaken-substn B Γ Δ {T} M N = begin
    substn (weaken+ B Γ Δ M) (weaken+ (T ∷ B) Γ Δ N)
  ≡⟨ cong₂ substn (substn+* B (Γ ++ Δ) Δ (snd Γ Δ) M) (substn+* (T ∷ B) (Γ ++ Δ) Δ (snd Γ Δ) N) ⟩
    substn (substn* (id B +++ snd Γ Δ) M) (substn* (id (T ∷ B) +++ snd Γ Δ) N)
  ≡⟨ substn*-∙ (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) (id (T ∷ B) +++ snd Γ Δ) N ⟩
    substn* ((substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) ∙ (id (T ∷ B) +++ snd Γ Δ)) N
  ≡⟨ substn*-cong lemma₂ N ⟩
    substn* ((id B +++ snd Γ Δ) ∙ (M ◁ id (B ++ Δ))) N
  ≡⟨ sym (substn*-∙ (id B +++ snd Γ Δ) (M ◁ id (B ++ Δ)) N) ⟩
    substn* (id B +++ snd Γ Δ) (substn M N)
  ≡⟨ sym (substn+* B (Γ ++ Δ) Δ (snd Γ Δ) (substn M N)) ⟩
    weaken+ B Γ Δ (substn M N)
  ∎ where

  lemma₁ : ∀ {S} (x : Case₃ S [ T ] B Δ) → 
    (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) 
      (par (id (T ∷ B)) (snd Γ Δ) (caseˡ x))
        ≡ substn* (id B +++ snd Γ Δ)
            (choose ⟨ M ⟩ (id (B ++ Δ)) (caseʳ x))
  lemma₁ (inj₁ x) = begin
      (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) (x ≪ B ≪ Γ ≪ Δ)
    ≡⟨ cong (choose ⟨ substn* (id B +++ snd Γ Δ) M ⟩ (id (B ++ Γ ++ Δ))) (case-≪ x (B ++ Γ ++ Δ)) ⟩
      ⟨ substn* (id B +++ snd Γ Δ) M ⟩ x
    ≡⟨ subst-natural (uniq x) (substn* (id B +++ snd Γ Δ)) M ⟩
      substn* (id B +++ snd Γ Δ) (⟨ M ⟩ x)
    ∎
  lemma₁ (inj₂ x) = begin
      (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) ([ T ] ≫ x ≪ Γ ≪ Δ)
    ≡⟨ cong (choose ⟨ substn* (id B +++ snd Γ Δ) M ⟩ (id (B ++ Γ ++ Δ))) (case-≫ [ T ] (x ≪ Γ ≪ Δ)) ⟩
      var (x ≪ Γ ≪ Δ)
    ≡⟨ cong (var ∘ par (id B) (snd Γ Δ)) (sym (case-≪ x Δ)) ⟩
      var ((id B +++ snd Γ Δ) (x ≪ Δ))
    ≡⟨ cong (var ∘ xsubstn+ [] (B ++ Γ ++ Δ) (B ++ Δ) (id B +++ snd Γ Δ)) (sym (case-≫ [] (x ≪ Δ))) ⟩
      substn* (id B +++ snd Γ Δ) (var (x ≪ Δ))
    ∎
  lemma₁ (inj₃ x) = begin
      (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) ([ T ] ≫ B ≫ Γ ≫ x)
    ≡⟨ cong (choose ⟨ substn* (id B +++ snd Γ Δ) M ⟩ (id (B ++ Γ ++ Δ))) (case-≫ [ T ] (B ≫ Γ ≫ x)) ⟩
      var (B ≫ Γ ≫ x)
    ≡⟨ cong (var ∘ par (id B) (snd Γ Δ)) (sym (case-≫ B x)) ⟩
      var ((id B +++ snd Γ Δ) (B ≫ x))
    ≡⟨ cong (var ∘ xsubstn+ [] (B ++ Γ ++ Δ) (B ++ Δ) (id B +++ snd Γ Δ)) (sym (case-≫ [] (B ≫ x))) ⟩
      substn* (id B +++ snd Γ Δ) (var (B ≫ x))
    ∎

  lemma₂ : ((substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) ∙ (id (T ∷ B) +++ snd Γ Δ))
    ≈ ((id B +++ snd Γ Δ) ∙ (M ◁ id (B ++ Δ)))
  lemma₂ {S} x = begin
      ((substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) ∙ (id (T ∷ B) +++ snd Γ Δ)) x
    ≡⟨ cong (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ) ∘ par (id (T ∷ B)) (snd Γ Δ)) 
         (sym (caseˡ₃ [ T ] B Δ x)) ⟩
      (substn* (id B +++ snd Γ Δ) M ◁ id (B ++ Γ ++ Δ)) 
        (par (id (T ∷ B)) (snd Γ Δ) (caseˡ (case₃ [ T ] B Δ x)))
    ≡⟨ lemma₁ (case₃ [ T ] B Δ x) ⟩
      substn* (id B +++ snd Γ Δ)
        (choose ⟨ M ⟩ (id (B ++ Δ)) (caseʳ (case₃ [ T ] B Δ x)))
    ≡⟨ cong (substn* (id B +++ snd Γ Δ) ∘ choose ⟨ M ⟩ (id (B ++ Δ)))
         (caseʳ₃ [ T ] B Δ x) ⟩
      ((id B +++ snd Γ Δ) ∙ (M ◁ id (B ++ Δ))) x
    ∎

-- Substitution into weakening discards the substitution

substn-weaken : ∀ {Γ T U} (M : Exp Γ U) (N : Exp Γ T) →
  substn N (weaken T M) ≡ M
substn-weaken {Γ} {T} M N = 
  begin
    substn N (weaken T M)
  ≡⟨ substn*-∙ (N ◁ id Γ) (snd [ T ] Γ) M ⟩
    substn* ((N ◁ id Γ) ∙ snd [ T ] Γ) M
  ≡⟨ substn*-cong (λ x → cong (choose ⟨ N ⟩ (id Γ)) (case-≫ [ T ] x)) M ⟩
    substn* (id Γ) M
  ≡⟨ substn*-id M ⟩
    M
  ∎ 

-- Substitution + weakening respects ◁

substn*-◁ : ∀ Γ Δ E {T U} (M : Exp (T ∷ Γ) U) (N : Exp (E ++ Δ) T) (σ : Substn (exp var) Δ Γ) →
  substn* (N ◁ weakens* E σ) M
    ≡ substn N (weaken+ [ T ] E Δ (substn+ [ T ] Δ Γ σ M))
substn*-◁ Γ Δ E {T} M N σ =
  begin
    substn* (N ◁ weakens* E σ) M
  ≡⟨ substn*-cong (λ x → lemma (case [ T ] Γ x)) M ⟩
    substn* ((N ◁ id (E ++ Δ)) ∙ (id [ T ] +++ (snd E Δ ∙ σ))) M
  ≡⟨ sym (substn*-∙ (N ◁ id (E ++ Δ)) (id [ T ] +++ (snd E Δ ∙ σ)) M) ⟩
    substn N (substn* (id [ T ] +++ (snd E Δ ∙ σ)) M)
  ≡⟨ cong (substn N) (sym (substn+* [ T ] (E ++ Δ) Γ (snd E Δ ∙ σ) M)) ⟩
    substn N (substn+ [ T ] (E ++ Δ) Γ (snd E Δ ∙ σ) M)
  ≡⟨ cong (substn N) (sym (substn+-∙ [ T ] (E ++ Δ) Δ Γ (snd E Δ) σ M)) ⟩
    substn N (weaken+ [ T ] E Δ (substn+ [ T ] Δ Γ σ M))
  ∎ where

  lemma : ∀ {U} (x : Case U [ T ] Γ) → 
    choose ⟨ N ⟩ (weakens* E σ) x
      ≡ substn N (par (id [ T ]) (snd E Δ ∙ σ) x)
  lemma (inj₁ x) =
    begin
      subst (Exp (E ++ Δ)) (uniq x) N
    ≡⟨ cong (choose ⟨ N ⟩ (id (E ++ Δ))) (sym (case-≪ x (E ++ Δ))) ⟩
      (N ◁ id (E ++ Δ)) (x ≪ E ≪ Δ)
    ≡⟨ sym (weaken*-[] ((N ◁ id (E ++ Δ)) (x ≪ E ≪ Δ))) ⟩
      weaken* [] ((N ◁ id (E ++ Δ)) (x ≪ E ≪ Δ))
    ≡⟨ cong (xsubstn+ [] (E ++ Δ) ([ T ] ++ E ++ Δ) (N ◁ id (E ++ Δ))) 
         (sym (case-≫ [] (x ≪ E ≪ Δ))) ⟩
     substn N (var (x ≪ E ≪ Δ))
    ≡⟨ cong (substn N) (sym (weaken*ʳ-var (E ++ Δ) x)) ⟩
     substn N (weaken*ʳ (E ++ Δ) (var x))
    ∎
  lemma (inj₂ x) = sym (substn-weaken (weaken* E (σ x)) N)
