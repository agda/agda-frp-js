import FRP.JS.Model.STLambdaC.Typ

open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; cong ; cong₂ ; subst ; begin_ ; _≡⟨_⟩_ ; _∎ ; _∘_ ; ⊥ )

module FRP.JS.Model.STLambdaC.Exp 
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Var ; Ctxt ; const ; _⇝_
  ; [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; _⋙_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫ ; case-⋙
  ; Case₃ ; case₃ ; caseˡ ; caseʳ ; caseˡ₃ ; caseʳ₃ )

-- Syntax

data Exp (Γ : Ctxt) : Typ → Set where
  const : ∀ {T} → Const T → Exp Γ T
  abs : ∀ T {U} → Exp (T ∷ Γ) U → Exp Γ (T ⇝ U)
  app : ∀ {T U} → Exp Γ (T ⇝ U) → Exp Γ T → Exp Γ U
  var : ∀ {T} → (T ∈ Γ) → Exp Γ T

-- Shorthand

var₀ : ∀ {Γ T} → Exp (T ∷ Γ) T
var₀ {Γ} {T} = var (singleton T ≪ Γ)

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

weaken+ : ∀ B Γ Δ {T} → Exp (B ++ Δ) T → Exp (B ++ Γ ++ Δ) T
weaken+ B Γ Δ = substn+ B (Γ ++ Δ) Δ (snd Γ Δ)

weaken* : ∀ Γ {Δ T} → Exp Δ T → Exp (Γ ++ Δ) T
weaken* Γ {Δ} = weaken+ [] Γ Δ 

weaken*ʳ : ∀ {Γ} Δ {T} → Exp Γ T → Exp (Γ ++ Δ) T
weaken*ʳ {Γ} Δ = weaken+ Γ Δ []

weaken : ∀ {Γ} T {U} → Exp Γ U → Exp (T ∷ Γ) U
weaken T = weaken* [ T ]

xweaken+ : ∀ B Γ Δ {T} → (T ∈ (B ++ Δ)) → (T ∈ (B ++ Γ ++ Δ))
xweaken+ B Γ Δ x = xsubstn+ B (Γ ++ Δ) Δ (snd Γ Δ) (case B Δ x)

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
    xsubstn+-∙ {k}       {var}     B Γ Δ E σ ρ (inj₁ x) = cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {var}     {exp var} B Γ Δ E σ ρ (inj₁ x) = cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {exp var} {exp var} B Γ Δ E σ ρ (inj₁ x) = cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≪ x Δ)
    xsubstn+-∙ {var}     {var}     B Γ Δ E σ ρ (inj₂ x) = cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≫ B (ρ x))
    xsubstn+-∙ {exp var} {var}     B Γ Δ E σ ρ (inj₂ x) = cong (expr ∘ xsubstn+ B Γ Δ σ) (case-≫ B (ρ x))
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
