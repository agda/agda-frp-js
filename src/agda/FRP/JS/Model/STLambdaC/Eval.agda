import FRP.JS.Model.STLambdaC.Typ
import FRP.JS.Model.STLambdaC.Exp
import FRP.JS.Model.STLambdaC.NF
import FRP.JS.Model.STLambdaC.Redn

open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; subst ; subst₂ ; δsubst₂ ; cong ; cong₂ ; begin_ ; _≡⟨_⟩_ ; _∎ )

module FRP.JS.Model.STLambdaC.Eval
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Ctxt ; const ; _⇝_ ; [_] ; [] ; _∷_ ; _++_ ; _∈_ ; uniq
  ; Case ; case ; inj₁ ; inj₂ ; case-≫ ; _≪_ ; _≫_ )

open module Exp = FRP.JS.Model.STLambdaC.Exp TConst Const using 
  ( Exp ; exp ; const ; abs ; app ; var ; var₀ 
  ; Substn ; substn+ ; substn* ; xsubstn+ ; weaken+ ; weaken* ; weakens* 
  ; ⟨_⟩ ; choose ; _◁_ ; id
  ; weaken*-[] ; weaken*-++ ; substn*-◁ ; substn*-id )

open module NF = FRP.JS.Model.STLambdaC.NF TConst Const using 
  ( Atom ; NF ; var ; const ; app ; abs ; atom ; atom₀ ; aweaken* )

open module Redn = FRP.JS.Model.STLambdaC.Redn TConst Const using 
  ( _⇒_ ; _⇓ ; _⇓′ ; eta ; beta ; lhs ; atom ; nf ; redn ; ⇓abs ; ⇓app ; rweaken* )

-- Values

data cVal {Γ C} : Exp Γ (const C) → Set where
  atom : ∀ {M} → Atom M → cVal M
  redn : ∀ {M N} → (M ⇒ N) → cVal N → cVal M

data fVal {Γ T U} (F : ∀ {Γ} → Exp Γ T → Set) (G : ∀ {Γ} → Exp Γ U → Set) : Exp Γ (T ⇝ U) → Set where
  fun : ∀ {M} → (∀ Δ → {N : Exp (Δ ++ Γ) T} → F N → G (app (weaken* Δ {Γ} M) N)) → fVal F G M
  redn : ∀ {M N} → (M ⇒ N) → fVal F G N → fVal F G M

Val : ∀ {Γ T} → Exp Γ T → Set
Val {Γ} {const C} M = cVal M
Val {Γ} {T ⇝ U}   M = fVal Val Val M

-- Values are closed under reduction and application

vredn : ∀ {Γ T} {M N : Exp Γ T} → (M ⇒ N) → Val N → Val M
vredn {Γ} {const C} = redn
vredn {Γ} {T ⇝ U}   = redn

vapp : ∀ {Γ T U} {M : Exp Γ (T ⇝ U)} {N : Exp Γ T} → Val M → Val N → Val (app M N)
vapp {Γ} {T} {U} {M} {N} (fun f) W = subst (λ X → Val (app X N)) (weaken*-[] M) (f [] W)
vapp                (redn M⇒N V) W = vredn (lhs M⇒N) (vapp V W)

-- Reification and reflection

mutual

  reify : ∀ {Γ T} {M : Exp Γ T} → Val M → (M ⇓)
  reify {Γ} {const C}   (atom N)     = nf (atom N)
  reify {Γ} {const C}   (redn M⇒N V) = redn M⇒N (reify V)
  reify {Γ} {T ⇝ U} {M} (fun f)      = redn (eta M) (⇓abs {Γ} T (reify (f [ T ] (reflect (atom (atom₀ {Γ}))))))
  reify {Γ} {T ⇝ U}     (redn M⇒N V) = redn M⇒N (reify V)

  reflect : ∀ {Γ T} {M : Exp Γ T} → (M ⇓′) → Val M
  reflect {Γ} {const C} (atom M) = atom M
  reflect {Γ} {T ⇝ U}   (atom M) = fun (λ Δ V → reflect (⇓app (atom (aweaken* Δ M)) (reify V)))
  reflect          (redn M⇒N N⇓) = vredn M⇒N (reflect N⇓)

-- Value substitutions

Vals : ∀ {Γ Δ} → Substn (exp var) Γ Δ → Set
Vals {Γ} {Δ} σ = ∀ {T} (x : T ∈ Δ) → Val (σ x)

⟪_⟫ : ∀ {Γ T} {N : Exp Γ T} → Val N → Vals ⟨ N ⟩
⟪ V ⟫ x = δsubst₂ (λ X Y → Val {T = X} Y) (uniq x) refl V

vchoose : ∀ {Γ Δ E} {σ : Substn (exp var) Γ Δ} {τ : Substn (exp var) Γ E} → Vals σ → Vals τ →
  ∀ {T} (x : Case T Δ E) → Val (choose σ τ x)
vchoose Vs Ws (inj₁ x) = Vs x
vchoose Vs Ws (inj₂ x) = Ws x

_◂_ : ∀ {Γ Δ T} {N : Exp Γ T} {σ : Substn (exp var) Γ Δ} → Val N → Vals σ → Vals (N ◁ σ)
_◂_ {Γ} {Δ} {T} V Vs x = vchoose ⟪ V ⟫ Vs (case [ T ] Δ x)

-- Weakening

vweaken* : ∀ {Γ} Δ {U} {M : Exp Γ U} → Val M → Val (weaken* Δ M)
vweaken* Δ {const C}   (atom N)     = atom (aweaken* Δ N)
vweaken* Δ {const C}   (redn M⇒N V) = redn (rweaken* Δ M⇒N) (vweaken* Δ V)
vweaken* Δ {T ⇝ U} {M} (fun f)      = fun (λ Φ {N} V → subst (λ X → Val (app X N)) (sym (weaken*-++ Φ Δ _ M)) (f (Φ ++ Δ) V))
vweaken* Δ {T ⇝ U}     (redn M⇒N V) = redn (rweaken* Δ M⇒N) (vweaken* Δ V)

vweakens* : ∀ {Γ Δ} E {σ : Substn (exp var) Γ Δ} → Vals σ → Vals (weakens* E σ)
vweakens* E {σ} Vs x = vweaken* E (Vs x)

-- Evaluation

eval : ∀ {Γ Δ T} (M : Exp Γ T) → {σ : Substn (exp var) Δ Γ} → 
  Vals σ → Val (substn* σ M)
eval (const {T} c) Vs = reflect (atom (const c))
eval {Γ} {Δ} (var x) {σ} Vs =
  subst Val (begin
    σ x
  ≡⟨ sym (weaken*-[] (σ x)) ⟩
    weaken* [] (σ x)
  ≡⟨ cong (xsubstn+ [] Δ Γ σ) (sym (case-≫ [] x)) ⟩
    substn* σ (var x)
  ∎) (Vs x)
eval {Γ} {Δ} (abs T M) {σ} Vs = 
  fun (λ E {N} V → 
    vredn (beta {E ++ Δ} (weaken+ [ T ] E Δ (substn+ [ T ] Δ Γ σ M)) N) 
      (subst Val 
        (substn*-◁ Γ Δ E M N σ) 
        (eval M (V ◂ vweakens* E {σ} Vs))))
eval (app M N) Vs = vapp (eval M Vs) (eval N Vs)

vid : ∀ Γ → Vals (id Γ)
vid Γ x = reflect (atom (var x))

normalize : ∀ {Γ T} → (M : Exp Γ T) → (M ⇓)
normalize {Γ} M = reify (subst Val (substn*-id M) (eval M (vid Γ)))