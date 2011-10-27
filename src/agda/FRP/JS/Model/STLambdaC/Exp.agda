import FRP.JS.Model.STLambdaC.Typ

open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst )

module FRP.JS.Model.STLambdaC.Exp 
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Ctxt ; const ; _⇝_ ; ∅ ; _◁_ ; _+_ ; [_] ; ⟨_⟩ ; case ; [] ; _∷_ )

data Var (T : Typ) : Ctxt → Set where
  zero : ∀ {Γ} → Var T (T ∷ Γ)
  suc : ∀ {Γ U} → Var T Γ → Var T (U ∷ Γ)

data Exp (Γ : Ctxt) : Typ → Set where
  const : ∀ {T} → Const T → Exp Γ T
  var : ∀ {T} → Var T Γ → Exp Γ T
  abs : ∀ T {U} → Exp (T ∷ Γ) U → Exp Γ (T ⇝ U)
  app : ∀ {T U} → Exp Γ (T ⇝ U) → Exp Γ T → Exp Γ U

data Exps (Δ : Ctxt) : Ctxt → Set where
  [] : Exps Δ []
  _∷_ : ∀ {Γ T} → Exp Δ T → Exps Δ Γ → Exps Δ (T ∷ Γ)

-- Weakening

xweaken+ : ∀ B Γ Δ {T} → Var T ⟨ B + Δ ⟩ → Var T ⟨ B + Γ + Δ ⟩
xweaken+ B        Γ        Δ x       with case B
xweaken+ .(T ◁ B) Γ        Δ zero    | (T ∷ B)      = zero
xweaken+ .(T ◁ B) Γ        Δ (suc x) | (T ∷ B)      = suc (xweaken+ B Γ Δ x)
xweaken+ .∅       Γ        Δ x       | [] with case Γ
xweaken+ .∅       .(T ◁ Γ) Δ x       | [] | (T ∷ Γ) = suc (xweaken+ ∅ Γ Δ x)
xweaken+ .∅       .∅       Δ x       | [] | []      = x

xweaken* : ∀ Γ Δ {T} → Var T ⟨ Δ ⟩ → Var T ⟨ Γ + Δ ⟩
xweaken* = xweaken+ ∅

weaken+ : ∀ B Γ Δ {T} → Exp ⟨ B + Δ ⟩ T → Exp ⟨ B + Γ + Δ ⟩ T
weaken+ B Γ Δ (const c) = const c
weaken+ B Γ Δ (var x)   = var (xweaken+ B Γ Δ x)
weaken+ B Γ Δ (abs T M) = abs T (weaken+ (T ◁ B) Γ Δ M)
weaken+ B Γ Δ (app M N) = app (weaken+ B Γ Δ M) (weaken+ B Γ Δ N)

weaken* : ∀ Γ Δ {T} → Exp ⟨ Δ ⟩ T → Exp ⟨ Γ + Δ ⟩ T
weaken* = weaken+ ∅

weaken : ∀ {Γ T U} → Exp Γ U → Exp (T ∷ Γ) U
weaken {Γ} {T} = weaken* [ T ∷ [] ] [ Γ ]

weakens+ : ∀ B Γ Δ {E} → Exps ⟨ B + Δ ⟩ E → Exps ⟨ B + Γ + Δ ⟩ E
weakens+ B Γ Δ []       = []
weakens+ B Γ Δ (M ∷ Ms) = (weaken+ B Γ Δ M ∷ weakens+ B Γ Δ Ms)

weakens* : ∀ Γ Δ {E} → Exps ⟨ Δ ⟩ E → Exps ⟨ Γ + Δ ⟩ E
weakens* = weakens+ ∅

weakens : ∀ {Γ Δ T} → Exps Γ Δ → Exps (T ∷ Γ) Δ
weakens {Γ} {Δ} {T} = weakens* [ T ∷ [] ] [ Γ ]

-- Substitution

xsubstn+ : ∀ B Γ Δ E {T} → Exps ⟨ Δ + E ⟩ ⟨ Γ ⟩ → Var T ⟨ B + Γ + E ⟩ → Exp ⟨ B + Δ + E ⟩ T
xsubstn+ B Γ Δ E Ns x with case B
xsubstn+ .(T ◁ B) Γ        Δ E Ns       zero    | (T ∷ B)      = var zero
xsubstn+ .(T ◁ B) Γ        Δ E Ns       (suc x) | (T ∷ B)      = weaken (xsubstn+ B Γ Δ E Ns x)
xsubstn+ .∅       Γ        Δ E Ns       x       | [] with case Γ
xsubstn+ .∅       .(T ◁ Γ) Δ E (N ∷ Ns) zero    | [] | (T ∷ Γ) = N
xsubstn+ .∅       .(T ◁ Γ) Δ E (N ∷ Ns) (suc x) | [] | (T ∷ Γ) = xsubstn+ ∅ Γ Δ E Ns x
xsubstn+ .∅       .∅       Δ E []       x       | [] | []      = weaken* Δ E (var x)

xsubstn* : ∀ Γ Δ E {T} → Exps ⟨ Δ + E ⟩ ⟨ Γ ⟩ → Var T ⟨ Γ + E ⟩ → Exp ⟨ Δ + E ⟩ T
xsubstn* = xsubstn+ ∅

substn+ : ∀ B Γ Δ E {T} → Exp ⟨ B + Γ + E ⟩ T → Exps ⟨ Δ + E ⟩ ⟨ Γ ⟩ → Exp ⟨ B + Δ + E ⟩ T
substn+ B Γ Δ E (const c) Ns = const c
substn+ B Γ Δ E (var x)   Ns = xsubstn+ B Γ Δ E Ns x
substn+ B Γ Δ E (abs T M) Ns = abs T (substn+ (T ◁ B) Γ Δ E M Ns)
substn+ B Γ Δ E (app M N) Ns = app (substn+ B Γ Δ E M Ns) (substn+ B Γ Δ E N Ns)

substn* : ∀ Γ Δ E {T} → Exp ⟨ Γ + E ⟩ T → Exps ⟨ Δ + E ⟩ ⟨ Γ ⟩ → Exp ⟨ Δ + E ⟩ T
substn* = substn+ ∅

substn : ∀ {Γ T U} → Exp (T ∷ Γ) U → Exp Γ T → Exp Γ U
substn {Γ} {T} M N = substn* [ T ∷ [] ] ∅ [ Γ ] M (N ∷ [])
