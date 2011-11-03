import FRP.JS.Model.STLambdaC.Typ
import FRP.JS.Model.STLambdaC.Exp
import FRP.JS.Model.STLambdaC.NF

open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; subst ; subst₂ ; cong ; cong₂ )

module FRP.JS.Model.STLambdaC.Redn
  (TConst : Set) 
  (Const : FRP.JS.Model.STLambdaC.Typ.Typ TConst → Set) where

open module Typ = FRP.JS.Model.STLambdaC.Typ TConst using 
  ( Typ ; Ctxt ; const ; _⇝_ ; [_] ; [] ; _∷_ ; _++_ ; case )

open module Exp = FRP.JS.Model.STLambdaC.Exp TConst Const using 
  ( Exp ; const ; abs ; app ; var ; var₀ 
  ; substn ; weaken ; weaken* ; weaken+ ; weaken+-weaken+ )

open module Redn = FRP.JS.Model.STLambdaC.NF TConst Const using 
  ( NF ; Atom ; app ; abs )

-- Small-step reduction

data _⇒_ {Γ} : ∀ {T : Typ} → Exp Γ T → Exp Γ T → Set where
  beta : ∀ {T U} (L : Exp (T ∷ Γ) U) (M : Exp Γ T) {N} → 
    .(N ≡ substn {Γ} L M) → (app (abs {Γ} T L) M) ⇒ N
  eta : ∀ {T U} (M : Exp Γ (T ⇝ U)) {N} → 
    .(N ≡ abs {Γ} T (app (weaken T M) (var₀ {Γ}))) → (M ⇒ N)
  lhs : ∀ {T U} {L M : Exp Γ (T ⇝ U)} {N : Exp Γ T} → 
    (L ⇒ M) → (app L N ⇒ app M N)
  rhs : ∀ {T U} {L : Exp Γ (T ⇝ U)} {M N : Exp Γ T} → 
    (M ⇒ N) → (app L M ⇒ app L N)
  abs : ∀ T {U} {M N : Exp (T ∷ Γ) U} →
    (M ⇒ N) → (abs {Γ} T M ⇒ abs {Γ} T N)

-- Reduction to normal form

data _⇓ {Γ T} (M : Exp Γ T) : Set where
  nf : NF M → (M ⇓)
  redn : ∀ {N} → (M ⇒ N) → (N ⇓) → (M ⇓)

-- Reduction to atomic form

data _⇓′ {Γ T} (M : Exp Γ T) : Set where
  atom : Atom M → (M ⇓′)
  redn : ∀ {N} → (M ⇒ N) → (N ⇓′) → (M ⇓′)

-- Normalization is closed under abstraction and application

⇓abs : ∀ {Γ} T {U} {M : Exp (T ∷ Γ) U} → (M ⇓) → (abs {Γ} T M ⇓)
⇓abs {Γ} T (nf M)        = nf (abs {Γ} T M)
⇓abs {Γ} T (redn M⇒N N⇓) = redn (abs T M⇒N) (⇓abs {Γ} T N⇓)

⇓app : ∀ {Γ T U} {M : Exp Γ (T ⇝ U)} {N : Exp Γ T} → (M ⇓′) → (N ⇓) → (app M N ⇓′)
⇓app (atom M)      (nf N)        = atom (app M N)
⇓app (atom L)      (redn L⇒M M⇓) = redn (rhs L⇒M) (⇓app (atom L) M⇓)
⇓app (redn L⇒M M⇓) N⇓            = redn (lhs L⇒M) (⇓app M⇓ N⇓)

-- Weakening

-- rweaken+ : ∀ B Γ Δ {T M N} → (M ⇒ N) → (weaken+ B Γ Δ {T} M ⇒ weaken+ B Γ Δ {T} N)
-- rweaken+ B Γ Δ (beta {T} L M N≡L[M/x]) = 
--   beta (weaken+ (T ∷ B) Γ Δ L) (weaken+ B Γ Δ M) 
--     (trans (cong (weaken+ B Γ Δ) N≡L[M/x]) (weaken+-substn B Γ Δ L M))
-- rweaken+ B Γ Δ (eta {T} M N≡λx→Mx) = 
--   eta (weaken+ B Γ Δ M)
--     (trans (cong (weaken+ B Γ Δ) N≡λx→Mx) 
--       (cong (abs T) (cong₂ app 
--         (sym (weaken+-weaken+ [] [ T ] B Γ Δ M))
--         (weaken+-var₀ B Γ Δ))))
-- rweaken+ B Γ Δ (lhs M⇒N)   = lhs (rweaken+ B Γ Δ M⇒N)
-- rweaken+ B Γ Δ (rhs M⇒N)   = rhs (rweaken+ B Γ Δ M⇒N)
-- rweaken+ B Γ Δ (abs T M⇒N) = abs T (rweaken+ (T ∷ B) Γ Δ M⇒N)

-- rweaken* : ∀ Γ Δ {T M N} → (M ⇒ N) → (weaken* Γ Δ {T} M ⇒ weaken* Γ Δ {T} N)
-- rweaken* = rweaken+ []
