open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; cong )
open import FRP.JS.Model.DList using ( List )
open import FRP.JS.Model.DNat using ( ℕ )
open import FRP.JS.Maybe using ( Maybe )

module FRP.JS.Model.STLambdaC.Typ (TConst : Set) where

infixr 2 _⇝_

data Typ : Set where
  const : TConst → Typ
  _⇝_ : Typ → Typ → Typ

Var : Set
Var = ℕ

Ctxt : Set
Ctxt = List Typ

open FRP.JS.Model.DList public using 
  ( [] ; [_] ; _++_ ; _∷_ ; _∈_ ; _≪_ ; _≫_ ; _⋙_ ; uniq ; singleton
  ; Case ; case ; inj₁ ; inj₂ ; inj₃ ; case-≪ ; case-≫ ; case-⋙
  ; Case₃ ; case₃ ; caseˡ ; caseʳ ; caseˡ₃ ; caseʳ₃ )
