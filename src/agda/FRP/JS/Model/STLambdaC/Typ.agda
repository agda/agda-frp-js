open import FRP.JS.Model.Util using ( _≡_ ; refl ; sym ; trans ; cong )
open import FRP.JS.Model.List using ( List )
open import FRP.JS.Model.Seq using ( Seq )

module FRP.JS.Model.STLambdaC.Typ (TConst : Set) where

infixr 2 _⇝_

data Typ : Set where
  const : TConst → Typ
  _⇝_ : Typ → Typ → Typ

Ctxt : Set
Ctxt = List Typ

Ctxt+ : Set
Ctxt+ = Seq Typ

open FRP.JS.Model.List public 
  using ( [] ; _∷_ )

open FRP.JS.Model.Seq public 
  using ( ∅ ; [_] ; ⟨_⟩ ; _+_ ; _◁_ ; Case ; [] ; _∷_ ; case )
