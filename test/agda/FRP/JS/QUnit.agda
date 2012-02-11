open import FRP.JS.Bool using ( Bool )
open import FRP.JS.True using ( ⊤ ; tt )
open import FRP.JS.String using ( String )
open import FRP.JS.True using ( True )
open import FRP.JS.RSet
open import FRP.JS.Behaviour

module FRP.JS.QUnit where

infixr 4 _,_

data Test : Set where
  ε : Test
  _,_ : Test → Test → Test
  ok : String → (b : {t : ⊤} → Bool) → {b✓ : True b} → Test
  ok! : String → (b : {t : ⊤} → Bool) → Test
  ok◇ : String → (b : ⟦ Beh ⟨ Bool ⟩ ⟧) → Test

data TestSuite : Set where
  ε : TestSuite
  _,_ : TestSuite → TestSuite → TestSuite
  test : String → Test → TestSuite

data TestSuites : Set where
  ε : TestSuites
  _,_ : TestSuites → TestSuites → TestSuites
  suite : String → TestSuite → TestSuites

