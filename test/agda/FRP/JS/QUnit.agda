open import FRP.JS.Bool using ( Bool )
open import FRP.JS.String using ( String )
open import FRP.JS.True using ( True )

module FRP.JS.QUnit where

infixr 4 _,_

data Test : Set where
  ε : Test
  _,_ : Test → Test → Test
  ok : String → (b : Bool) → {b✓ : True b} → Test
  ok! : String → (b : Bool) → Test

data TestSuite : Set where
  ε : TestSuite
  _,_ : TestSuite → TestSuite → TestSuite
  test : String → Test → TestSuite

data TestSuites : Set where
  ε : TestSuites
  _,_ : TestSuites → TestSuites → TestSuites
  suite : String → TestSuite → TestSuites

