-- Tests for the compiler itself

open import FRP.JS.Bool using ( Bool ; true ; false ; not )
open import FRP.JS.QUnit using ( TestSuite ; test ; ok ; _,_ )

module FRP.JS.Test.Compiler where

module A where
  module B where
    x = true

f : Bool → Bool
f x = y where
  y = true

f′ : Bool → Bool
f′ x = not y where
  y = false

g : Bool → Bool → Bool
g x = h where
  h : Bool → Bool
  h y = z where
    z = true

mutual
  m1 = m2
  m2 = true
  m3 = m1

tests : TestSuite
tests = 
  ( test "nested modules"
    ( ok "A.B.x" A.B.x)
  , test "where clauses"
    ( ok "f false" (f false)
    , ok "f′ false" (f′ false)
    , ok "g false false" (g false false) )
  , test "mutual clauses"
    ( ok "m1" m1
    , ok "m2" m2
    , ok "m3" m3 ) )
