open import FRP.JS.QUnit using ( TestSuites ; suite ; _,_ )

import FRP.JS.Test.Bool
import FRP.JS.Test.Nat
import FRP.JS.Test.String
import FRP.JS.Test.List

module FRP.JS.Test where

tests : TestSuites
tests = 
  ( suite "Bool"   FRP.JS.Test.Bool.tests 
  , suite "Nat"    FRP.JS.Test.Nat.tests
  , suite "String" FRP.JS.Test.String.tests
  , suite "List"   FRP.JS.Test.List.tests )
