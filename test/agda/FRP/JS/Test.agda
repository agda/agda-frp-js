open import FRP.JS.QUnit using ( TestSuites ; suite ; _,_ )

import FRP.JS.Test.Bool
import FRP.JS.Test.Nat
import FRP.JS.Test.Int
import FRP.JS.Test.Float
import FRP.JS.Test.String
import FRP.JS.Test.Maybe
import FRP.JS.Test.List
import FRP.JS.Test.Array
import FRP.JS.Test.Object
import FRP.JS.Test.JSON
import FRP.JS.Test.Behaviour
import FRP.JS.Test.DOM
import FRP.JS.Test.Compiler

module FRP.JS.Test where

tests : TestSuites
tests = 
  ( suite "Bool"      FRP.JS.Test.Bool.tests
  , suite "Nat"       FRP.JS.Test.Nat.tests
  , suite "Int"       FRP.JS.Test.Int.tests
  , suite "Float"     FRP.JS.Test.Float.tests
  , suite "String"    FRP.JS.Test.String.tests
  , suite "Maybe"     FRP.JS.Test.Maybe.tests
  , suite "List"      FRP.JS.Test.List.tests
  , suite "Array"     FRP.JS.Test.Array.tests
  , suite "Object"    FRP.JS.Test.Object.tests
  , suite "JSON"      FRP.JS.Test.JSON.tests
  , suite "Behaviour" FRP.JS.Test.Behaviour.tests
  , suite "DOM"       FRP.JS.Test.DOM.tests
  , suite "Compiler"  FRP.JS.Test.Compiler.tests )
