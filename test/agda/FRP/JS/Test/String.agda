open import FRP.JS.Bool using ( not )
open import FRP.JS.String using ( _==_ ; _≤_ ; _<_ )
open import FRP.JS.True using ()
open import FRP.JS.QUnit using ( TestSuite ; ok ; test ; _,_ )

module FRP.JS.Test.String where

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "abc == abc" ("abc" == "abc")
    , ok "ε == abc" (not ("" == "abc"))
    , ok "a == abc" (not ("a" == "abc"))
    , ok "abc == ABC" (not ("abc" == "ABC")) )
  , test "≤" 
    ( ok "abc ≤ abc" ("abc" ≤ "abc")
    , ok "abc ≤ ε" (not ("abc" ≤ ""))
    , ok "abc ≤ a" (not ("abc" ≤ "a"))
    , ok "abc ≤ ab" (not ("abc" ≤ "a"))
    , ok "abc ≤ ABC" (not ("abc" ≤ "ABC"))
    , ok "ε ≤ abc" ("" ≤ "abc")
    , ok "a ≤ abc" ("a" ≤ "abc")
    , ok "ab ≤ abc" ("a" ≤ "abc")
    , ok "ABC ≤ abc" ("ABC" ≤ "abc") )
  , test "<" 
    ( ok "abc < abc" (not ("abc" < "abc"))
    , ok "abc < ε" (not ("abc" < ""))
    , ok "abc < a" (not ("abc" < "a"))
    , ok "abc < ab" (not ("abc" < "a"))
    , ok "abc < ABC" (not ("abc" < "ABC"))
    , ok "ε < abc" ("" < "abc")
    , ok "a < abc" ("a" < "abc")
    , ok "ab < abc" ("a" < "abc")
    , ok "ABC < abc" ("ABC" < "abc") ) )