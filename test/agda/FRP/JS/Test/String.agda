open import FRP.JS.Bool using ( not )
open import FRP.JS.Nat using ( ) renaming ( _==_ to _==n_ )
open import FRP.JS.String using ( _==_ ; _≤_ ; _<_ ; length )
open import FRP.JS.QUnit using ( TestSuite ; ok ; test ; _,_ )

module FRP.JS.Test.String where

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "abc == abc" ("abc" == "abc")
    , ok "ε == abc" (not ("" == "abc"))
    , ok "a == abc" (not ("a" == "abc"))
    , ok "abc == ABC" (not ("abc" == "ABC")) )
  , test "length" 
    ( ok "length ε" (length "" ==n 0)
    , ok "length a" (length "a" ==n 1)
    , ok "length ab" (length "ab" ==n 2)
    , ok "length abc" (length "abc" ==n 3)
    , ok "length \"\\\"" (length "\"\\\"" ==n 3)
    , ok "length åäö⊢ξ∀" (length "åäö⊢ξ∀" ==n 6)
    , ok "length ⟨line-terminators⟩" (length "\r\n\x2028\x2029" ==n 4) )
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