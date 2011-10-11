open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ; _≟[_]_ )
open import FRP.JS.Float using ( ℝ ; _≟_ ; -_ ; _+_ ; _*_ ; _-_ ; _/_ ; _/?_ ; _≤_ ; _<_ ; show )
open import FRP.JS.String using () renaming ( _≟_ to _≟s_ )
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Float where

infixr 2 _≟?_

_≟?_ : Maybe ℝ → Maybe ℝ → Bool
x ≟? y = x ≟[ _≟_ ] y

tests : TestSuite
tests = 
  ( test "≟" 
    ( ok "0 ≟ 0" (0.0 ≟ 0.0)
    , ok "1 ≟ 1" (1.0 ≟ 1.0)
    , ok "2 ≟ 2" (2.0 ≟ 2.0)
    , ok "0 != 1" (not (0.0 ≟ 1.0))
    , ok "0 != 2" (not (0.0 ≟ 2.0))
    , ok "1 != 2" (not (1.0 ≟ 2.0))
    , ok "1 != 0" (not (1.0 ≟ 0.0)) )
  , test "+" 
    ( ok "0 + 0" (0.0 + 0.0 ≟ 0.0)
    , ok "1 + 1" (1.0 + 1.0 ≟ 2.0)
    , ok "37 + 0" (37.0 + 0.0 ≟ 37.0)
    , ok "37 + 1" (37.0 + 1.0 ≟ 38.0)
    , ok "37 + 5" (37.0 + 5.0 ≟ 42.0) )
  , test "*" 
    ( ok "0 * 0" (0.0 * 0.0 ≟ 0.0)
    , ok "1 * 1" (1.0 * 1.0 ≟ 1.0)
    , ok "37 * 0" (37.0 * 0.0 ≟ 0.0)
    , ok "37 * 1" (37.0 * 1.0 ≟ 37.0)
    , ok "37 * 5" (37.0 * 5.0 ≟ 185.0) )
  , test "-" 
    ( ok "0 - 0" (0.0 - 0.0 ≟ 0.0)
    , ok "1 - 1" (1.0 - 1.0 ≟ 0.0)
    , ok "37 - 0" (37.0 - 0.0 ≟ 37.0)
    , ok "37 - 1" (37.0 - 1.0 ≟ 36.0)
    , ok "37 - 5" (37.0 - 5.0 ≟ 32.0)
    , ok "5 - 37" (5.0 - 37.0 ≟ - 32.0) )
  , test "/" 
    ( ok "1 / 1" (1.0 / 1.0 ≟ 1.0)
    , ok "37 / 1" (37.0 / 1.0 ≟ 37.0)
    , ok "37 / 5" (37.0 / 5.0 ≟ 7.4)
    , ok "0 /? 0" (0.0 /? 0.0 ≟? nothing)
    , ok "1 /? 1" (1.0 /? 1.0 ≟? just 1.0)
    , ok "37 /? 0" (37.0 /? 0.0 ≟? nothing)
    , ok "37 /? 1" (37.0 /? 1.0 ≟? just 37.0)
    , ok "37 /? 5" (37.0 /? 5.0 ≟? just 7.4) )
  , test "≤" 
    ( ok "0 ≤ 0" (0.0 ≤ 0.0)
    , ok "0 ≤ 1" (0.0 ≤ 1.0)
    , ok "1 ≤ 0" (not (1.0 ≤ 0.0))
    , ok "1 ≤ 1" (1.0 ≤ 1.0)
    , ok "37 ≤ 0" (not (37.0 ≤ 0.0))
    , ok "37 ≤ 1" (not (37.0 ≤ 1.0))
    , ok "37 ≤ 5" (not (37.0 ≤ 5.0))
    , ok "5 ≤ 37" (5.0 ≤ 37.0) )
  , test "<" 
    ( ok "0 < 0" (not (0.0 < 0.0))
    , ok "0 < 1" (0.0 < 1.0)
    , ok "1 < 0" (not (1.0 < 0.0))
    , ok "1 < 1" (not (1.0 < 1.0))
    , ok "37 < 0" (not (37.0 < 0.0))
    , ok "37 < 1" (not (37.0 < 1.0))
    , ok "37 < 5" (not (37.0 < 5.0))
    , ok "5 < 37" (5.0 < 37.0) )
  , test "show"
    ( ok "show 0" (show 0.0 ≟s "0")
    , ok "show 1" (show 1.0 ≟s "1")
    , ok "show 5" (show 5.0 ≟s "5")
    , ok "show 37" (show 37.0 ≟s "37")
    , ok "show -0" (show (- 0.0) ≟s "0")
    , ok "show -37" (show (- 37.0) ≟s "-37")
    , ok "show 3.1415" (show 3.1415 ≟s "3.1415")
    , ok "show -3.1415" (show (- 3.1415) ≟s "-3.1415") ) )
