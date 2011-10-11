open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ; _≟[_]_ )
open import FRP.JS.Int using ( ℤ ; _≟_ ; _+_ ; _*_ ; _-_ ; _/_ ; _/?_ ; _≤_ ; _<_ ; show ; float )
open import FRP.JS.Nat using ( +_ ; -_ )
open import FRP.JS.Float using ( ℝ ) renaming ( _≟_ to _≟r_ )
open import FRP.JS.String using () renaming ( _≟_ to _≟s_ )
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Int where

infixr 2 _≟?r_

_≟?r_ : Maybe ℝ → Maybe ℝ → Bool
x ≟?r y = x ≟[ _≟r_ ] y

+0 = + 0
+1 = + 1
+2 = + 2
+5 = + 5
+32 = + 32
+36 = + 36
+37 = + 37
+38 = + 38
+42 = + 42
+185 = + 185
-32 = - 32

tests : TestSuite
tests = 
  ( test "≟" 
    ( ok "0 ≟ 0" (+0 ≟ +0)
    , ok "1 ≟ 1" (+1 ≟ +1)
    , ok "2 ≟ 2" (+2 ≟ +2)
    , ok "0 != 1" (not (+0 ≟ +1))
    , ok "0 != 2" (not (+0 ≟ +2))
    , ok "1 != 2" (not (+1 ≟ +2))
    , ok "1 != 0" (not (+1 ≟ +0)) )
  , test "+" 
    ( ok "0 + 0" (+0 + +0 ≟ +0)
    , ok "1 + 1" (+1 + +1 ≟ +2)
    , ok "37 + 0" (+37 + +0 ≟ +37)
    , ok "37 + 1" (+37 + +1 ≟ +38)
    , ok "37 + 5" (+37 + +5 ≟ +42) )
  , test "*" 
    ( ok "0 * 0" (+0 * +0 ≟ +0)
    , ok "1 * 1" (+1 * +1 ≟ +1)
    , ok "37 * 0" (+37 * +0 ≟ +0)
    , ok "37 * 1" (+37 * +1 ≟ +37)
    , ok "37 * 5" (+37 * +5 ≟ +185) )
  , test "-" 
    ( ok "0 - 0" (+0 - +0 ≟ +0)
    , ok "1 - 1" (+1 - +1 ≟ +0)
    , ok "37 - 0" (+37 - +0 ≟ +37)
    , ok "37 - 1" (+37 - +1 ≟ +36)
    , ok "37 - 5" (+37 - +5 ≟ +32)
    , ok "5 - 37" (+5 - +37 ≟ -32) )
  , test "/" 
    ( ok "1 / 1" (+1 / +1 ≟r 1.0)
    , ok "37 / 1" (+37 / +1 ≟r 37.0)
    , ok "37 / 5" (+37 / +5 ≟r 7.4)
    , ok "0 /? 0" (+0 /? +0 ≟?r nothing)
    , ok "1 /? 1" (+1 /? +1 ≟?r just 1.0)
    , ok "37 /? 0" (+37 /? +0 ≟?r nothing)
    , ok "37 /? 1" (+37 /? +1 ≟?r just 37.0)
    , ok "37 /? 5" (+37 /? +5 ≟?r just 7.4) )
  , test "≤" 
    ( ok "0 ≤ 0" (+0 ≤ +0)
    , ok "0 ≤ 1" (+0 ≤ +1)
    , ok "1 ≤ 0" (not (+1 ≤ +0))
    , ok "1 ≤ 1" (+1 ≤ +1)
    , ok "37 ≤ 0" (not (+37 ≤ +0))
    , ok "37 ≤ 1" (not (+37 ≤ +1))
    , ok "37 ≤ 5" (not (+37 ≤ +5))
    , ok "5 ≤ 37" (+5 ≤ +37) )
  , test "<" 
    ( ok "0 < 0" (not (+0 < +0))
    , ok "0 < 1" (+0 < +1)
    , ok "1 < 0" (not (+1 < +0))
    , ok "1 < 1" (not (+1 < +1))
    , ok "37 < 0" (not (+37 < +0))
    , ok "37 < 1" (not (+37 < +1))
    , ok "37 < 5" (not (+37 < +5))
    , ok "5 < 37" (+5 < +37) )
  , test "show"
    ( ok "show 0" (show +0 ≟s "0")
    , ok "show 1" (show +1 ≟s "1")
    , ok "show 5" (show +5 ≟s "5")
    , ok "show 37" (show +37 ≟s "37") )
  , test "float"
    ( ok "float 0" (float +0 ≟r 0.0)
    , ok "float 1" (float +1 ≟r 1.0)
    , ok "float 5" (float +5 ≟r 5.0)
    , ok "float 37" (float +37 ≟r 37.0) )
  )