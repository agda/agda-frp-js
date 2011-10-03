open import FRP.JS.Bool using ( not )
open import FRP.JS.Nat using ( ℕ ; _==_ ; _+_ ; _*_ ; _∸_ ; _≤_ ; _<_ )
open import FRP.JS.Nat.Show using ( show )
open import FRP.JS.String using () renaming ( _==_ to _===_ )
open import FRP.JS.True using ()
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Nat where

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "0 == 0" (0 == 0)
    , ok "1 == 1" (1 == 1)
    , ok "2 == 2" (2 == 2)
    , ok "0 != 1" (not (0 == 1))
    , ok "0 != 2" (not (0 == 2))
    , ok "1 != 2" (not (1 == 2))
    , ok "1 != 0" (not (1 == 0)) )
  , test "+" 
    ( ok "0 + 0" (0 + 0 == 0)
    , ok "1 + 1" (1 + 1 == 2)
    , ok "37 + 0" (37 + 0 == 37)
    , ok "37 + 1" (37 + 1 == 38)
    , ok "37 + 5" (37 + 5 == 42) )
  , test "*" 
    ( ok "0 * 0" (0 * 0 == 0)
    , ok "1 * 1" (1 * 1 == 1)
    , ok "37 * 0" (37 * 0 == 0)
    , ok "37 * 1" (37 * 1 == 37)
    , ok "37 * 5" (37 * 5 == 185) )
  , test "∸" 
    ( ok "0 ∸ 0" (0 ∸ 0 == 0)
    , ok "1 ∸ 1" (1 ∸ 1 == 0)
    , ok "37 ∸ 0" (37 ∸ 0 == 37)
    , ok "37 ∸ 1" (37 ∸ 1 == 36)
    , ok "37 ∸ 5" (37 ∸ 5 == 32)
    , ok "5 ∸ 37" (5 ∸ 37 == 0) )
  , test "≤" 
    ( ok "0 ≤ 0" (0 ≤ 0)
    , ok "0 ≤ 1" (0 ≤ 1)
    , ok "1 ≤ 0" (not (1 ≤ 0))
    , ok "1 ≤ 1" (1 ≤ 1)
    , ok "37 ≤ 0" (not (37 ≤ 0))
    , ok "37 ≤ 1" (not (37 ≤ 1))
    , ok "37 ≤ 5" (not (37 ≤ 5))
    , ok "5 ≤ 37" (5 ≤ 37) )
  , test "<" 
    ( ok "0 < 0" (not (0 < 0))
    , ok "0 < 1" (0 < 1)
    , ok "1 < 0" (not (1 < 0))
    , ok "1 < 1" (not (1 < 1))
    , ok "37 < 0" (not (37 < 0))
    , ok "37 < 1" (not (37 < 1))
    , ok "37 < 5" (not (37 < 5))
    , ok "5 < 37" (5 < 37) )
  , test "show" -- Slightly annoyingly, show is a postulate so we have to use ok! not ok.
    ( ok! "show 0" (show 0 === "0")
    , ok! "show 1" (show 1 === "1")
    , ok! "show 5" (show 5 === "5")
    , ok! "show 37" (show 37 === "37") )
  )