open import FRP.JS.String using ( _≟_ )
open import FRP.JS.Bool using ( Bool ; true ; false ; if_then_else_ ; _∧_ ; _∨_ ; not ; _xor_ )
open import FRP.JS.QUnit using ( TestSuite ; ok ; test ; _,_ )

module FRP.JS.Test.Bool where

tests : TestSuite
tests = 
  ( test "true" 
    ( ok "true" true )
  , test "false" 
    ( ok "false" (not false) )
  , test "if" 
    ( ok "if true" (if true then "a" else "b" ≟ "a")
    , ok "if false" (if false then "a" else "b" ≟ "b") )
  , test "∧" 
    ( ok "true ∧ true" (true ∧ true)
    , ok "true ∧ false" (not (true ∧ false))
    , ok "false ∧ true" (not (false ∧ true))
    , ok "false ∧ false" (not (false ∧ false)) )
  , test "∨" 
    ( ok "true ∨ true" (true ∨ true)
    , ok "true ∨ false" (true ∨ false)
    , ok "false ∨ true" (false ∨ true)
    , ok "false ∨ false" (not (false ∨ false)) )
  , test "xor" 
    ( ok "true xor true" (not (true xor true))
    , ok "true xor false" (true xor false)
    , ok "false xor true" (false xor true)
    , ok "false xor false" (not (false xor false)) )
  )