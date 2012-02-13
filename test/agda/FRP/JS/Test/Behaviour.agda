open import FRP.JS.Nat using ( ℕ ; suc ; _+_ ; _≟_ )
open import FRP.JS.RSet
open import FRP.JS.Time using ( Time ; epoch )
open import FRP.JS.Delay using ( _ms )
open import FRP.JS.Behaviour
open import FRP.JS.Event using ( ∅ )
open import FRP.JS.Bool using ( Bool ; not ; true )
open import FRP.JS.QUnit using ( TestSuite ; ok◇ ; test ; _,_ ; ε )

module FRP.JS.Test.Behaviour where

infixr 2 _≟*_

_≟*_ : ⟦ Beh ⟨ ℕ ⟩ ⇒ Beh ⟨ ℕ ⟩ ⇒ Beh ⟨ Bool ⟩ ⟧
_≟*_ = map2 _≟_

tests : TestSuite
tests =
  ( test "≟*"
    ( ok◇ "[ 1 ] ≟* [ 1 ]" ([ 1 ] ≟* [ 1 ])
    , ok◇ "[ 1 ] ≟* [ 0 ]" (not* ([ 1 ] ≟* [ 0 ]))
    , ok◇ "[ 0 ] ≟* [ 1 ]" (not* ([ 0 ] ≟* [ 1 ])) )
  , test "map"
    ( ok◇ "map suc [ 0 ] ≟* [ 1 ]" (map suc [ 0 ] ≟* [ 1 ])
    , ok◇ "map suc [ 1 ] ≟* [ 1 ]" (not* (map suc [ 1 ] ≟* [ 1 ])) )
  , test "join"
    ( ok◇ "join (map [ suc ] [ 0 ] ) ≟* [ 1 ]" (join (map (λ n → [ suc n ]) [ 0 ]) ≟* [ 1 ])
    , ok◇ "join (map [ suc ] [ 1 ]) ≟* [ 1 ]" (not* (join (map (λ n → [ suc n ]) [ 1 ]) ≟* [ 1 ])) )
  , test "hold"
    ( ok◇ "hold 1 ∅ ≟* [ 1 ]" (hold 1 ∅ ≟* [ 1 ])
    , ok◇ "hold 0 ∅ ≟* [ 1 ]" (not* (hold 0 ∅ ≟* [ 1 ])) ) )
