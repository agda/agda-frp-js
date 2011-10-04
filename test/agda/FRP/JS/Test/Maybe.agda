open import FRP.JS.Nat using ( ℕ ; suc ; _+_ ; _==_ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ; _==[_]_ )
open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Maybe where

_==¹_ : Maybe ℕ → Maybe ℕ → Bool
xs ==¹ ys = xs ==[ _==_ ] ys

Maybe² : Set → Set
Maybe² A = Maybe (Maybe A)

_==²_ : Maybe² ℕ → Maybe² ℕ → Bool
xs ==² ys = xs ==[ _==¹_ ] ys

just² : ∀ {A : Set} → A → Maybe² A
just² a = just (just a)

Maybe³ : Set → Set
Maybe³ A = Maybe (Maybe² A)

_==³_ : Maybe³ ℕ → Maybe³ ℕ → Bool
xs ==³ ys = xs ==[ _==²_ ] ys

just³ : ∀ {A} → A → Maybe³ A
just³ a = just (just² a)

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "nothing == nothing" (nothing ==¹ nothing) 
    , ok "just 0 == just 0"   (just 0 ==¹ just 0)
    , ok "nothing == just 1"  (not (nothing ==¹ just 1))
    , ok "just 0 == nothing"  (not (just 0 ==¹ nothing))
    , ok "just 0 == just 1"   (not (just 0 ==¹ just 1)) )
  , test "==²" 
    ( ok "nothing ==² nothing"           (nothing ==² nothing) 
    , ok "just nothing ==² just nothing" (just nothing ==² just nothing)
    , ok "just² 0 ==² just² 0"           (just² 0 ==² just² 0)
    , ok "nothing ==² just nothing"      (not (nothing ==² just nothing))
    , ok "nothing ==² just² 1"           (not (nothing ==² just² 1))
    , ok "just nothing ==² just² 1"      (not (just nothing ==² just² 1))
    , ok "just² 0 ==² just² 1"           (not (just² 0 ==² just² 1)) )
  , test "==³" 
    ( ok "nothing ==³ nothing"             (nothing ==³ nothing) 
    , ok "just nothing ==³ just nothing"   (just nothing ==³ just nothing)
    , ok "just² nothing ==³ just² nothing" (just² nothing ==³ just² nothing)
    , ok "just³ 0 ==³ just³ 0"             (just³ 0 ==³ just³ 0)
    , ok "nothing ==³ just nothing"        (not (nothing ==³ just nothing))
    , ok "nothing ==³ just² nothing"       (not (nothing ==³ just² nothing))
    , ok "nothing ==³ just³ 1"             (not (nothing ==³ just³ 1))
    , ok "just nothing ==³ just² nothing"  (not (just nothing ==³ just² nothing))
    , ok "just nothing ==³ just³ 1"        (not (just nothing ==³ just³ 1))
    , ok "just³ 0 ==³ just³ 1"             (not (just³ 0 ==³ just³ 1)) ) )
