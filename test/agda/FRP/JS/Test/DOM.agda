open import FRP.JS.Nat using ( ℕ ; suc ; _+_ )
open import FRP.JS.DOM
open import FRP.JS.RSet
open import FRP.JS.Time using ( Time ; epoch )
open import FRP.JS.Delay using ( _ms )
open import FRP.JS.Behaviour
open import FRP.JS.Bool using ( Bool ; not ; true )
open import FRP.JS.QUnit using ( TestSuite ; ok◇ ; test ; _,_ ; ε )

module FRP.JS.Test.DOM where

withDOW : {A : Set} → ((w : DOW) → A) → A
withDOW f = f unattached

tests : TestSuite
tests =
  ( test "≟*"
    ( ok◇ "[] ≟* []"
      (withDOW λ w → [] {w} ≟* [])
    , ok◇ "[] ++ [] ≟* []"
      (withDOW λ w → [] {left w} ++ [] ≟* []) )
  , test "attr"
    ( ok◇ "attr class [ alpha ] ≟* attr class [ alpha ]"
      (withDOW λ w → attr {w} "class" [ "alpha" ] ≟* attr "class" [ "alpha" ])
    , ok◇ "attr foo [ alpha ] ≟* attr foo [ alpha ]"
      (withDOW λ w → attr {w} "foo" [ "alpha" ] ≟* attr "foo" [ "alpha" ])
    , ok◇ "attr foo [ alpha ] ++ attr bar [ alpha ] ≟* attr foo [ alpha ] ++ attr bar [ alpha ]"
      (withDOW λ w → attr {left w} "foo" [ "alpha" ] ++ attr "bar" [ "alpha" ] ≟* attr "foo" [ "alpha" ] ++ attr "bar" [ "alpha" ])
    , ok◇ "attr class [ beta ] ≟* attr class [ alpha ]"
      (withDOW λ w → not* (attr {w} "class" [ "beta" ] ≟* attr "class" [ "alpha" ]))
    , ok◇ "attr foo [ alpha ] ≟* attr class [ alpha ]"
      (withDOW λ w → not* (attr {w} "foo" [ "alpha" ] ≟* attr "class" [ "alpha" ]))
    , ok◇ "attr foo [ alpha ] ++ attr bar [ alpha ] ≟* attr foo [ alpha ]"
      (withDOW λ w → not* (attr {left w} "foo" [ "alpha" ] ++ attr "bar" [ "alpha" ] ≟* attr "foo" [ "alpha" ])) )
  , test "text"
    ( ok◇ "text [ abc ] ≟* text [ abc ]"
      (withDOW λ w → text {w} [ "abc" ] ≟* text [ "abc" ])
    , ok◇ "text [ a ] ≟* text [ abc ]"
      (withDOW λ w → not* (text {w} [ "a" ] ≟* text [ "abc" ]))
    , ok◇ "[] ≟* text [ abc ]"
      (withDOW λ w → not* ([] ≟* text {w} [ "abc" ]))
    , ok◇ "text [ abc ] ++ [] ≟* text [ abc ]"
      (withDOW λ w → text {left w} [ "abc" ] ++ [] ≟* (text [ "abc" ]))
    , ok◇ "[] ++ text [ abc ] ≟* text [ abc ]"
      (withDOW λ w → [] ++ text {right w} [ "abc" ] ≟* (text [ "abc" ])) )
  , test "element"
    ( ok◇ "element p (text [ abc ]) ≟* element p (text [ abc ])"
      (withDOW λ w → element "p" {w} (text [ "abc" ]) ≟* element "p" (text [ "abc" ]))
    , ok◇ "element p (text [ a ]) ≟* element p (text [ abc ])"
      (withDOW λ w → not* (element "p" {w} (text [ "a" ]) ≟* element "p" (text [ "abc" ])))
    , ok◇ "element div (attr class [ alpha ] ++ text [ abc ]) ≟* element div (attr class [ alpha ] ++ text [ abc ])"
      (withDOW λ w → element "div" {w} (attr "class" [ "alpha" ] ++ text [ "abc" ]) ≟* element "div" {w} (attr "class" [ "alpha" ] ++ text [ "abc" ]))
    , ok◇ "element div (attr class [ beta ] ++ text [ abc ]) ≟* element div (attr class [ alpha ] ++ text [ abc ])"
      (withDOW λ w → not* (element "div" {w} (attr "class" [ "beta" ] ++ text [ "abc" ]) ≟* element "div" {w} (attr "class" [ "alpha" ] ++ text [ "abc" ])))
    , ok◇ "element p (text [ abc ]) ≟* element p (text [ abc ])"
      (withDOW λ w → element "p" {w} (text [ "abc" ]) ≟* element "p" (text [ "abc" ]))
    , ok◇ "element p (text [ a ]) ++ element p (text [ b ]) ≟* element p (text [ a ])"
      (withDOW λ w → not* (element "p" {left w} (text [ "a" ]) ++ element "p" (text [ "b" ]) ≟* element "p" (text [ "a" ])))
      )
  , test "join"
    ( ok◇ "text (join (map [ x ] [ abc ])) ≟* text [ abc ]"
      (withDOW λ w → text {w} (join (map (λ s → [ s ]) [ "abc" ])) ≟* text [ "abc" ])
    , ok◇ "join (map (text [ x ]) [ abc ]) ≟* text [ abc ]"
      (withDOW λ w → join (map (λ s → text {w} [ s ]) [ "abc" ]) ≟* text [ "abc" ])
   , ok◇ "element p (join (map (attr foo [ x ]) [ alpha ]) ++ join (map (attr bar [ x ]) [ alpha ])) ≟* element p (attr foo [ alpha ] ++ attr bar [ alpha ])"
      (withDOW λ w → element "p" {w} (join (map (λ s → attr "foo" [ s ]) [ "alpha" ]) ++ join (map (λ s → attr "bar" [ s ]) [ "alpha" ])) ≟* element "p" (attr "foo" [ "alpha" ] ++ attr "bar" [ "alpha" ]))
   , ok◇ "element p (join (map (attr foo [ x ]) [ beta ]) ++ join (map (attr bar [ x ]) [ alpha ])) ≟* element p (attr foo [ alpha ] ++ attr bar [ alpha ])"
      (withDOW λ w → not* (element "p" {w} (join (map (λ s → attr "foo" [ s ]) [ "beta" ]) ++ join (map (λ s → attr "bar" [ s ]) [ "alpha" ])) ≟* element "p" (attr "foo" [ "alpha" ] ++ attr "bar" [ "alpha" ])))
    , ok◇ "text (join (map [ x ] [ a ])) ≟* text [ abc ]"
      (withDOW λ w → not* (text {w} (join (map (λ s → [ s ]) [ "a" ])) ≟* text [ "abc" ]))
    , ok◇ "join (map (text [ x ]) [ a ]) ≟* text [ abc ]"
      (withDOW λ w → not* (join (map (λ s → text {w} [ s ]) [ "a" ]) ≟* text [ "abc" ])) ) )

