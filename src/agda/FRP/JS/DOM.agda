open import FRP.JS.RSet using ( RSet ; ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.Event using ( Evt ; ∅ ; _∪_ ; map )
open import FRP.JS.Product using ( _∧_ ; _,_ )
open import FRP.JS.String using ( String )

module FRP.JS.DOM where

infixr 4 _++_ _+++_

postulate
  Mouse Keyboard : RSet
  EventType : RSet → Set
  click : EventType Mouse
  press : EventType Keyboard

{-# COMPILED_JS click "click" #-}
{-# COMPILED_JS press "press" #-}

postulate
  DOW : Set
  left right : DOW → DOW
  child : String → DOW → DOW
  events : ∀ {A} → EventType A → DOW → ⟦ Evt A ⟧

{-# COMPILED_JS left function(w) { return w.left(); } #-}
{-# COMPILED_JS right function(w) { return w.right(); } #-}
{-# COMPILED_JS child function(a) { return function(w) { return w.child(a); }; } #-}
{-# COMPILED_JS events function(A) { return function(t) { return function(w) { return function(s) { return w.events(t); }; }; }; } #-}

postulate
  DOM : DOW → RSet
  text : ∀ {w} → ⟦ Beh ⟨ String ⟩ ⇒ Beh (DOM w) ⟧
  attr : ∀ {w} → String → ⟦ Beh ⟨ String ⟩ ⇒ Beh (DOM w) ⟧
  element : ∀ a {w} → ⟦ Beh (DOM (child a w)) ⇒ Beh (DOM w) ⟧
  [] : ∀ {w} → ⟦ Beh (DOM w) ⟧
  _++_ : ∀ {w} → ⟦ Beh (DOM (left w)) ⇒ Beh (DOM (right w)) ⇒ Beh (DOM w) ⟧

{-# COMPILED_JS attr function(w) { return function(k) { return function(s) { return function(b) { return b.attribute(k); }; }; }; } #-}
{-# COMPILED_JS text function(w) { return function(s) { return function(b) { return b.text(); }; }; } #-}
{-# COMPILED_JS element function(a) { return function(w) { return function(s) { return function(b) { return w.element(a,b); }; }; }; } #-}
{-# COMPILED_JS [] function(w) { return require("agda.frp").empty; } #-}
{-# COMPILED_JS _++_ function(w) { return function(s) { return function(a) { return function(b) { return a.concat(b); }; }; }; } #-}
 
listen : ∀ {A w} → EventType A → ⟦ Beh (DOM w) ⇒ Evt A ⟧
listen {A} {w} t b = events t w

{-# COMPILED_JS listen function(A) { return function(w) { return function(t) { return function(s) { return function(b) { return w.events(t); }; }; }; }; } #-}

[+] : ∀ {A w} → ⟦ Beh (DOM w) ∧ Evt A ⟧
[+] = ([] , ∅)

_+++_ : ∀ {A w} → ⟦ (Beh (DOM (left w)) ∧ Evt A) ⇒ (Beh (DOM (right w)) ∧ Evt A) ⇒ (Beh (DOM w) ∧ Evt A) ⟧
(dom₁ , evt₁) +++ (dom₂ , evt₂) = ((dom₁ ++ dom₂) , (evt₁ ∪ evt₂))

text+ : ∀ {A w} → ⟦ Beh ⟨ String ⟩ ⇒ (Beh (DOM w) ∧ Evt A) ⟧
text+ msg = (text msg , ∅)

attr+ : ∀ {A w} → String → ⟦ Beh ⟨ String ⟩ ⇒ (Beh (DOM w) ∧ Evt A) ⟧
attr+ key val = (attr key val , ∅)

element+ : ∀ a {A w} → ⟦ (Beh (DOM (child a w)) ∧ Evt A) ⇒ (Beh (DOM w) ∧ Evt A) ⟧
element+ a (dom , evt) = (element a dom , evt)

listen+ : ∀ {A B w} → EventType A → ⟦ A ⇒ B ⟧ → ⟦ (Beh (DOM w) ∧ Evt B) ⇒ (Beh (DOM w) ∧ Evt B) ⟧
listen+ t f (dom , evt) = (dom , map f (listen t dom) ∪ evt)
