open import FRP.JS.RSet using ( RSet ; ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.String using ( String )

module FRP.JS.DOM where

infixr 4 _++_

postulate
  DOM : RSet
  text : ⟦ Beh ⟨ String ⟩ ⇒ Beh DOM ⟧
  element : String → ⟦ Beh DOM ⇒ Beh DOM ⟧
  [] : ⟦ Beh DOM ⟧
  _++_ : ⟦ Beh DOM ⇒ Beh DOM ⇒ Beh DOM ⟧

{-# COMPILED_JS text function(s) { return function(b) { return b.text(); }; } #-}
{-# COMPILED_JS element function(a) { return function(s) { return function(b) { return b.element(a); }; }; } #-}
{-# COMPILED_JS [] require("agda.frp").empty #-}
{-# COMPILED_JS _++_ function(s) { return function(a) { return function(b) { return a.concat(b); }; }; } #-}
 
