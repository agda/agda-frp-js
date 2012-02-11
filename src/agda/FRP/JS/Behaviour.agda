open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Event using ( Evt ; accumBy )
open import FRP.JS.RSet using ( RSet ; _⇒_ ; ⟦_⟧ ; ⟨_⟩ )

module FRP.JS.Behaviour where

postulate
  Beh : RSet → RSet
  map : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ Beh A ⇒ Beh B ⟧
  map2 : ∀ {A B C} → ⟦ A ⇒ B ⇒ C ⟧ → ⟦ Beh A ⇒ Beh B ⇒ Beh C ⟧
  [_] : ∀ {A} → A → ⟦ Beh ⟨ A ⟩ ⟧
  hold : ∀ {A} → ⟦ ⟨ A ⟩ ⇒ Evt ⟨ A ⟩ ⇒ Beh ⟨ A ⟩ ⟧

{-# COMPILED_JS map function(A) { return function(B) { 
  return function(f) { return function(s) { return function(b) { 
    return b.map(function (t,v) { return f(t)(v); });
  }; }; }; 
}; } #-} 

{-# COMPILED_JS map2 function(A) { return function(B) { return function(C) {
  return function(f) { return function(s) { return function(a) { return function(b) {
    return a.map2(b, function (t,v1,v2) { return f(t)(v1)(v2); });
  }; }; }; };
}; }; } #-}

{-# COMPILED_JS [_] function(A) { return function(a) { return function(s) { 
  return require("agda.frp").constant(a);
}; }; } #-}

{-# COMPILED_JS hold function(A) { return function(s) { return function(a) { return function(e) {
  return e.hold(a);
}; }; }; } #-}

accumHoldBy : ∀ {A B} → ⟦ (⟨ B ⟩ ⇒ A ⇒ ⟨ B ⟩) ⟧ → B → ⟦ Evt A ⇒ Beh ⟨ B ⟩ ⟧
accumHoldBy f b σ = hold b (accumBy f b σ)

not* : ⟦ Beh ⟨ Bool ⟩ ⇒ Beh ⟨ Bool ⟩ ⟧
not* = map not
