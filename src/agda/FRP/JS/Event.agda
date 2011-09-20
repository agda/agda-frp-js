open import FRP.JS.RSet using ( RSet ; _⇒_ ; ⟦_⟧ ; ⟨_⟩ )

module FRP.JS.Event where

postulate
  Evt : RSet → RSet
  map : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ Evt A ⇒ Evt B ⟧

{-# COMPILED_JS map function(A) { return function(B) { 
  return function(f) { return function(s) { return function(e) { 
    return e.map(function (t,v) { return f(t)(v); });
  }; }; }; 
}; } #-} 

tag : ∀ {A B} → ⟦ B ⟧ → ⟦ Evt A ⇒ Evt B ⟧
tag b = map (λ _ → b)