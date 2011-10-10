open import FRP.JS.RSet using ( RSet ; _⇒_ ; ⟦_⟧ ; ⟨_⟩ )

module FRP.JS.Event where

infixr 4 _∪_

postulate
  Evt : RSet → RSet
  map : ∀ {A B} → ⟦ A ⇒ B ⟧ → ⟦ Evt A ⇒ Evt B ⟧
  ∅ : ∀ {A} → ⟦ Evt A ⟧
  _∪_ : ∀ {A} → ⟦ Evt A ⇒ Evt A ⇒ Evt A ⟧
  accumBy : ∀ {A B} → ⟦ ⟨ B ⟩ ⇒ A ⇒ ⟨ B ⟩ ⟧ → B → ⟦ Evt A ⇒ Evt ⟨ B ⟩ ⟧

{-# COMPILED_JS map function(A) { return function(B) { 
  return function(f) { return function(s) { return function(e) { 
    return e.map(function (t,v) { return f(t)(v); });
  }; }; }; 
}; } #-} 

{-# COMPILED_JS ∅ function(A) { return require("agda.frp.signal").zero; } #-}

{-# COMPILED_JS _∪_ function(A) { return function(s) { 
  return function(x) { return function(y) { return x.merge(y); }; };
}; } #-} 

{-# COMPILED_JS accumBy function(A) { return function(B) { return function(f) { 
  return function(b) { return function(s) { return function(e) {
    return e.accumBy(function(t,b,a) { return f(t)(b)(a); },b);
  }; }; };
}; }; } #-} 

tag : ∀ {A B} → ⟦ B ⟧ → ⟦ Evt A ⇒ Evt B ⟧
tag b = map (λ _ → b)