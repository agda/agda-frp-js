{-# OPTIONS --universe-polymorphism #-}
open import FRP.JS.Level using ( Level )

module FRP.JS.Maybe where

-- Data.Maybe doesn't have bindings for JavaScript, so we define Maybe here.

-- We'd like to use JavaScript's built-in null as the representation
-- of nothing, and use x as the representation of just x.
-- Unfortunately this doens't work for nested Maybes, as it identifies
-- nothing and just nothing at type Maybe Maybe A, which in turn
-- breaks parametericity. So instead we use an object of the form { value: x }
-- as the representative of just x.

data Maybe {a : Level} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A

{-# COMPILED_JS Maybe function(x,v) { 
  if (x === null) { return v.nothing(); } else { return v.just(x.value); }
} #-}
{-# COMPILED_JS just function(x) { return { "value": x }; } #-}
{-# COMPILED_JS nothing null #-}

-- When interacting with native JS via the FFI, we don't get boxed
-- values, we get raw values, so we introduce types which are used
-- with the FFI.  Note, we introduce two types, one for inputing from
-- JS, and one for outputing to JS. If we identified these types then
-- we'd again break parametericity.

postulate
  Maybe⁺ Maybe⁻ : ∀ {a} → Set a → Set a
  maybe⁺ : ∀ {a} {A : Set a} → Maybe A → Maybe⁺ A
  maybe⁻ : ∀ {a} {A : Set a} → Maybe⁻ A → Maybe A

{-# COMPILED_JS maybe⁺ function(a) { return function(A) { return function (x) {
  if (x === null) { return null; } else { return x.value; }
}; }; } #-}

{-# COMPILED_JS maybe⁻ function(a) { return function(A) { return function (x) {
  if (x === null) { return null; } else { return { "value": x }; }
}; }; } #-}
