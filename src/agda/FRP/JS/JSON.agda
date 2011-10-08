{-# OPTIONS --sized-types #-}

open import FRP.JS.Bool using ( Bool ; true ; false ) renaming ( _==_ to _==b_ )
open import FRP.JS.Nat using ( ℕ )
open import FRP.JS.Float using ( ℝ ) renaming ( _==_ to _==n_ )
open import FRP.JS.String using ( String ) renaming ( _==_ to _==s_ )
open import FRP.JS.Array using ( Array ) renaming ( lookup? to alookup? ; _==[_]_ to _==a[_]_ )
open import FRP.JS.Object using ( Object ) renaming ( lookup? to olookup? ; _==[_]_ to _==o[_]_ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.Size using ( Size ; ↑_ )

module FRP.JS.JSON where

data JSON : {σ : Size} → Set where
  null : ∀ {σ} → JSON {σ}
  string : ∀ {σ} → String → JSON {σ}
  float : ∀ {σ} → ℝ → JSON {σ}
  bool : ∀ {σ} → Bool → JSON {σ}
  array : ∀ {σ} → Array (JSON {σ}) → JSON {↑ σ}
  object : ∀ {σ} → Object (JSON {σ}) → JSON {↑ σ}

{-# COMPILED_JS JSON function(x,v) {
  if (x === null) { return v.null(null); }
  else if (x.constructor === String) { return v.string(null,x); }
  else if (x.constructor === Number) { return v.float(null,x); }
  else if (x.constructor === Boolean) { return v.bool(null,x); }
  else if (x.constructor === Array) { return v.array(null,x); }
  else { return v.object(null,x); }
} #-}
{-# COMPILED_JS null   function() { return null; } #-}
{-# COMPILED_JS string function() { return function(x) { return x; }; } #-}
{-# COMPILED_JS float  function() { return function(x) { return x; }; } #-}
{-# COMPILED_JS bool   function() { return function(x) { return x; }; } #-}
{-# COMPILED_JS array  function() { return function(x) { return x; }; } #-}
{-# COMPILED_JS object function() { return function(x) { return x; }; } #-}

postulate
  show  : JSON → String
  parse : String → Maybe JSON

{-# COMPILED_JS show  JSON.stringify #-}
{-# COMPILED_JS parse require("agda.box").handle(JSON.parse) #-}

Key : Bool → Set
Key true  = String
Key false = ℕ

lookup? : ∀ {σ} → Maybe (JSON {↑ σ}) → ∀ {b} → Key b → Maybe (JSON {σ})
lookup? (just (object js)) {true}  k = olookup? js k
lookup? (just (array js))  {false} i = alookup? js i
lookup? _                          _ = nothing

_==_ : ∀ {σ τ} → JSON {σ} → JSON {τ} → Bool
null      == null      = true
string s  == string t  = s ==s t
float m   == float n   = m ==n n
bool b    == bool c    = b ==b c
array js  == array ks  = js ==a[ _==_ ] ks
object js == object ks = js ==o[ _==_ ] ks
_         == _         = false
