open import FRP.JS.String using ( String ; _≟_ ; _<_ )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )

module FRP.JS.Keys where

infixr 4 _∷_

data IKeys : Set where
  [] : IKeys
  _∷_ : (k : String) → (ks : IKeys) → IKeys

{-# COMPILED_JS IKeys function(x,v) {
  if ((x.array.length) <= (x.offset)) { return v["[]"](); }
  else { return v["_∷_"](x.key(),x.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.keys").iempty #-}
{-# COMPILED_JS _∷_ function(k) { return function(ks) { return ks.cons(k); }; } #-}

head : IKeys → Maybe String
head []       = nothing
head (k ∷ ks) = just k

{-# COMPILED_JS head function(ks) { return require("agda.box").box(ks.key()); } #-}

_<?_ : String → Maybe String → Bool
k <? nothing = true
k <? just l  = k < l

sorted : IKeys → Bool
sorted []       = true
sorted (k ∷ ks) = (k <? head ks) ∧ (sorted ks)

record Keys : Set where
  constructor keys
  field
    ikeys : IKeys
    {ikeys✓} : True (sorted ikeys)

open Keys public

{-# COMPILED_JS Keys function(x,v) { return v.keys(require("agda.keys").iarray(x),null); } #-}
{-# COMPILED_JS keys function(ks) { return function() { return ks.keys(); }; } #-}
{-# COMPILED_JS ikeys function(ks) { return require("agda.keys").iarray(ks); } #-}
{-# COMPILED_JS ikeys✓ function(ks) { return null; } #-}

_∈i_ : String → IKeys → Bool
l ∈i [] = false
l ∈i (k ∷ ks)
 with k ≟ l
... | true  = true
... | false 
 with k < l
... | true  = l ∈i ks
... | false = false

_∈_ : String → Keys → Bool
l ∈ keys ks = l ∈i ks
