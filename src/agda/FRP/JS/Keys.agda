open import FRP.JS.String using ( String ; _<_ )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ )
open import FRP.JS.True using ( True )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )

module FRP.JS.Keys where

infixr 4 _∷_

data IKeys : Set where
  [] : IKeys
  _∷_ : (k : String) → (ks : IKeys) → IKeys

{-# COMPILED_JS IKeys function(x,v) {
  if (x.array.length <= x.offset) { return v["[]"](); }
  else { return v["_∷_"](x.head(),x.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.keys").iempty #-}
{-# COMPILED_JS _∷_ function(k) { return function(ks) { return ks.cons(k); }; } #-}

head : IKeys → Maybe String
head []       = nothing
head (k ∷ ks) = just k

{-# COMPILED_JS head function(ks) { return ks.head(); } #-}

_<?_ : String → Maybe String → Bool
k <? nothing = true
k <? just l  = k < l

sorted : IKeys → Bool
sorted []       = true
sorted (k ∷ ks) = (k <? head ks) ∧ (sorted ks)

IKeys✓ : IKeys → Set
IKeys✓ ks = True (sorted ks)

record Keys : Set where
  constructor [_]
  field
    ikeys : IKeys
    {ikeys✓} : IKeys✓ ikeys

open Keys public

{-# COMPILED_JS [_] function(x,v) { return v["[_]"](require("agda.keys").iarray(x,null)); } #-}
{-# COMPILED_JS ikeys function(ks) { return require("agda.keys").iarray(ks); } #-}
{-# COMPILED_JS ikeys✓ function(ks) { return null; } #-}