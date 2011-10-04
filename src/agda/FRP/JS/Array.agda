{-# OPTIONS --universe-polymorphism #-}

open import FRP.JS.Nat using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; _==_ )
open import FRP.JS.Nat.Properties using ( ≤-impl-≯ ; <-impl-s≤ ; ≤≠-impl-< ; ≤-bot )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.True using ( True ; contradiction ; dec ; yes ; no )

module FRP.JS.Array where

infixr 4 _∷_

-- IArray A m n is offset m of a length n array with contents of type A

data IArray {α} (A : Set α) : ℕ → ℕ → Set α where
  [] : ∀ {n} → IArray A n n
  _∷_ : ∀ {m n} → (a : A) → (as : IArray A (suc m) n) → IArray A m n

{-# COMPILED_JS IArray function(xs,v) {
  if (xs.array.length <= xs.offset) { return v["[]"](xs.offset); }
  else { return v["_∷_"](xs.offset,xs.array.length,xs.head(),xs.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.array").iempty #-}
{-# COMPILED_JS _∷_ function(m) { return function(n) { 
  return function(x) { return function(xs) { return xs.cons(x); }; };
}; } #-}

ilookup : ∀ {α A m n} → IArray {α} A m n → ∀ i → {m≤i : True (m ≤ i)} → {i<n : True (i < n)} → A
ilookup []       i {m≤i} {i<m} = contradiction (≤-impl-≯ m≤i i<m)
ilookup (a ∷ as) i {m≤i} {i<n} with dec _
ilookup (a ∷ as) i {m≤i} {i<n} | yes  m=i = a
ilookup (a ∷ as) i {m≤i} {i<n} | no   m≠i = ilookup as i {<-impl-s≤ (≤≠-impl-< m≤i m≠i)} {i<n}

{-# COMPILED_JS ilookup function() { return function() { return function() { return function() { 
  return function(as) { return function(i) { return function() { return function() {
    return as.lookup(i);
  }; }; }; };
}; }; }; } #-}

ilookup? : ∀ {α A m n} → IArray {α} A m n → ℕ → Maybe A
ilookup? []       i       = nothing
ilookup? (a ∷ as) zero    = just a
ilookup? (a ∷ as) (suc i) = ilookup? as i

{-# COMPILED_JS ilookup? function() { return function() { return function() { return function() { 
  return function(as) { return function(i) {
    return require("agda.box").box(as.lookup(i));
  }; };
}; }; }; } #-}

imap : ∀ {α β A B m n} → (A → B) → IArray {α} A m n → IArray {β} B m n
imap f [] = []
imap f (a ∷ as) = f a ∷ imap f as

{-# COMPILED_JS imap function() { return function() { return function() { return function() { 
  return function() { return function() { return function(f) { return function(as) { return as.map(f); }; }; }; };
}; }; }; } #-}

iall : ∀ {α A m n} → (A → Bool) → IArray {α} A m n → Bool
iall f []       = true
iall f (a ∷ as) = f a ∧ iall f as

{-# COMPILED_JS iall function() { return function() { return function() { return function() { 
  return function(f) { return function(as) { return as.array.every(f); }; };
}; }; }; } #-}

_==i[_]_ : ∀ {α β A B l m n} → IArray {α} A l m → (A → B → Bool) → IArray {β} B l n → Bool
[]       ==i[ p ] []       = true
(a ∷ as) ==i[ p ] (b ∷ bs) = (p a b) ∧ (as ==i[ p ] bs)
as       ==i[ p ] bs       = false

{-# COMPILED_JS _==i[_]_ function() { return function() { return function() { return function() { 
  return function() { return function() { return function() { 
    return function(as) { return function(p) { return function(bs) {
      return require("agda.array").ievery2(as,bs,function(a,b) { return p(a)(b); });
    }; }; };
  }; }; };
}; }; }; } #-}

data Array {α} (A : Set α) : Set α where
  [_] : ∀ {n} → (as : IArray A 0 n) → Array A

{-# COMPILED_JS Array function(as,v) { return v["[_]"](as.length,require("agda.array").iarray(as)); } #-}
{-# COMPILED_JS [_] function(n) { return function(as) { return as.array; }; } #-}

length : ∀ {α A} → Array {α} A → ℕ
length ([_] {n} as) = n

{-# COMPILED_JS length function() { return function() { return function(as) { return as.length; }; }; } #-}

iarray : ∀ {α A} → (as : Array {α} A) → IArray A 0 (length as)
iarray [ as ] = as

{-# COMPILED_JS iarray function() { return function() { return require("agda.array").iarray; }; } #-}

lookup : ∀ {α A} (as : Array {α} A) i → {i<#as : True (i < length as)} → A
lookup [ as ] i {i<#as} = ilookup as i {≤-bot} {i<#as}

{-# COMPILED_JS lookup function() { return function() { return function(as) { return function(i) { return function() {
  return require("agda.array").lookup(as,i); 
}; }; }; }; } #-}

lookup? : ∀ {α A} → Array {α} A → ℕ → Maybe A
lookup? [ as ] i = ilookup? as i

{-# COMPILED_JS lookup? function() { return function() { return function(as) { return function(i) {
  return require("agda.box").box(require("agda.array").lookup(as,i)); 
}; }; }; } #-}

map : ∀ {α β A B} → (A → B) → Array {α} A → Array {β} B
map f [ as ] = [ imap f as ]

{-# COMPILED_JS map function() { return function() { return function() { return function() {
  return function(f) { return function(as) { return as.map(f); }; };
}; }; }; } #-}

all : ∀ {α A} → (A → Bool) → Array {α} A → Bool
all f [ as ] = iall f as

{-# COMPILED_JS all function() { return function() {
  return function(f) { return function(as) { return as.every(f); }; };
}; } #-}

_==[_]_ : ∀ {α β A B} → Array {α} A → (A → B → Bool) → Array {β} B → Bool
[ as ] ==[ p ] [ bs ] = as ==i[ p ] bs

{-# COMPILED_JS _==[_]_ function() { return function() { return function() { return function() {
  return function(as) { return function(p) { return function(bs) {
    return require("agda.array").every2(as,bs,function(a,b) { return p(a)(b); });
  }; }; };
}; }; }; } #-}
