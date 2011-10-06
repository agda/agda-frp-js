{-# OPTIONS --universe-polymorphism #-}

open import FRP.JS.Nat using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; _==_ ; _+_ )
open import FRP.JS.Nat.Properties using ( ≤-impl-≯ ; <-impl-s≤ ; ≤≠-impl-< ; ≤-bot )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∧_ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.True using ( True ; contradiction ; dec ; yes ; no )

module FRP.JS.Array where

infixr 5 _∷_
infixr 4 _++i_

-- IArray A m n is offset m of a length n array with contents of type A

data IArray {α} (A : Set α) : ℕ → ℕ → Set α where
  [] : ∀ {n} → IArray A n n
  _∷_ : ∀ {m n} → (a : A) → (as : IArray A (suc m) n) → IArray A m n

data Array {α} (A : Set α) : Set α where
  array : ∀ {n} → (as : IArray A 0 n) → Array A

{-# COMPILED_JS IArray function(xs,v) {
  if ((xs.array.length) <= (xs.offset)) { return v["[]"](xs.offset); }
  else { return v["_∷_"](xs.offset,xs.array.length,xs.head(),xs.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.array").iempty #-}
{-# COMPILED_JS _∷_ function(m) { return function(n) { 
  return function(x) { return function(xs) { return xs.cons(x); }; };
}; } #-}
{-# COMPILED_JS Array function(as,v) { 
  return v.array(as.length,require("agda.array").iarray(as));
} #-}
{-# COMPILED_JS array function(n) { return function(as) { return as.array; }; } #-}

length : ∀ {α A} → Array {α} A → ℕ
length (array {n} as) = n

{-# COMPILED_JS length function() { return function() { return function(as) { return as.length; }; }; } #-}

iarray : ∀ {α A} → (as : Array {α} A) → IArray A 0 (length as)
iarray (array as) = as

{-# COMPILED_JS iarray function() { return function() { return require("agda.array").iarray; }; } #-}

⟨⟩ : ∀ {α A} → Array {α} A
⟨⟩ = array []

{-# COMPILED_JS ⟨⟩ function() { return function() { return require("agda.array").empty; }; } #-}

ilookup : ∀ {α A m n} → IArray {α} A m n → ∀ i → {m≤i : True (m ≤ i)} → {i<n : True (i < n)} → A
ilookup []       i {m≤i} {i<m} = contradiction (≤-impl-≯ m≤i i<m)
ilookup (a ∷ as) i {m≤i} {i<n} with dec _
ilookup (a ∷ as) i {m≤i} {i<n} | yes  m=i = a
ilookup (a ∷ as) i {m≤i} {i<n} | no   m≠i = ilookup as i {<-impl-s≤ (≤≠-impl-< m≤i m≠i)} {i<n}

lookup : ∀ {α A} (as : Array {α} A) i → {i<#as : True (i < length as)} → A
lookup (array as) i {i<#as} = ilookup as i {≤-bot} {i<#as}

{-# COMPILED_JS lookup function() { return function() { return function(as) { return function(i) { return function() {
  return require("agda.array").lookup(as,i); 
}; }; }; }; } #-}

ilookup? : ∀ {α A m n} → IArray {α} A m n → ℕ → Maybe A
ilookup? []       i       = nothing
ilookup? (a ∷ as) zero    = just a
ilookup? (a ∷ as) (suc i) = ilookup? as i

lookup? : ∀ {α A} → Array {α} A → ℕ → Maybe A
lookup? (array as) i = ilookup? as i

{-# COMPILED_JS lookup? function() { return function() { return function(as) { return function(i) {
  return require("agda.box").box(require("agda.array").lookup(as,i)); 
}; }; }; } #-}

imap : ∀ {α β A B m n} → (A → B) → IArray {α} A m n → IArray {β} B m n
imap f [] = []
imap f (a ∷ as) = f a ∷ imap f as

map : ∀ {α β A B} → (A → B) → Array {α} A → Array {β} B
map f (array as) = array (imap f as)

{-# COMPILED_JS map function() { return function() { return function() { return function() {
  return function(f) { return function(as) { return as.map(f); }; };
}; }; }; } #-}

#filter : ∀ {α A m n} → (A → Bool) → IArray {α} A m n → ℕ → ℕ
#filter p []       l = l
#filter p (a ∷ as) l
 with p a
... | true  = #filter p as (1 + l)
... | false = #filter p as l

ifilter : ∀ {α A l m n} p as → IArray A l (#filter {α} {A} {m} {n} p as l)
ifilter p []       = []
ifilter p (a ∷ as)
 with p a
... | true  = a ∷ ifilter p as
... | false = ifilter p as

filter : ∀ {α A} → (A → Bool) → Array {α} A → Array A
filter p (array as) = array (ifilter p as)

{-# COMPILED_JS filter function() { return function() {
  return function(p) { return function(as) { return as.filter(p); }; };
}; } #-}

iall : ∀ {α A m n} → (A → Bool) → IArray {α} A m n → Bool
iall f []       = true
iall f (a ∷ as) = f a ∧ iall f as

all : ∀ {α A} → (A → Bool) → Array {α} A → Bool
all f (array as) = iall f as

{-# COMPILED_JS all function() { return function() {
  return function(f) { return function(as) { return as.every(f); }; };
}; } #-}

_==i[_]_ : ∀ {α β A B l m n} → IArray {α} A l m → (A → B → Bool) → IArray {β} B l n → Bool
[]       ==i[ p ] []       = true
(a ∷ as) ==i[ p ] (b ∷ bs) = (p a b) ∧ (as ==i[ p ] bs)
as       ==i[ p ] bs       = false

_==[_]_ : ∀ {α β A B} → Array {α} A → (A → B → Bool) → Array {β} B → Bool
array as ==[ p ] array bs = as ==i[ p ] bs

{-# COMPILED_JS _==[_]_ function() { return function() { return function() { return function() {
  return function(as) { return function(p) { return function(bs) {
    return require("agda.array").equals(as,bs,function(a,b) { return p(a)(b); });
  }; }; };
}; }; }; } #-}

_⊆i[_]_ : ∀ {α β A B l m n} → IArray {α} A l m → (A → B → Bool) → IArray {β} B l n → Bool
[]       ⊆i[ p ] bs       = true
(a ∷ as) ⊆i[ p ] []       = false
(a ∷ as) ⊆i[ p ] (b ∷ bs) = (p a b) ∧ (as ⊆i[ p ] bs)

_⊆[_]_ : ∀ {α β A B} → Array {α} A → (A → B → Bool) → Array {β} B → Bool
array as ⊆[ p ] array bs = as ⊆i[ p ] bs

{-# COMPILED_JS _⊆[_]_ function() { return function() { return function() { return function() {
  return function(as) { return function(p) { return function(bs) {
    return require("agda.array").subseteq(as,bs,function(a,b) { return p(a)(b); });
  }; }; };
}; }; }; } #-}

igrow : ∀ {α A l m n} → IArray {α} A l n → IArray A (l + m) (n + m)
igrow []       = []
igrow (a ∷ as) = a ∷ igrow as

_++i_ : ∀ {α A l m n} → IArray {α} A l m → IArray A 0 n → IArray A l (n + m)
[]       ++i bs = igrow bs
(a ∷ as) ++i bs = a ∷ (as ++i bs)

_++_ :  ∀ {α A} → Array {α} A → Array {α} A → Array {α} A
array as ++ array bs = array (as ++i bs)

{-# COMPILED_JS _++_ function() { return function() {
  return function(as) { return function(bs) { return as.concat(bs); }; };
}; } #-}

-- Surface syntax, e.g. ⟨ 1 , 2 , 3 ⟩ : Array ℕ

infix 3 ⟨_
infixr 4 _,_
infixr 5 _⟩

data Sugar {α} (A : Set α) : Set α where
  ε : Sugar A
  _,_ : A → Sugar A → Sugar A

_⟩ : ∀ {α A} → A → Sugar {α} A
a ⟩ = (a , ε)

slength : ∀ {α A} → Sugar {α} A → ℕ → ℕ
slength ε        m = m
slength (a , as) m = slength as (1 + m)

desugar : ∀ {α A m} as → IArray A m (slength {α} {A} as m)
desugar ε        = []
desugar (a , as) = a ∷ desugar as

⟨_ : ∀ {α A} → Sugar {α} A → Array A
⟨ as = array (desugar as)
