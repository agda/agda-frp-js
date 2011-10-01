{-# OPTIONS --universe-polymorphism #-}

open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∨_ ; _∧_ )
open import FRP.JS.True using ( True ; tt ; contradiction ; ∧-intro ; ∧-elim₁ ; ∧-elim₂ )
open import FRP.JS.Nat using ( ℕ ; _+_ ; _∸_ )
open import FRP.JS.Keys using ( Keys ; IKeys ; IKeys✓ ; _<?_ ; head ) 
  renaming ( ikeys to ikeysk ; ikeys✓ to ikeysk✓ ; [] to []k ; _∷_ to _∷k_ )
open import FRP.JS.String using ( String ; _<_ ; _==_ )

module FRP.JS.Object where

infixr 4 _∷_
infixr 5 _↦_

record Field {α} (A : Set α) : Set α where
  constructor _↦_
  field
    key : String
    value : A

{-# COMPILED_JS Field function(x,v) { return v(x.key,x.value); } #-}
{-# COMPILED_JS _↦_ function(k) { return function(v) { return { "key": k, "value": v }; }; } #-}

open Field public

data IObject {α} (A : Set α) : ∀ ks → IKeys✓ ks → Set α where
  [] : IObject A []k tt
  _∷_ : ∀ (f : Field A) {ks k∷ks✓} →
    (as : IObject A ks (∧-elim₂ {key f <? head ks} k∷ks✓)) →
      IObject A (key f ∷k ks) k∷ks✓

{-# COMPILED_JS IObject function(x,v) {
  if (x.array.length <= x.offset) { return v["[]"](); }
  else { return v["_∷_"](x,x.tail(),null,x.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.object").empty #-}
{-# COMPILED_JS _∷_ function(f) { return function () { return function() { return function(as) {
  return as.set(f.key,f.value);
}; }; }; } #-}

ikeys : ∀ {α A ks ks✓} → IObject {α} A ks ks✓ → IKeys
ikeys {ks = ks} as = ks

ikeys✓ : ∀ {α A ks ks✓} as → IKeys✓ (ikeys {α} {A} {ks} {ks✓} as)
ikeys✓ {ks✓ = ks✓} as = ks✓

record Object {α} (A : Set α) : Set α where
  constructor [_]
  field
    {keys} : Keys
    iobject : IObject A (ikeysk keys) (ikeysk✓ keys)

open Object public

{-# COMPILED_JS Object function(x,v) { 
  return v["[_]"](require("agda.object").keys(x),require("agda.object").iobject(x));
} #-}
{-# COMPILED_JS [_] function() { return function(as) { return as.object(); }; } #-}
{-# COMPILED_JS keys require("agda.object").keys #-}
{-# COMPILED_JS iobject require("agda.object").iobject #-}

open Object public

ilookup : ∀ {α A ks ks✓} → IObject {α} A ks ks✓ → String → Maybe A
ilookup []           l = nothing
ilookup (k ↦ a ∷ as) l 
 with k == l
... | true  = just a
... | false = ilookup as l

{-# COMPILED_JS ilookup function() { return function() { return function() { return function() {
  return function(as) { return function(l) { return as.get(l); }; };
}; }; }; } #-}

lookup : ∀ {α A} → Object {α} A → String → Maybe A
lookup [ as ] l = ilookup as l

{-# COMPILED_JS lookup function() { return function() { 
  return function(as) { return function(l) { return require("agda.object").lookup(as,l); }; }; 
}; } #-}

imap : ∀ {α β A B} → (String → A → B) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → IObject {β} B ks ks✓
imap f []           = []
imap f (k ↦ a ∷ as) = (k ↦ f k a ∷ imap f as)

{-# COMPILED_JS imap function() { return function() { return function() { return function() {
  return function(f) { return function() { return function() { return function(as) {
    return as.map(function(a,s) { return f(s)(a); });
  }; }; }; };
}; }; }; } #-}

mapi : ∀ {α β A B} → (String → A → B) → Object {α} A → Object {β} B
mapi f [ as ] = [ imap f as ]

{-# COMPILED_JS mapi function() { return function() { return function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").map(function(a,s) { return f(s)(a); },as);
  }; };
}; }; }; } #-}

map : ∀ {α β A B} → (A → B) → Object {α} A → Object {β} B
map f = mapi (λ s → f)

{-# COMPILED_JS map function() { return function() { return function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").map(f,as);
  }; };
}; }; }; } #-}

iall : ∀ {α A} → (String → A → Bool) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → Bool
iall f []           = true
iall f (k ↦ a ∷ as) = f k a ∧ iall f as

{-# COMPILED_JS iall function() { return function() {
  return function(f) { return function() { return function() { return function(as) {
    return as.all(function(a,s) { return f(s)(a); });
  }; }; }; };
}; } #-}

alli : ∀ {α A} → (String → A → Bool) → Object {α} A → Bool
alli f [ as ] = iall f as

{-# COMPILED_JS alli function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").all(function(a,s) { return f(s)(a); },as);
  }; };
}; } #-}

all : ∀ {α A} → (A → Bool) → Object {α} A → Bool
all f = alli (λ s → f)

{-# COMPILED_JS all function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").all(f,as);
  }; };
}; } #-}

must : ∀ {α A} → (A → Bool) → (Maybe {α} A → Bool)
must f nothing  = false
must f (just a) = f a

_⊆[_]_ : ∀ {α β A B} → Object {α} A → (A → B → Bool) → Object {β} B → Bool
as ⊆[ p ] bs = alli (λ k a → must (p a) (lookup bs k)) as

kfilter : ∀ {α A} → (String → A → Bool) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → IKeys
kfilter f []           = []k
kfilter f (k ↦ a ∷ as)
 with f k a
... | true  = k ∷k kfilter f as
... | false = kfilter f as

postulate
  <-trans : ∀ {k l m} → True (k < l) → True (l < m) → True (k < m)

<?-trans : ∀ {k l m} → True (k < l) → True (l <? m) → True (k <? m)
<?-trans {m = nothing} k<l l<m = tt
<?-trans {m = just m}  k<l l<m = <-trans k<l l<m

kfilter-<? : ∀ {α A} f {ks ks✓} as k → True (k <? head ks) → 
  True (k <? head (kfilter {α} {A} f {ks} {ks✓} as))
kfilter-<? f [] k tt = tt
kfilter-<? f {ks✓ = l∷ls✓} (l ↦ a ∷ as) k k<l
 with f l a
... | true  = k<l
... | false = kfilter-<? f as k (<?-trans {m = head (ikeys as)} k<l (∧-elim₁ l∷ls✓))

kfilter✓ : ∀ {α A} f {ks ks✓} as → IKeys✓ (kfilter {α} {A} f {ks} {ks✓} as)
kfilter✓ f [] = tt
kfilter✓ f {ks✓ = k∷ks✓} (k ↦ a ∷ as) 
 with f k a
... | true  = ∧-intro (kfilter-<? f as k (∧-elim₁ k∷ks✓)) (kfilter✓ f as)
... | false = kfilter✓ f as

ifilter : ∀ {α A} f {ks ks✓} as → ∀ {ls✓} → IObject A (kfilter {α} {A} f {ks} {ks✓} as) ls✓
ifilter f [] = []
ifilter f (k ↦ a ∷ as)
 with f k a
... | true  = (k ↦ a ∷ ifilter f as)
... | false = ifilter f as

{-# COMPILED_JS ifilter function() { return function() { return function(f) { 
  return function() { return function() { return function(as) { return function() {
    return as.filter(function(a,s) { return f(s)(a); });
  }; }; }; };
}; }; } #-}

filteri : ∀ {α} {A} → (String → A → Bool) → Object {α} A → Object A
filteri f [ as ] = [ ifilter f as {kfilter✓ f as} ]

{-# COMPILED_JS filteri function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").filter(function(a,s) { return f(s)(a); },as);
  }; };
}; } #-}

filter : ∀ {α} {A} → (A → Bool) → Object {α} A → Object A
filter f = filteri (λ s → f)

{-# COMPILED_JS filter function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").filter(f,as);
  }; };
}; } #-}
