open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.Bool using ( Bool ; true ; false ; _∨_ ; _∧_ )
open import FRP.JS.True using ( True ; tt ; contradiction ; ∧-intro ; ∧-elim₁ ; ∧-elim₂ )
open import FRP.JS.Nat using ( ℕ ; _+_ ; _∸_ )
open import FRP.JS.Keys using ( Keys ; IKeys ; _<?_ ; sorted ; head ; _∈i_ ; _∈_ ) 
  renaming ( keys to kkeys ; ikeys to ikeysk ; ikeys✓ to ikeysk✓ ; [] to []k ; _∷_ to _∷k_ )
open import FRP.JS.String using ( String ; _<_ ; _==_ )
open import FRP.JS.String.Properties using ( <-trans )

module FRP.JS.Object where

infixr 4 _↦_∷_

data IObject {α} (A : Set α) : ∀ ks → True (sorted ks) → Set α where
  [] : IObject A []k tt
  _↦_∷_ : ∀ k (a : A) {ks k∷ks✓} → 
    (as : IObject A ks (∧-elim₂ {k <? head ks} k∷ks✓)) →
      IObject A (k ∷k ks) k∷ks✓

{-# COMPILED_JS IObject function(x,v) {
  if ((x.array.length) <= (x.offset)) { return v["[]"](); }
  else { return v["_↦_∷_"](x.key(),x.value(),x.tail(),null,x.tail()); }
} #-}
{-# COMPILED_JS [] require("agda.object").iempty() #-}
{-# COMPILED_JS _↦_∷_ function(k) { return function(a) { 
  return function () { return function() { return function(as) {
    return as.set(k,a);
}; }; }; }; } #-}

ikeys : ∀ {α A ks ks✓} → IObject {α} A ks ks✓ → IKeys
ikeys {ks = ks} as = ks

ikeys✓ : ∀ {α A ks ks✓} as → True (sorted (ikeys {α} {A} {ks} {ks✓} as))
ikeys✓ {ks✓ = ks✓} as = ks✓

record Object {α} (A : Set α) : Set α where
  constructor object
  field
    {keys} : Keys
    iobject : IObject A (ikeysk keys) (ikeysk✓ keys)

open Object public

{-# COMPILED_JS Object function(x,v) { 
  return v.object(require("agda.object").keys(x),require("agda.object").iobject(x));
} #-}
{-# COMPILED_JS object function() { return function(as) { return as.object(); }; } #-}
{-# COMPILED_JS keys function() { return function() { return require("agda.object").keys; }; } #-}
{-# COMPILED_JS iobject function() { return function() { return require("agda.object").iobject; }; } #-}

open Object public

⟪⟫ : ∀ {α A} → Object {α} A
⟪⟫ = object []

{-# COMPILED_JS ⟪⟫ function() { return function() { return {}; }; } #-}

ilookup? : ∀ {α A ks ks✓} → IObject {α} A ks ks✓ → String → Maybe A
ilookup? [] l = nothing
ilookup? (k ↦ a ∷ as) l 
 with k == l
... | true  = just a
... | false
 with k < l
... | true  = ilookup? as l
... | false = nothing

lookup? : ∀ {α A} → Object {α} A → String → Maybe A
lookup? (object as) l = ilookup? as l

{-# COMPILED_JS lookup? function() { return function() { return function(as) { return function(l) { 
  return require("agda.box").box(require("agda.object").lookup(as,l)); 
}; }; }; } #-}

ilookup : ∀ {α A ks ks✓} → IObject {α} A ks ks✓ → ∀ l → {l∈ks : True (l ∈i ks)} → A
ilookup [] l {l∈[]} = contradiction l∈[]
ilookup (k ↦ a ∷ as) l {l∈k∷ks}
 with k == l
... | true  = a
... | false
 with k < l
... | true  = ilookup as l {l∈k∷ks}
... | false = contradiction l∈k∷ks

lookup : ∀ {α A} as l → {l∈ks : True (l ∈ keys {α} {A} as)} → A
lookup (object as) l {l∈ks} = ilookup as l {l∈ks}

{-# COMPILED_JS lookup function() { return function() { return function(as) { return function(l) { return function() {
  return require("agda.object").lookup(as,l); 
}; }; }; }; } #-}

imap : ∀ {α β A B} → (String → A → B) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → IObject {β} B ks ks✓
imap f []           = []
imap f (k ↦ a ∷ as) = (k ↦ f k a ∷ imap f as)

mapi : ∀ {α β A B} → (String → A → B) → Object {α} A → Object {β} B
mapi f (object as) = object (imap f as)

map : ∀ {α β A B} → (A → B) → Object {α} A → Object {β} B
map f = mapi (λ s → f)

{-# COMPILED_JS mapi function() { return function() { return function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").map(function(a,s) { return f(s)(a); },as);
  }; };
}; }; }; } #-}

{-# COMPILED_JS map function() { return function() { return function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").map(f,as);
  }; };
}; }; }; } #-}

iall : ∀ {α A} → (String → A → Bool) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → Bool
iall f []           = true
iall f (k ↦ a ∷ as) = f k a ∧ iall f as

alli : ∀ {α A} → (String → A → Bool) → Object {α} A → Bool
alli f (object as) = iall f as

all : ∀ {α A} → (A → Bool) → Object {α} A → Bool
all f = alli (λ s → f)

{-# COMPILED_JS alli function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").all(function(a,s) { return f(s)(a); },as);
  }; };
}; } #-}

{-# COMPILED_JS all function() { return function() {
  return function(f) { return function(as) {
    return require("agda.object").all(f,as);
  }; };
}; } #-}

must : ∀ {α A} → (A → Bool) → (Maybe {α} A → Bool)
must p nothing  = false
must p (just a) = p a

_⊆[_]_ : ∀ {α β A B} → Object {α} A → (A → B → Bool) → Object {β} B → Bool
as ⊆[ p ] bs = alli (λ k a → must (p a) (lookup? bs k)) as

_==[_]_ : ∀ {α β A B} → Object {α} A → (A → B → Bool) → Object {β} B → Bool
as ==[ p ] bs = (as ⊆[ p ] bs) ∧ (bs ⊆[(λ a b → true)] as)

kfilter : ∀ {α A} → (String → A → Bool) → ∀ {ks ks✓} → IObject {α} A ks ks✓ → IKeys
kfilter f []           = []k
kfilter f (k ↦ a ∷ as)
 with f k a
... | true  = k ∷k kfilter f as
... | false = kfilter f as

<?-trans : ∀ {k l m} → True (k < l) → True (l <? m) → True (k <? m)
<?-trans {k} {l} {nothing} k<l l<m = tt
<?-trans {k} {l} {just m}  k<l l<m = <-trans {k} {l} {m} k<l l<m

kfilter-<? : ∀ {α A} f {ks ks✓} as k → True (k <? head ks) → 
  True (k <? head (kfilter {α} {A} f {ks} {ks✓} as))
kfilter-<? f [] k tt = tt
kfilter-<? f {ks✓ = l∷ls✓} (l ↦ a ∷ as) k k<l
 with f l a
... | true  = k<l
... | false = kfilter-<? f as k (<?-trans {m = head (ikeys as)} k<l (∧-elim₁ l∷ls✓))

kfilter✓ : ∀ {α A} f {ks ks✓} as → True (sorted (kfilter {α} {A} f {ks} {ks✓} as))
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

filteri : ∀ {α} {A} → (String → A → Bool) → Object {α} A → Object A
filteri f (object as) = object (ifilter f as {kfilter✓ f as})

filter : ∀ {α} {A} → (A → Bool) → Object {α} A → Object A
filter f = filteri (λ k → f)

{-# COMPILED_JS filteri function() { return function() {
  return function(p) { return function(as) {
    return require("agda.object").filter(function(a,s) { return p(s)(a); },as);
  }; };
}; } #-}

{-# COMPILED_JS filter function() { return function() {
  return function(p) { return function(as) {
    return require("agda.object").filter(p,as);
  }; };
}; } #-}

-- Syntax sugar, e.g. ⟪ "a" ↦ 1 , "b" ↦ 2 , "c" ↦ 3 ⟫ : Object ℕ

infix 3 ⟪_
infixr 4 _↦_,_ _↦_⟫

data Sugar {α} (A : Set α) : Set α where
  ε : Sugar A
  _↦_,_ : String → A → Sugar A → Sugar A

_↦_⟫ : ∀ {α A} → String → A → Sugar {α} A
k ↦ a ⟫ = (k ↦ a , ε)

skeys : ∀ {α A} → Sugar {α} A → IKeys
skeys ε            = []k
skeys (k ↦ a , as) = k ∷k skeys as

desugar : ∀ {α A} as {ks✓} → IObject A (skeys {α} {A} as) ks✓
desugar ε            = []
desugar (k ↦ a , as) = k ↦ a ∷ desugar as

⟪_ : ∀ {α A} as → {ks✓ : True (sorted (skeys {α} {A} as))} → Object A
⟪_ as {ks✓} = object {keys = kkeys (skeys as) {ks✓}} (desugar as)
