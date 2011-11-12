open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; subst ; cong ; cong₂ ; begin_ ; _≡⟨_⟩_ ; _∎ ; ≡-relevant
  ; id ; _∘_  )
open import FRP.JS.List using () renaming
  ( List to ♭List ; [] to []♭ ; _∷_ to _∷♭_ ; _++_ to _++♭_ ; lookup to lookup♭ ; length to length♭ )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing )
open import FRP.JS.Nat using ( zero ; suc ) renaming ( _+_ to _+♭_ )
open import FRP.JS.Model.DNat using ( ℕ ; ♯0 ; _+_ ; iso-resp-+ ) renaming 
  ( ♭ to ♭ⁿ ; ♯ to ♯ⁿ ; iso to isoⁿ ; iso⁻¹ to isoⁿ⁻¹ )

module FRP.JS.Model.DList where

infixr 4 _++_ 
infixl 3 _≪_
infixr 2 _≫_

cat : ∀ {A : Set} → ♭List A → ♭List A → ♭List A
cat = _++♭_

cat-assoc : ∀ {A} (as bs : ♭List A) → (cat (cat as bs) ≡ ((cat as) ∘ (cat bs)))
cat-assoc []♭       bs = refl
cat-assoc (a ∷♭ as) bs = cong (_∘_ (_∷♭_ a)) (cat-assoc as bs)

cat-unit : ∀ {A} (as : ♭List A) → cat as []♭ ≡ as
cat-unit []♭       = refl
cat-unit (a ∷♭ as) = cong (_∷♭_ a) (cat-unit as)

-- List A is isomorphic to ♭List A, but has associativity of concatenation
-- up to beta reduction, not just up to propositional equality.
-- We keep track of the length explicitly to ensure that length is a monoid
-- homomorphism up to beta-reduction, not just up to ≡.

record List (A : Set) : Set where
  constructor list
  field
    length : ℕ
    fun : ♭List A → ♭List A
    .length✓ : length ≡ ♯ⁿ (length♭ (fun []♭))
    .fun✓ : fun ≡ cat (fun []♭)

open List public

-- Convert any list into a Seq and back

♯ : ∀ {A} → ♭List A → List A
♯ as = list 
  (♯ⁿ (length♭ as)) 
  (cat as) 
  (cong (♯ⁿ ∘ length♭) (sym (cat-unit as)))
  (cong cat (sym (cat-unit as)))

♭ : ∀ {A} → List A → ♭List A
♭ (list n f n✓ f✓) = f []♭

-- Empty list

[] : ∀ {A} → List A
[] = ♯ []♭

-- Singleton

[_] : ∀ {A} → A → List A
[ a ] = ♯ (a ∷♭ []♭)

-- Concatenation

length♭-resp-++ : ∀ {A : Set} (as bs : ♭List A) → length♭ (as ++♭ bs) ≡ (length♭ as +♭ length♭ bs)
length♭-resp-++ []♭       bs = refl
length♭-resp-++ (a ∷♭ as) bs = cong (_+♭_ 1) (length♭-resp-++ as bs)

_++_ : ∀ {A} → List A → List A → List A
list m f m✓ f✓ ++ list n g n✓ g✓ = list (m + n) (f ∘ g) m+n✓ f∘g✓ where
  .m+n✓ : (m + n) ≡ ♯ⁿ (length♭ (f (g []♭)))
  m+n✓ = begin
      m + n
    ≡⟨ cong₂ _+_ m✓ n✓ ⟩
      ♯ⁿ (length♭ (f []♭)) + ♯ⁿ (length♭ (g []♭))
    ≡⟨ sym (isoⁿ (♯ⁿ (length♭ (f []♭)) + ♯ⁿ (length♭ (g []♭)))) ⟩
      ♯ⁿ (♭ⁿ (♯ⁿ (length♭ (f []♭)) + ♯ⁿ (length♭ (g []♭))))
    ≡⟨ cong ♯ⁿ (iso-resp-+ (♯ⁿ (length♭ (f []♭))) (♯ⁿ (length♭ (g []♭)))) ⟩
      ♯ⁿ (♭ⁿ (♯ⁿ (length♭ (f []♭))) +♭ ♭ⁿ (♯ⁿ (length♭ (g []♭))))
    ≡⟨ cong ♯ⁿ (cong₂ _+♭_ (isoⁿ⁻¹ (length♭ (f []♭))) (isoⁿ⁻¹ (length♭ (g []♭)))) ⟩
      ♯ⁿ (length♭ (f []♭) +♭ length♭ (g []♭))
    ≡⟨ cong ♯ⁿ (sym (length♭-resp-++ (f []♭) (g []♭))) ⟩
      ♯ⁿ (length♭ (f []♭ ++♭ g []♭))
    ≡⟨ cong (λ X → ♯ⁿ (length♭ (X (g []♭)))) (sym f✓) ⟩
      ♯ⁿ (length♭ (f (g []♭)))
    ∎
  .f∘g✓ : (f ∘ g) ≡ cat (f (g []♭))
  f∘g✓ = begin
      f ∘ g
    ≡⟨ cong₂ _∘_ f✓ g✓ ⟩
      cat (f []♭) ∘ cat (g []♭)
    ≡⟨ sym (cat-assoc (f []♭) (g []♭)) ⟩
      cat (f []♭ ++♭ g []♭)
    ≡⟨ cong (λ X → cat (X (g []♭))) (sym f✓) ⟩
      cat (f (g []♭))
    ∎

-- Cons

_∷_ : ∀ {A} → A → List A → List A
a ∷ as = [ a ] ++ as

-- Ismorphism between List and ♭List which respects ++ and length

inject : ∀ {A} (as bs : List A) → (length as ≡ length bs) → (fun as ≡ fun bs) → (as ≡ bs)
inject (list m f m✓ f✓) (list .m .f n✓ g✓) refl refl = refl

iso : ∀ {A} (as : List A) → ♯ (♭ as) ≡ as
iso as = inject (♯ (♭ as)) as (sym (≡-relevant (length✓ as))) (sym (≡-relevant (fun✓ as))) 

iso⁻¹ : ∀ {A} (as : ♭List A) → ♭ (♯ as) ≡ as
iso⁻¹ = cat-unit

iso-resp-++ : ∀ {A} (as bs : List A) → ♭ (as ++ bs) ≡ (♭ as ++♭ ♭ bs)
iso-resp-++ (list m f m✓ f✓) (list n g n✓ g✓) = cong (λ X → X (g []♭)) (≡-relevant f✓)

iso-resp-length : ∀ {A} (as : List A) → ♭ⁿ (length as) ≡ length♭ (♭ as)
iso-resp-length as = 
  begin
    ♭ⁿ (length as)
  ≡⟨ cong (♭ⁿ ∘ length) (sym (iso as)) ⟩
    ♭ⁿ (♯ⁿ (length♭ (♭ as))) 
  ≡⟨ isoⁿ⁻¹ (length♭ (♭ as)) ⟩
    length♭ (♭ as)
  ∎

-- Associtivity and units on the nose

++-assoc : ∀ {A} (as bs cs : List A) → ((as ++ bs) ++ cs) ≡ (as ++ (bs ++ cs))
++-assoc as bs cs = refl

++-unit₁ : ∀ {A} (as : List A) → (([] ++ as) ≡ as)
++-unit₁ as = refl

++-unit₂ : ∀ {A} (as : List A) → ((as ++ []) ≡ as)
++-unit₂ as = refl

-- Length is a monoid homomorphism on the nose

length-resp-++ : ∀ {A} (as bs : List A) → (length (as ++ bs) ≡ (length as + length bs))
length-resp-++ as bs = refl

length-resp-[] : ∀ {A} → (length {A} [] ≡ ♯0)
length-resp-[] = refl

-- Lookup

lookup : ∀ {A} → List A → ℕ → Maybe A
lookup as n = lookup♭ (♭ as) (♭ⁿ n)

lookup♭₁ : ∀ {A : Set} {a : A} as bs n → 
  (lookup♭ as n ≡ just a) → (lookup♭ (as ++♭ bs) n ≡ just a)
lookup♭₁ []♭       bs n       ()
lookup♭₁ (a ∷♭ as) bs zero    refl    = refl
lookup♭₁ (a ∷♭ as) bs (suc n) as[n]≡a = lookup♭₁ as bs n as[n]≡a

lookup♭₂ : ∀ {A : Set} {a : A} as bs n → 
  (lookup♭ bs n ≡ just a) → (lookup♭ (as ++♭ bs) (length♭ as +♭ n) ≡ just a)
lookup♭₂ []♭       bs n bs[n]≡a = bs[n]≡a
lookup♭₂ (a ∷♭ as) bs n bs[n]≡a = lookup♭₂ as bs n bs[n]≡a

lookup₁ : ∀ {A} {a : A} as bs n →
  (lookup as n ≡ just a) → (lookup (as ++ bs) n ≡ just a)
lookup₁ {A} {a} as bs n as[n]≡a =
  begin
    lookup♭ (♭ (as ++ bs)) (♭ⁿ n)
  ≡⟨ cong (λ X → lookup♭ X (♭ⁿ n)) (iso-resp-++ as bs) ⟩
    lookup♭ (♭ as ++♭ ♭ bs) (♭ⁿ n)
  ≡⟨ lookup♭₁ (♭ as) (♭ bs) (♭ⁿ n) as[n]≡a ⟩
    just a
  ∎

lookup₂ : ∀ {A} {a : A} as bs n → 
  (lookup bs n ≡ just a) → (lookup (as ++ bs) (length as + n) ≡ just a)
lookup₂ {A} {a} as bs n bs[n]≡a =
  begin
    lookup♭ (♭ (as ++ bs)) (♭ⁿ (length as + n))
  ≡⟨ cong₂ lookup♭ (iso-resp-++ as bs) (iso-resp-+ (length as) n) ⟩
    lookup♭ (♭ as ++♭ ♭ bs) (♭ⁿ (length as) +♭ ♭ⁿ n)
  ≡⟨ cong (λ X → lookup♭ (♭ as ++♭ ♭ bs) (X +♭ ♭ⁿ n)) (iso-resp-length as) ⟩
    lookup♭ (♭ as ++♭ ♭ bs) (length♭ (♭ as) +♭ ♭ⁿ n)
  ≡⟨ lookup♭₂ (♭ as) (♭ bs) (♭ⁿ n) bs[n]≡a ⟩
    just a
  ∎

-- Membership

record _∈_ {A} (a : A) (as : List A) : Set where
  constructor _,_
  field
    index : ℕ
    .index✓ : lookup as index ≡ just a

open _∈_ public

-- Extending membership on the left and right

_≪_ : ∀ {A} {a : A} {as} → (a ∈ as) → ∀ bs → (a ∈ (as ++ bs))
_≪_ {A} {a} {as} (n , n✓) bs = (n , lookup₁ as bs n n✓)

_≫_ : ∀ {A} {a : A} as {bs} → (a ∈ bs) → (a ∈ (as ++ bs))
_≫_ as {bs} (n , n✓) = ((length as + n) , lookup₂ as bs n n✓)

-- Membership extensions have units

≪-unit : ∀ {A} {a : A} as (a∈as : a ∈ as) →
  (a∈as ≪ []) ≡ a∈as
≪-unit as a∈as = refl

≫-unit : ∀ {A} {a : A} as (a∈as : a ∈ as) →
  ([] ≫ a∈as) ≡ a∈as
≫-unit as a∈as = refl

-- Membership extension is associative on the nose

≪-assoc : ∀ {A} {a : A} as bs cs (a∈as : a ∈ as) →
  (a∈as ≪ bs ≪ cs) ≡ (a∈as ≪ bs ++ cs)
≪-assoc as bs cs a∈as = refl

≫-≪-assoc : ∀ {A} {a : A} as bs cs (a∈bs : a ∈ bs) →
  ((as ≫ a∈bs) ≪ cs) ≡ (as ≫ (a∈bs ≪ cs))
≫-≪-assoc as bs cs a∈bs = refl

≫-assoc : ∀ {A} {a : A} as bs cs (a∈cs : a ∈ cs) →
  (as ≫ bs ≫ a∈cs) ≡ (as ≫ bs ≫ a∈cs)
≫-assoc as bs cs a∈cs = refl

-- Index is a monoid homomorphism on the nose

≪-index : ∀ {A} {a : A} as bs (a∈as : a ∈ as) →
  index (a∈as ≪ bs) ≡ index a∈as
≪-index as bs a∈as = refl

≫-index : ∀ {A} {a : A} as bs (a∈bs : a ∈ bs) →
  index (as ≫ a∈bs) ≡ (length as + index a∈bs)
≫-index as bs a∈bs = refl

-- Index is injective

index-inj : ∀ {A} (a : A) {as} (a∈as₁ a∈as₂ : a ∈ as) → 
  (index a∈as₁ ≡ index a∈as₂) → (a∈as₁ ≡ a∈as₂)
index-inj a (m , m✓) (.m , n✓) refl = refl

-- Membership of singleton

lookup-uniq : ∀ {A} {a : A} {m} {b} n → (♯ⁿ n ≡ m) → 
  (lookup (b ∷ []) m ≡ just a) → (b ≡ a)
lookup-uniq zero    refl refl = refl
lookup-uniq (suc n) refl ()

uniq : ∀ {A} {a b : A} → (a ∈ [ b ]) → (b ≡ a)
uniq (n , n✓) = lookup-uniq (♭ⁿ n) (isoⁿ n) (≡-relevant n✓)

singleton : ∀ {A} (a : A) → (a ∈ [ a ])
singleton a = (♯0 , refl)

-- Case on membership

data Case {A} a (as bs : List A) : Set where
  inj₁ : (a∈as : a ∈ as) → Case a as bs
  inj₂ : (a∈bs : a ∈ bs) → Case a as bs

-- Case function

_⋙_ : ∀ {A a} as {bs cs} → Case {A} a bs cs → Case a (as ++ bs) cs
as ⋙ inj₁ a∈bs = inj₁ (as ≫ a∈bs)
as ⋙ inj₂ a∈cs = inj₂ a∈cs

lookup♭-case : ∀ {A} {a : A} cs ds n → 
  .(lookup♭ (cs ++♭ ds ++♭ []♭) (n +♭ 0) ≡ just a) → (Case a (♯ cs) (♯ ds))
lookup♭-case []♭       ds n       n✓ = inj₂ (♯ⁿ n , n✓)
lookup♭-case (c ∷♭ cs) ds zero    n✓ = inj₁ (♯0 , n✓)
lookup♭-case (c ∷♭ cs) ds (suc n) n✓ = [ c ] ⋙ lookup♭-case cs ds n n✓

lookup-case : ∀ {A a as bs m} cs ds n →
  .(lookup (as ++ bs) m ≡ just a) → (♯ cs ≡ as) → (♯ ds ≡ bs) → (♯ⁿ n ≡ m) → 
    Case {A} a as bs
lookup-case cs ds n n✓ refl refl refl = lookup♭-case cs ds n n✓

case : ∀ {A a} as bs → (a ∈ (as ++ bs)) → Case {A} a as bs
case {A} {a} as bs (n , n✓) = 
  lookup-case {A} {a} {as} {bs} {n} (♭ as) (♭ bs) (♭ⁿ n) n✓ (iso as) (iso bs) (isoⁿ n)

-- Beta for case with ≪

lookup♭-case-≪ : ∀ {A} {a : A} cs ds n .n✓₁ .n✓₂ →
  lookup♭-case {A} {a} cs ds n n✓₂ ≡ inj₁ (♯ⁿ n , n✓₁)
lookup♭-case-≪ []♭       ds n       ()  n✓₂
lookup♭-case-≪ (c ∷♭ cs) ds zero    n✓₁ n✓₂ = refl
lookup♭-case-≪ (c ∷♭ cs) ds (suc n) n✓₁ n✓₂ = cong (_⋙_ [ c ]) (lookup♭-case-≪ cs ds n n✓₁ n✓₂)

lookup-case-≪ : ∀ {A} {a : A} {as bs m} cs ds n .m✓₁ .m✓₂ cs≡as ds≡bs n≡m →
  lookup-case {A} {a} {as} {bs} {m} cs ds n m✓₂ cs≡as ds≡bs n≡m
    ≡ inj₁ (m , m✓₁)
lookup-case-≪ cs ds n m✓₁ m✓₂ refl refl refl = lookup♭-case-≪ cs ds n m✓₁ m✓₂

case-≪ : ∀ {A a as} (a∈as : a ∈ as) bs → (case {A} {a} as bs (a∈as ≪ bs) ≡ inj₁ a∈as)
case-≪ {A} {a} {as} (n , n✓) bs = 
  lookup-case-≪ {A} {a} {as} {bs} {n} (♭ as) (♭ bs) (♭ⁿ n) n✓ 
    (lookup₁ as bs n n✓) (iso as) (iso bs) (isoⁿ n)

-- Beta for case with ≫

lookup♭-case-≫ : ∀ {A} {a : A} cs ds n₁ n₂ .n✓₁ .n✓₂ → (n₂ ≡ n₁) →
  lookup♭-case {A} {a} cs ds (length♭ cs +♭ n₂) n✓₂ ≡ inj₂ (♯ⁿ n₁ , n✓₁)
lookup♭-case-≫ []♭       ds n .n n✓₁ n✓₂ refl = refl
lookup♭-case-≫ (c ∷♭ cs) ds n .n n✓₁ n✓₂ refl = cong (_⋙_ [ c ]) (lookup♭-case-≫ cs ds n n n✓₁ n✓₂ refl)
  
lookup-case-≫ : ∀ {A} {a : A} {as bs m l+m} cs ds n .m✓₁ .m✓₂ cs≡as ds≡bs l+n≡l+m → (♯ⁿ n ≡ m) → 
    lookup-case {A} {a} {as} {bs} {l+m} cs ds (♭ⁿ (length as + m)) m✓₂ cs≡as ds≡bs l+n≡l+m
      ≡ inj₂ (m , m✓₁)
lookup-case-≫ cs ds n m✓₁ m✓₂ refl refl refl refl = 
  lookup♭-case-≫ cs ds n (n +♭ 0) m✓₁ m✓₂ (isoⁿ⁻¹ n)

case-≫ : ∀ {A a} as {bs} (a∈bs : a ∈ bs) → (case {A} {a} as bs (as ≫ a∈bs) ≡ inj₂ a∈bs)
case-≫ {A} {a} as {bs} (n , n✓) =
  lookup-case-≫ {A} {a} {as} {bs} {n} {length as + n} (♭ as) (♭ bs) (♭ⁿ n) n✓ 
    (lookup₂ as bs n n✓) (iso as) (iso bs) (isoⁿ (length as + n)) (isoⁿ n)

-- A variant of case which remembers its argument

data Case+ {A} {a} (as bs : List A) : (a ∈ (as ++ bs)) → Set where
  inj₁ : (a∈as : a ∈ as) → Case+ as bs (a∈as ≪ bs)
  inj₂ : (a∈bs : a ∈ bs) → Case+ as bs (as ≫ a∈bs)

_⋙+_ : ∀ {A a} as {bs cs} {a∈bs++cs} →
  Case+ {A} {a} bs cs a∈bs++cs → Case+ (as ++ bs) cs (as ≫ a∈bs++cs)
as ⋙+ inj₁ a∈bs = inj₁ (as ≫ a∈bs)
as ⋙+ inj₂ a∈cs = inj₂ a∈cs

lookup♭-case+ : ∀ {A a} cs ds n .n✓ → (Case+ {A} {a} (♯ cs) (♯ ds) (♯ⁿ n , n✓))
lookup♭-case+ []♭       ds n       n✓ = inj₂ (♯ⁿ n , n✓)
lookup♭-case+ (c ∷♭ cs) ds zero    n✓ = inj₁ (♯0 , n✓)
lookup♭-case+ (c ∷♭ cs) ds (suc n) n✓ = [ c ] ⋙+ lookup♭-case+ cs ds n n✓

lookup-case+ : ∀ {A a as bs m} cs ds n .m✓ → (♯ cs ≡ as) → (♯ ds ≡ bs) → (♯ⁿ n ≡ m) →
  Case+ {A} {a} as bs (m , m✓)
lookup-case+ cs ds n n✓ refl refl refl = lookup♭-case+ cs ds n n✓

case+ : ∀ {A a} as bs a∈as++bs → Case+ {A} {a} as bs a∈as++bs
case+ {A} {a} as bs (n , n✓) = 
  lookup-case+ {A} {a} {as} {bs} {n} (♭ as) (♭ bs) (♭ⁿ n) n✓ (iso as) (iso bs) (isoⁿ n)

-- Inverse of case

case⁻¹ : ∀ {A a as bs} → Case {A} a as bs → (a ∈ (as ++ bs))
case⁻¹ {A} {a} {as} {bs} (inj₁ a∈as) = (a∈as ≪ bs)
case⁻¹ {A} {a} {as} {bs} (inj₂ a∈bs) = (as ≫ a∈bs)

case-iso : ∀ {A a} as bs (a∈as++bs : a ∈ (as ++ bs)) → 
  case⁻¹ (case {A} {a} as bs a∈as++bs) ≡ a∈as++bs
case-iso as bs a∈as++bs     with case+ as bs a∈as++bs
case-iso as bs .(a∈as ≪ bs) | inj₁ a∈as = cong case⁻¹ (case-≪ a∈as bs)
case-iso as bs .(as ≫ a∈bs) | inj₂ a∈bs = cong case⁻¹ (case-≫ as a∈bs)

case-iso⁻¹ : ∀ {A a} as bs (a∈as++bs : Case a as bs) → 
  case {A} {a} as bs (case⁻¹ a∈as++bs) ≡ a∈as++bs
case-iso⁻¹ as bs (inj₁ a∈as) = case-≪ a∈as bs
case-iso⁻¹ as bs (inj₂ a∈bs) = case-≫ as a∈bs

-- ⋙ distributes through case

case-⋙ : ∀ {A} {a : A} as bs cs (a∈bs++cs : a ∈ (bs ++ cs)) →
  (as ⋙ case bs cs a∈bs++cs) ≡ (case (as ++ bs) cs (as ≫ a∈bs++cs))
case-⋙ as bs cs a∈bs++cs with case+ bs cs a∈bs++cs 
case-⋙ as bs cs .(a∈bs ≪ cs) | inj₁ a∈bs =
  begin
    as ⋙ case bs cs (a∈bs ≪ cs)
  ≡⟨ cong (_⋙_ as) (case-≪ a∈bs cs) ⟩
    inj₁ (as ≫ a∈bs)
  ≡⟨ sym (case-≪ (as ≫ a∈bs) cs) ⟩
    case (as ++ bs) cs (as ≫ a∈bs ≪ cs)
  ∎
case-⋙ as bs cs .(bs ≫ a∈cs) | inj₂ a∈cs =
  begin
    as ⋙ case bs cs (bs ≫ a∈cs)
  ≡⟨ cong (_⋙_ as) (case-≫ bs a∈cs) ⟩
    inj₂ a∈cs
  ≡⟨ sym (case-≫ (as ++ bs) a∈cs) ⟩
    case (as ++ bs) cs (as ≫ bs ≫ a∈cs)
  ∎

-- Three-way case, used for proving associativity properties

data Case₃ {A} (a : A) as bs cs : Set where
  inj₁ : (a ∈ as) → Case₃ a as bs cs
  inj₂ : (a ∈ bs) → Case₃ a as bs cs
  inj₃ : (a ∈ cs) → Case₃ a as bs cs

case₂₃ : ∀ {A} {a : A} as bs cs → (Case a bs cs) → (Case₃ a as bs cs)
case₂₃ as bs cs (inj₁ a∈bs) = inj₂ a∈bs
case₂₃ as bs cs (inj₂ a∈cs) = inj₃ a∈cs

case₁₃ : ∀ {A} {a : A} as bs cs → (Case a as (bs ++ cs)) → (Case₃ a as bs cs)
case₁₃ as bs cs (inj₁ a∈as)     = inj₁ a∈as
case₁₃ as bs cs (inj₂ a∈bs++cs) = case₂₃ as bs cs (case bs cs a∈bs++cs)

case₃ : ∀ {A} {a : A} as bs cs → (a ∈ (as ++ bs ++ cs)) → (Case₃ a as bs cs)
case₃ as bs cs a∈as++bs++cs = case₁₃ as bs cs (case as (bs ++ cs) a∈as++bs++cs)

-- Associating case₃ to the left gives case

caseˡ : ∀ {A} {a : A} {as bs cs} → Case₃ a as bs cs → Case a (as ++ bs) cs
caseˡ {bs = bs} (inj₁ a∈as) = inj₁ (a∈as ≪ bs)
caseˡ {as = as} (inj₂ a∈bs) = inj₁ (as ≫ a∈bs)
caseˡ           (inj₃ a∈cs) = inj₂ a∈cs

caseˡ₂₃ : ∀ {A a} as bs cs {a∈bs++cs} → Case+ {A} {a} bs cs a∈bs++cs →
  caseˡ (case₂₃ as bs cs (case bs cs a∈bs++cs)) ≡ case (as ++ bs) cs (as ≫ a∈bs++cs)
caseˡ₂₃ as bs cs (inj₁ a∈bs) = 
  begin
    caseˡ (case₂₃ as bs cs (case bs cs (a∈bs ≪ cs)))
  ≡⟨ cong (caseˡ ∘ case₂₃ as bs cs) (case-≪ a∈bs cs) ⟩
    inj₁ (as ≫ a∈bs)
  ≡⟨ sym (case-≪ (as ≫ a∈bs) cs) ⟩
    case (as ++ bs) cs (as ≫ a∈bs ≪ cs)
  ∎
caseˡ₂₃ as bs cs (inj₂ a∈cs) =
  begin
    caseˡ (case₂₃ as bs cs (case bs cs (bs ≫ a∈cs)))
  ≡⟨ cong (caseˡ ∘ case₂₃ as bs cs) (case-≫ bs a∈cs) ⟩
    inj₂ a∈cs
  ≡⟨ sym (case-≫ (as ++ bs) a∈cs) ⟩
    case (as ++ bs) cs (as ≫ bs ≫ a∈cs)
  ∎

caseˡ₁₃ : ∀ {A a} as bs cs {a∈as++bs++cs} → Case+ {A} {a} as (bs ++ cs) a∈as++bs++cs →
  caseˡ (case₁₃ as bs cs (case as (bs ++ cs) a∈as++bs++cs)) ≡ case (as ++ bs) cs a∈as++bs++cs
caseˡ₁₃ as bs cs (inj₁ a∈as) =
  begin
    caseˡ (case₁₃ as bs cs (case as (bs ++ cs) (a∈as ≪ bs ≪ cs)))
  ≡⟨ cong (caseˡ ∘ case₁₃ as bs cs) (case-≪ a∈as (bs ++ cs)) ⟩
    inj₁ (a∈as ≪ bs)
  ≡⟨ sym (case-≪ (a∈as ≪ bs) cs) ⟩
    case (as ++ bs) cs (a∈as ≪ bs ≪ cs)
  ∎
caseˡ₁₃ as bs cs (inj₂ a∈bs++cs) =
  begin
    caseˡ (case₁₃ as bs cs (case as (bs ++ cs) (as ≫ a∈bs++cs)))
  ≡⟨ cong (caseˡ ∘ case₁₃ as bs cs) (case-≫ as a∈bs++cs) ⟩
    caseˡ (case₂₃ as bs cs (case bs cs a∈bs++cs))
  ≡⟨ caseˡ₂₃ as bs cs (case+ bs cs a∈bs++cs) ⟩
    case (as ++ bs) cs (as ≫ a∈bs++cs)
  ∎

caseˡ₃ : ∀ {A} {a : A} as bs cs (a∈as++bs++cs : a ∈ (as ++ bs ++ cs)) →
  caseˡ (case₃ as bs cs a∈as++bs++cs) ≡ case (as ++ bs) cs a∈as++bs++cs
caseˡ₃ as bs cs a∈as++bs++cs = caseˡ₁₃ as bs cs (case+ as (bs ++ cs) a∈as++bs++cs)

-- Associating case₃ to the right gives case

caseʳ : ∀ {A} {a : A} {as bs cs} → Case₃ a as bs cs → Case a as (bs ++ cs)
caseʳ           (inj₁ a∈as) = inj₁ a∈as
caseʳ {cs = cs} (inj₂ a∈bs) = inj₂ (a∈bs ≪ cs)
caseʳ {bs = bs} (inj₃ a∈cs) = inj₂ (bs ≫ a∈cs)

caseʳ₂₃ : ∀ {A a} as bs cs {a∈bs++cs} → Case+ {A} {a} bs cs a∈bs++cs →
  caseʳ (case₂₃ as bs cs (case bs cs a∈bs++cs)) ≡ inj₂ a∈bs++cs
caseʳ₂₃ as bs cs (inj₁ a∈bs) = cong (caseʳ ∘ case₂₃ as bs cs) (case-≪ a∈bs cs)
caseʳ₂₃ as bs cs (inj₂ a∈cs) = cong (caseʳ ∘ case₂₃ as bs cs) (case-≫ bs a∈cs)

caseʳ₁₃ : ∀ {A a} as bs cs {a∈as++bs++cs} → Case+ {A} {a} as (bs ++ cs) a∈as++bs++cs →
  caseʳ (case₁₃ as bs cs (case as (bs ++ cs) a∈as++bs++cs)) ≡ case as (bs ++ cs) a∈as++bs++cs
caseʳ₁₃ as bs cs (inj₁ a∈as) =
  begin
    caseʳ (case₁₃ as bs cs (case as (bs ++ cs) (a∈as ≪ bs ≪ cs)))
  ≡⟨ cong (caseʳ ∘ case₁₃ as bs cs) (case-≪ a∈as (bs ++ cs)) ⟩
    inj₁ a∈as
  ≡⟨ sym (case-≪ a∈as (bs ++ cs)) ⟩
    case as (bs ++ cs) (a∈as ≪ bs ≪ cs)
  ∎
caseʳ₁₃ as bs cs (inj₂ a∈bs++cs) =
  begin
    caseʳ (case₁₃ as bs cs (case as (bs ++ cs) (as ≫ a∈bs++cs)))
  ≡⟨ cong (caseʳ ∘ case₁₃ as bs cs) (case-≫ as a∈bs++cs) ⟩
    caseʳ (case₂₃ as bs cs (case bs cs a∈bs++cs))
  ≡⟨ caseʳ₂₃ as bs cs (case+ bs cs a∈bs++cs) ⟩
    inj₂ a∈bs++cs
  ≡⟨ sym (case-≫ as a∈bs++cs) ⟩
    case as (bs ++ cs) (as ≫ a∈bs++cs)
  ∎

caseʳ₃ : ∀ {A} {a : A} as bs cs (a∈as++bs++cs : a ∈ (as ++ bs ++ cs)) →
  caseʳ (case₃ as bs cs a∈as++bs++cs) ≡ case as (bs ++ cs) a∈as++bs++cs
caseʳ₃ as bs cs a∈as++bs++cs = caseʳ₁₃ as bs cs (case+ as (bs ++ cs) a∈as++bs++cs)
