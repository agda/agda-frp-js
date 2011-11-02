open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; trans ; subst ; cong ; cong₂ ; δcong₂ ; begin_ ; _≡⟨_⟩_ ; _∎
  ; id ; _∘_ ; ≡-relevant ; Σ ; _,_ )
open import FRP.JS.List using ( List ; [] ; _∷_ ; _++_ ; _∈_ ; ∈-inj₁ ; ∈-inj₂ ; ∈-case ; zero ; suc ; length )
open import FRP.JS.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import FRP.JS.Nat using ( ℕ ; zero ; suc ; _+_ )

module FRP.JS.Model.Seq where

infixr 4 _⊕_ _,_
infixl 3 _≪_
infixr 2 _≫_

cat : ∀ {A : Set} → List A → List A → List A
cat = _++_

cat-assoc : ∀ {A} (as bs : List A) → (cat (cat as bs) ≡ ((cat as) ∘ (cat bs)))
cat-assoc []       bs = refl
cat-assoc (a ∷ as) bs = cong (_∘_ (_∷_ a)) (cat-assoc as bs)

cat-unit : ∀ {A} (as : List A) → cat as [] ≡ as
cat-unit []       = refl
cat-unit (a ∷ as) = cong (_∷_ a) (cat-unit as)

-- Seq A is isomorphic to List A, but has associativity of concatenation
-- up to beta reduction, not just up to propositional equality.

record Seq (A : Set) : Set where
  constructor _,_
  field
    f : List A → List A
    .f✓ : f ≡ cat (f [])

open Seq public using () renaming ( f to fun ; f✓ to fun✓ )

-- Convert any list into a Seq and back

♯ : ∀ {A} → List A → Seq A
♯ as = (cat as , cong cat (sym (cat-unit as)))

♭ : ∀ {A} → Seq A → List A
♭ (f , f✓) = f []

-- Empty list

∅ : ∀ {A} → Seq A
∅ = (id , refl)

-- Singleton

⟨_⟩ : ∀ {A} → A → Seq A
⟨ a ⟩ = (_∷_ a , refl)

-- Concatenation

_⊕_ : ∀ {A} → Seq A → Seq A → Seq A
(f , f✓) ⊕ (g , g✓) = 
  ( (f ∘ g) 
  , trans (cong₂ _∘_ f✓ g✓) 
      (trans (sym (cat-assoc (f []) (g []))) 
        (cong (λ X → cat (X (g []))) (sym f✓))))

-- Cons

_◁_ : ∀ {A} → A → Seq A → Seq A
a ◁ (f , f✓) = ((_∷_ a) ∘ f) , (cong (_∘_ (_∷_ a)) f✓)

-- Ismorphism between Seq and List which respects ⊕

fun-inj : ∀ {A} (as bs : Seq A) → (fun as ≡ fun bs) → (as ≡ bs)
fun-inj (f , f✓) (.f , g✓) refl = refl

iso : ∀ {A} (as : Seq A) → ♯ (♭ as) ≡ as
iso as = fun-inj (♯ (♭ as)) as (sym (≡-relevant (fun✓ as))) 

iso⁻¹ : ∀ {A} (as : List A) → ♭ (♯ as) ≡ as
iso⁻¹ = cat-unit

iso-resp-⊕ : ∀ {A} (as bs : Seq A) → ♭ (as ⊕ bs) ≡ (♭ as ++ ♭ bs)
iso-resp-⊕ (f  , f✓) (g , g✓) = cong (λ X → X (g [])) (≡-relevant f✓)

iso-resp-⊕² : ∀ {A} (as bs cs : Seq A) → ♭ (as ⊕ bs ⊕ cs) ≡ (♭ as ++ ♭ bs ++ ♭ cs)
iso-resp-⊕² as bs cs = trans (iso-resp-⊕ as (bs ⊕ cs)) (cong (_++_ (♭ as)) (iso-resp-⊕ bs cs))

-- Case analysis

data Case {A : Set} : Seq A → Set where
  [] : Case ∅
  _∷_ : ∀ a as → Case (a ◁ as)

case′ : ∀ {A} {as : Seq A} bs → (♯ bs ≡ as) → Case as
case′ []       refl = []
case′ (b ∷ bs) refl = b ∷ ♯ bs

case : ∀ {A} (as : Seq A) → Case as
case as = case′ (♭ as) (iso as)

-- Associtivity and units are true up to beta-reduction

⊕-assoc : ∀ {A} (as bs cs : Seq A) → ((as ⊕ bs) ⊕ cs) ≡ (as ⊕ (bs ⊕ cs))
⊕-assoc as bs cs = refl

⊕-unit₁ : ∀ {A} (as : Seq A) → ((∅ ⊕ as) ≡ as)
⊕-unit₁ as = refl

⊕-unit₂ : ∀ {A} (as : Seq A) → ((as ⊕ ∅) ≡ as)
⊕-unit₂ as = refl

-- Sequence membership. We do the same trick, to get associativity
-- properties for ≪ and ≫.

ext′ : ∀ {A} {a : A} {as bs cs} ds es fs → 
  (♯ ds ≡ as) → (♯ es ≡ bs) → (♯ fs ≡ cs) → (a ∈ es) → (a ∈ ♭ (as ⊕ bs ⊕ cs))
ext′ ds es fs refl refl refl a∈es = ∈-inj₂ ds (∈-inj₁ a∈es (fs ++ []))

ext : ∀ {A} {a : A} as bs cs → (a ∈ ♭ bs) → (a ∈ ♭ (as ⊕ bs ⊕ cs))
ext {A} {a} as bs cs a∈bs = ext′ (♭ as) (♭ bs) (♭ cs) (iso as) (iso bs) (iso cs) a∈bs

record _∋_ {A} (bs : Seq A) (a : A) : Set where
  constructor _,_
  field
    f : ∀ as cs → (a ∈ ♭ (as ⊕ bs ⊕ cs))
    .f✓ : ∀ as cs → f as cs ≡ ext as bs cs (f ∅ ∅)

-- Extension on the left and right.
-- as∋a ≪ bs : (as ⊕ bs) ∋ a
-- as ≫ bs∋b : (as ⊕ bs) ∋ b
-- Requires some hoop-jumping to show that ext is associative.

index : ∀ {A} {a : A} {as} → (a ∈ as) → ℕ
index zero    = zero
index (suc x) = suc (index x)

suc-inj : ∀ {m n} → ((1 + m) ≡ (1 + n)) → (m ≡ n)
suc-inj refl = refl

+-assoc : ∀ l m n → ((l + m) + n) ≡ (l + (m + n))
+-assoc zero    m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

index-inj : ∀ {A} {a : A} {as} (p q : a ∈ as) → (index p ≡ index q) → (p ≡ q)
index-inj zero    zero    refl = refl
index-inj (suc x) (suc y) p≡q  = cong suc (index-inj x y (suc-inj p≡q))
index-inj zero    (suc y) ()
index-inj (suc y) zero    ()

size : ∀ {A} → Seq A → ℕ
size as = length (♭ as)

length-+ : ∀ {A : Set} (as bs : List A) → (length (as ++ bs) ≡ (length as + length bs))
length-+ []       bs = refl
length-+ (a ∷ as) bs = cong suc (length-+ as bs)

size-⊕ : ∀ {A} (as bs : Seq A) → (size (as ⊕ bs) ≡ (size as + size bs))
size-⊕ as bs =
  begin
    length (♭ (as ⊕ bs))
  ≡⟨ cong length (iso-resp-⊕ as bs) ⟩
    length (♭ as ++ ♭ bs)
  ≡⟨ length-+ (♭ as) (♭ bs) ⟩
    length (♭ as) + length (♭ bs)
  ∎

index-inj₁ : ∀ {A : Set} {a : A} {as} (a∈as : a ∈ as) bs →
  index (∈-inj₁ a∈as bs) ≡ index a∈as
index-inj₁ zero    bs = refl
index-inj₁ (suc x) bs = cong suc (index-inj₁ x bs)

index-inj₂ : ∀ {A : Set} {a : A} as {bs} (a∈bs : a ∈ bs) →
  index (∈-inj₂ as a∈bs) ≡ (length as + index a∈bs)
index-inj₂ []       a∈bs = refl
index-inj₂ (a ∷ as) a∈bs = cong suc (index-inj₂ as a∈bs)

index-ext′ : ∀ {A} {a : A} {as bs cs} ds es fs 
  (ds≡as : ♯ ds ≡ as) (es≡bs : ♯ es ≡ bs) (fs≡cs : ♯ fs ≡ cs) (a∈es : a ∈ es) →
    index (ext′ ds es fs ds≡as es≡bs fs≡cs a∈es) ≡ (size as + index a∈es)
index-ext′ ds es fs refl refl refl a∈es =
  begin
    index (∈-inj₂ ds (∈-inj₁ a∈es (fs ++ [])))
  ≡⟨ index-inj₂ ds (∈-inj₁ a∈es (fs ++ [])) ⟩
    length ds + index (∈-inj₁ a∈es (fs ++ []))
  ≡⟨ cong₂ _+_ (cong length (sym (cat-unit ds))) (index-inj₁ a∈es (fs ++ [])) ⟩
    length (ds ++ []) + index a∈es
  ∎

index-ext : ∀ {A} {a : A} as bs cs (a∈bs : a ∈ ♭ bs) →
  index (ext as bs cs a∈bs) ≡ (size as + index a∈bs)
index-ext as bs cs a∈bs = index-ext′ (♭ as) (♭ bs) (♭ cs) (iso as) (iso bs) (iso cs) a∈bs

ext-ext : ∀ {A} {a : A} as bs cs ds es (a∈cs : a ∈ ♭ cs) →
  ext (as ⊕ bs) cs (ds ⊕ es) a∈cs
    ≡ ext as (bs ⊕ cs ⊕ ds) es (ext bs cs ds a∈cs) 
ext-ext as bs cs ds es a∈cs = 
  index-inj 
    (ext (as ⊕ bs) cs (ds ⊕ es) a∈cs) 
    (ext as (bs ⊕ cs ⊕ ds) es (ext bs cs ds a∈cs))
    (begin
      index (ext (as ⊕ bs) cs (ds ⊕ es) a∈cs)
    ≡⟨ index-ext (as ⊕ bs) cs (ds ⊕ es) a∈cs ⟩
      size (as ⊕ bs) + index a∈cs
    ≡⟨ cong (λ X → X + index a∈cs) (size-⊕ as bs) ⟩
      (size as + size bs) + index a∈cs
    ≡⟨ +-assoc (size as) (size bs) (index a∈cs) ⟩
      size as + (size bs + index a∈cs)
    ≡⟨ cong (_+_ (size as)) (sym (index-ext bs cs ds a∈cs)) ⟩
      size as + index (ext bs cs ds a∈cs)
    ≡⟨ sym (index-ext as (bs ⊕ cs ⊕ ds) es (ext bs cs ds a∈cs)) ⟩
      index (ext as (bs ⊕ cs ⊕ ds) es (ext bs cs ds a∈cs))
    ∎)

_≪_ : ∀ {A} {a : A} {bs} → (bs ∋ a) → ∀ cs → ((bs ⊕ cs) ∋ a)
_≪_ {A} {a} {bs} (f , f✓) cs = 
  ( (λ as ds → f as (cs ⊕ ds))
  , (λ as ds → trans (f✓ as (cs ⊕ ds)) 
      (trans (ext-ext as ∅ bs cs ds (f ∅ ∅)) 
        (cong (ext as (bs ⊕ cs) ds) (sym (f✓ ∅ cs))))))

_≫_ : ∀ {A} {a : A} bs {cs} → (cs ∋ a) → ((bs ⊕ cs) ∋ a)
_≫_ {A} {a} bs {cs} (f , f✓) = 
  ( (λ as ds → f (as ⊕ bs) ds)
  , (λ as ds → trans (f✓ (as ⊕ bs) ds)
      (trans (ext-ext as bs cs ∅ ds (f ∅ ∅)) 
        (cong (ext as (bs ⊕ cs) ds) (sym (f✓ bs ∅))))) )

-- Membership respects ♯ and ♭.

∈♭ : ∀ {A} {a : A} bs → (a ∈ ♭ bs) → (bs ∋ a)
∈♭ bs a∈bs = ((λ as cs → ext as bs cs a∈bs) , (λ as cs → ext-ext as ∅ bs ∅ cs a∈bs))

∈♯ : ∀ {A} {a : A} bs → (a ∈ bs) → (♯ bs ∋ a)
∈♯ bs a∈bs = ∈♭ (♯ bs) (subst (_∈_ _) (sym (cat-unit bs)) a∈bs)

∋♭ : ∀ {A} {a : A} bs → (bs ∋ a) → (a ∈ ♭ bs)
∋♭ bs (f , f✓) = f ∅ ∅

∋♯ : ∀ {A} {a : A} bs → (♯ bs ∋ a) → (a ∈ bs)
∋♯ bs (f , f✓) = subst (_∈_ _) (cat-unit bs) (f ∅ ∅)

-- (as ⊕ bs) ∋ a  iff  as ∋ a  or  bs ∋ a


∋-case′ : ∀ {A} {a : A} {as bs} cs ds → (♯ cs ≡ as) → (♯ ds ≡ bs) → 
  (a ∈ ♭ (as ⊕ bs)) → ((as ∋ a) ⊎ (bs ∋ a))
∋-case′ cs ds refl refl a∈as⊕bs
  with ∈-case cs (ds ++ []) a∈as⊕bs
... | inj₁ a∈cs = inj₁ (∈♯ cs a∈cs)
... | inj₂ a∈ds = inj₂ (∈♭ (♯ ds) a∈ds)

∋-case : ∀ {A} {a : A} as bs → ((as ⊕ bs) ∋ a) → ((as ∋ a) ⊎ (bs ∋ a))
∋-case as bs as⊕bs∋a = ∋-case′ (♭ as) (♭ bs) (iso as) (iso bs) (∋♭ (as ⊕ bs) as⊕bs∋a)

∋-case₁ : ∀ {A} {a : A} {as} (as∋a : as ∋ a) bs →
  ∋-case as bs (as∋a ≪ bs) ≡ inj₁ as∋a
∋-case₁ {A} {a} {as} (f , f✓) bs = {!∋♭ (as ⊕ bs) (as∋a ≪ bs)!}

-- ∋-case {A} {a} as bs (# x) with ∈-case (♭ as) (♭ bs) (subst (_∈_ a) (iso-resp-⊕ as bs) x)
-- ∋-case {A} {a} as bs (# x) | inj₁ y = inj₁ (# y)
-- ∋-case {A} {a} as bs (# x) | inj₂ y = inj₂ (# y)

≪-assoc : ∀ {A} {a : A} {as} (x : as ∋ a) bs cs → (x ≪ bs ≪ cs) ≡ (x ≪ bs ⊕ cs)
≪-assoc x bs cs = refl

≫-assoc : ∀ {A} {a : A} {cs} as bs (x : cs ∋ a)  → (as ⊕ bs ≫ x) ≡ (as ≫ bs ≫ x)
≫-assoc as bs x = refl

≫-≪-assoc : ∀ {A} {a : A} as {bs} (x : bs ∋ a) cs → ((as ≫ x) ≪ cs) ≡ (as ≫ (x ≪ cs))
≫-≪-assoc as x cs = refl

-- (b ◁ bs) ∋ b

_◂_ : ∀ {A} (b : A) bs → ((b ◁ bs) ∋ b)
b ◂ bs = ((λ as cs → ext as (b ◁ bs) cs zero) , (λ as cs → ext-ext as ∅ (b ◁ bs) ∅ cs zero))

-- ⟨ a ⟩ ∋ b implies a ≡ b

∋-uniq : ∀ {A} (a b : A) → (⟨ a ⟩ ∋ b) → (a ≡ b)
∋-uniq a b  (f , f✓) with f ∅ ∅
∋-uniq a .a (f , f✓) | zero = refl
∋-uniq a b  (f , f✓) | suc ()

