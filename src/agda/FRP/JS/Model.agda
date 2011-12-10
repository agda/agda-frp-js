open import FRP.JS.Level using ( Level ; _⊔_ ) renaming ( zero to o ; suc to ↑ )
open import FRP.JS.Time using ( Time ; _≤_ ; _<_ )
open import FRP.JS.Bool using ( Bool ; true ; false ; not ; _≟_ ) 
open import FRP.JS.True using ( True ; tt )

module FRP.JS.Model where

-- This model is essentially System F-omega with a kind time
-- together with a type for the partial order on time,
-- and expressions for reflexivity and transitivity.
-- We prove parametricity, and then show that parametricity implies causality.

-- Note that this is a "deep" notion of causality, not the "shallow"
-- causality usually used in FRP. The pragmatic upshot of this is that
-- there is only one time model: nested signals are in the same time
-- model, not a simulated time model. This fits with the JS implementation,
-- which uses wall clock time for all signals.

-- Propositional equality

data _≡_ {α} {A : Set α} (a : A) : A → Set α where
  refl : a ≡ a

sym : ∀ {α} {A : Set α} {a b : A} → (a ≡ b) → (b ≡ a)
sym refl = refl

trans : ∀ {α} {A : Set α} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
trans refl refl = refl

cong : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) {a₁ a₂ : A} →
  (a₁ ≡ a₂) → (f a₁ ≡ f a₂)
cong f refl = refl

apply : ∀ {α β} {A : Set α} {B : Set β} {F G : A → B} → (F ≡ G) → 
  ∀ {a b} → (a ≡ b) → (F a ≡ G b)
apply refl refl = refl

cast : ∀ {α} {A B : Set α} → (A ≡ B) → A → B
cast refl a = a

cast² : ∀ {α} {A B : Set α} {ℜ ℑ : A → B → Set α} → (ℜ ≡ ℑ) → ∀ {a b} → ℜ a b → ℑ a b
cast² refl aℜb = aℜb

irrel : ∀ b → (b₁ b₂ : True b) → (b₁ ≡ b₂)
irrel true  tt tt = refl
irrel false () ()

-- Postulates (including dependent extensionality)

postulate
  ≤-refl : ∀ t → True (t ≤ t)
  ≤-trans : ∀ t u v → True (t ≤ u) → True (u ≤ v) → True (t ≤ v)
  dext : ∀ {α β} {A : Set α} {B : A → Set β} {F G : ∀ a → B a} → (∀ a → F a ≡ G a) → (F ≡ G)

ext : ∀ {α β} {A : Set α} {B : Set β} {F G : A → B} →
  (∀ a → F a ≡ G a) → (F ≡ G)
ext = dext

iext : ∀ {α β} {A : Set α} {B : A → Set β} {F G : ∀ {a} → B a} → 
  (∀ a → F {a} ≡ G {a}) → ((λ {a} → F {a}) ≡ (λ {a} → G {a}))
iext F≈G = cong (λ X {a} → X a) (dext F≈G)

-- Finite products

record ⊤ {α} : Set α where
  constructor tt

open ⊤ public

record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A × B = Σ A (λ a → B)

_×²_ : ∀ {α β} {A C : Set α} {B D : Set β} → 
  (A → C → Set α) → (B → D → Set β) → ((A × B) → (C × D) → Set (α ⊔ β))
(ℜ ×² ℑ) (a , b) (c , d) = (ℜ a c × ℑ b d)

_→²_ : ∀ {α β} {A C : Set α} {B D : Set β} → 
  (A → C → Set α) → (B → D → Set β) → ((A → B) → (C → D) → Set (α ⊔ β))
(ℜ →² ℑ) f g = ∀ {a b} → ℜ a b → ℑ (f a) (g b)

-- Case on booleans

data Case (c : Bool) : Set where
  _,_ : ∀ b → True (b ≟ c) → Case c

switch : ∀ b → Case b
switch true  = (true , tt)
switch false = (false , tt)

-- Reactive sets

RSet : ∀ α → Set (↑ α)
RSet α = Time → Set α

-- Equalitional reasoning

infix  4 _IsRelatedTo_
infix  2 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_

data _IsRelatedTo_ {α} {A : Set α} (a b : A) : Set α where
  relTo : (a≡b : a ≡ b) → a IsRelatedTo b

begin_ : ∀ {α} {A : Set α} {a b : A} → a IsRelatedTo b → a ≡ b
begin relTo a≡b = a≡b

_≡⟨_⟩_ : ∀ {α} {A : Set α} a {b c : A} → a ≡ b → b IsRelatedTo c → a IsRelatedTo c
_ ≡⟨ a≡b ⟩ relTo b≡c = relTo (trans a≡b b≡c)

_∎ : ∀ {α} {A : Set α} (a : A) → a IsRelatedTo a
_∎ _ = relTo refl

-- Kinds

data Kind : Set where
  time : Kind
  set : Level → Kind
  _⇒_ : Kind → Kind → Kind

level : Kind → Level
level time    = o
level (set α) = ↑ α
level (K ⇒ L) = level K ⊔ level L

K⟦_⟧ : ∀ K → Set (level K)
K⟦ time ⟧  = Time
K⟦ set α ⟧ = Set α
K⟦ K ⇒ L ⟧ = K⟦ K ⟧ → K⟦ L ⟧

_∋_↔_ : ∀ K → K⟦ K ⟧ → K⟦ K ⟧ → Set (level K)
time    ∋ t ↔ u = (t ≡ u)
set α   ∋ A ↔ B = A → B → Set α
(K ⇒ L) ∋ F ↔ G = ∀ {A B} → (K ∋ A ↔ B) → (L ∋ F A ↔ G B)

-- ≡ can be used as a structural equivalence on relations.

struct : ∀ K {A B C D} → (A ≡ B) → (K ∋ B ↔ D) → (C ≡ D) → (K ∋ A ↔ C)
struct K refl ℜ refl = ℜ

struct-ext : ∀ K L {A B} {F G H I : K⟦ K ⇒ L ⟧} 
  (F≈G : ∀ A → F A ≡ G A) (ℜ : (K ⇒ L) ∋ G ↔ I) (H≈I : ∀ B → H B ≡ I B) (ℑ : K ∋ A ↔ B) →
    struct L (F≈G A) (ℜ ℑ) (H≈I B) ≡ struct (K ⇒ L) (ext F≈G) ℜ (ext H≈I) ℑ
struct-ext K L {A} {B} F≈G ℜ H≈I ℑ 
 with ext F≈G | ext H≈I | F≈G A | H≈I B
... | refl    | refl    | refl  | refl = refl

struct-apply : ∀ K L {F G H I A B C D} → 
  (F≡G : F ≡ G) (ℜ : (K ⇒ L) ∋ G ↔ I) (H≡I : H ≡ I) → 
  (A≡B : A ≡ B) (ℑ : K ∋ B ↔ D) (C≡D : C ≡ D) → 
    struct (K ⇒ L) F≡G ℜ H≡I (struct K A≡B ℑ C≡D)
      ≡ struct L (apply F≡G A≡B) (ℜ ℑ) (apply H≡I C≡D)
struct-apply K L refl ℜ refl refl ℑ refl = refl

struct-cast : ∀ {α A B C D} (ℜ : set α ∋ B ↔ D) (A≡B : A ≡ B) (C≡D : C ≡ D) {a c} →
  struct (set α) A≡B ℜ C≡D a c → ℜ (cast A≡B a) (cast C≡D c)
struct-cast ℜ refl refl aℜc = aℜc

struct-sym : ∀ K {A B C D ℑ ℜ} → (A≡B : A ≡ B) → (C≡D : C ≡ D) →
  (ℑ ≡ struct K A≡B ℜ C≡D) → 
    (ℜ ≡ struct K (sym A≡B) ℑ (sym C≡D))
struct-sym K refl refl refl = refl

struct-trans : ∀ K {A B C D E F}
  (A≡B : A ≡ B) (B≡C : B ≡ C) (ℜ : K ∋ C ↔ F) (E≡F : E ≡ F) (D≡E : D ≡ E) →
    struct K A≡B (struct K B≡C ℜ E≡F) D≡E ≡
      struct K (trans A≡B B≡C) ℜ (trans D≡E E≡F)
struct-trans K refl refl ℜ refl refl = refl

-- Type contexts

infixr 4 _∷_

data Kinds : Set where
  [] : Kinds
  _∷_ : Kind → Kinds → Kinds

levels : Kinds → Level
levels []      = o
levels (K ∷ Σ) = level K ⊔ levels Σ

Σ⟦_⟧ : ∀ Σ → Set (levels Σ)
Σ⟦ [] ⟧    = ⊤
Σ⟦ K ∷ Σ ⟧ = K⟦ K ⟧ × Σ⟦ Σ ⟧

_∋_↔*_ : ∀ Σ → Σ⟦ Σ ⟧ → Σ⟦ Σ ⟧ → Set (levels Σ)
[]      ∋ tt       ↔* tt       = ⊤
(K ∷ Σ) ∋ (A , As) ↔* (B , Bs) = (K ∋ A ↔ B) × (Σ ∋ As ↔* Bs)

-- Inclusion order on type contexts.
-- Credited by Randy Pollack to Geuvers and Nederhof, JAR 1991.
-- http://thread.gmane.org/gmane.comp.lang.agda/3259/focus=3267

data _⊑_ : Kinds → Kinds → Set where
  id : ∀ {Σ} → Σ ⊑ Σ
  keep : ∀ K {Σ Υ} → (Σ ⊑ Υ) → ((K ∷ Σ) ⊑ (K ∷ Υ))
  skip : ∀ K {Σ Υ} → (Σ ⊑ Υ) → (Σ ⊑ (K ∷ Υ))

⊑⟦_⟧ : ∀ {Σ Υ} → (Σ ⊑ Υ) → Σ⟦ Υ ⟧ → Σ⟦ Σ ⟧
⊑⟦ id ⟧         As       = As
⊑⟦ keep K Σ⊑Υ ⟧ (A , As) = (A , ⊑⟦ Σ⊑Υ ⟧ As)
⊑⟦ skip K Σ⊑Υ ⟧ (A , As) = ⊑⟦ Σ⊑Υ ⟧ As

⊑⟦_⟧² : ∀ {Σ Υ} → (Σ⊑Υ : Σ ⊑ Υ) → ∀ {As Bs} → (Υ ∋ As ↔* Bs) → (Σ ∋ ⊑⟦ Σ⊑Υ ⟧ As ↔* ⊑⟦ Σ⊑Υ ⟧ Bs)
⊑⟦ id ⟧²         ℜs       = ℜs
⊑⟦ keep K Σ⊑Υ ⟧² (ℜ , ℜs) = (ℜ , ⊑⟦ Σ⊑Υ ⟧² ℜs)
⊑⟦ skip K Σ⊑Υ ⟧² (ℜ , ℜs) = ⊑⟦ Σ⊑Υ ⟧² ℜs

-- Concatenation of type contexts

_++_ : Kinds → Kinds → Kinds
[]      ++ Υ = Υ
(K ∷ Σ) ++ Υ = K ∷ (Σ ++ Υ)

_∋_++_∋_ : ∀ Σ → Σ⟦ Σ ⟧ → ∀ Υ → Σ⟦ Υ ⟧ → Σ⟦ Σ ++ Υ ⟧
[]      ∋ tt       ++ Υ ∋ Bs = Bs
(K ∷ Σ) ∋ (A , As) ++ Υ ∋ Bs = (A , (Σ ∋ As ++ Υ ∋ Bs))

_∋_++²_∋_ : ∀ Σ {As Bs} → (Σ ∋ As ↔* Bs) → ∀ Υ {Cs Ds} → (Υ ∋ Cs ↔* Ds) → 
  ((Σ ++ Υ) ∋ (Σ ∋ As ++ Υ ∋ Cs) ↔* (Σ ∋ Bs ++ Υ ∋ Ds))
[]      ∋ tt       ++² Υ ∋ ℑs = ℑs
(K ∷ Σ) ∋ (ℜ , ℜs) ++² Υ ∋ ℑs = (ℜ , (Σ ∋ ℜs ++² Υ ∋ ℑs))

-- Type variables

data TVar (K : Kind) : Kinds → Set where
  zero : ∀ {Σ} → TVar K (K ∷ Σ)
  suc : ∀ {L Σ} → TVar K Σ → TVar K (L ∷ Σ)

τ⟦_⟧ : ∀ {Σ K} (τ : TVar K Σ) → Σ⟦ Σ ⟧ → K⟦ K ⟧
τ⟦ zero ⟧  (A , As)  = A
τ⟦ suc τ ⟧ (A , As)  = τ⟦ τ ⟧ As

τ⟦_⟧² : ∀ {Σ K} (τ : TVar K Σ) {As Bs} → (Σ ∋ As ↔* Bs) → (K ∋ τ⟦ τ ⟧ As ↔ τ⟦ τ ⟧ Bs)
τ⟦ zero ⟧²  (ℜ , ℜs)  = ℜ
τ⟦ suc τ ⟧² (ℜ , ℜs)  = τ⟦ τ ⟧² ℜs

-- Type constants

data TConst : Kind → Set where
  prod fun : ∀ {α β} → TConst (set α ⇒ (set β ⇒ set (α ⊔ β)))
  leq lt : TConst (time ⇒ (time ⇒ set o))
  univ : ∀ K {α} → TConst ((K ⇒ set α) ⇒ set (level K ⊔ α))

C⟦_⟧ : ∀ {K} → (TConst K) → K⟦ K ⟧
C⟦ prod ⟧   = λ A B → (A × B)
C⟦ fun ⟧    = λ A B → (A → B)
C⟦ leq ⟧    = λ t u → True (t ≤ u)
C⟦ lt ⟧     = λ t u → True (t < u)
C⟦ univ K ⟧ = λ F → ∀ A → F A

C⟦_⟧² : ∀ {K} (C : TConst K) → (K ∋ C⟦ C ⟧ ↔ C⟦ C ⟧)
C⟦ prod ⟧²   = λ ℜ ℑ → (ℜ ×² ℑ)
C⟦ fun ⟧²    = λ ℜ ℑ → (ℜ →² ℑ)
C⟦ leq ⟧²    = λ _ _ _ _ → ⊤
C⟦ lt ⟧²     = λ _ _ _ _ → ⊤
C⟦ univ K ⟧² = λ ℜ f g → ∀ {a b} ℑ → ℜ ℑ (f a) (g b)

-- Types

data Typ (Σ : Kinds) : Kind → Set where
  const : ∀ {K} → TConst K → Typ Σ K
  abs : ∀ K {L} → Typ (K ∷ Σ) L → Typ Σ (K ⇒ L)
  app : ∀ {K L} → Typ Σ (K ⇒ L) → Typ Σ K → Typ Σ L
  var : ∀ {K} → TVar K Σ → Typ Σ K

tlevel : ∀ {Σ α} → Typ Σ (set α) → Level
tlevel {Σ} {α} T = α

T⟦_⟧ : ∀ {Σ K} (T : Typ Σ K) → Σ⟦ Σ ⟧ → K⟦ K ⟧
T⟦ const C ⟧ As  = C⟦ C ⟧
T⟦ abs K T ⟧ As  = λ A → T⟦ T ⟧ (A , As)
T⟦ app T U ⟧ As  = T⟦ T ⟧ As (T⟦ U ⟧ As)
T⟦ var τ ⟧ As    = τ⟦ τ ⟧ As

T⟦_⟧² : ∀ {Σ K} (T : Typ Σ K) {As Bs} → (Σ ∋ As ↔* Bs) → (K ∋ T⟦ T ⟧ As ↔ T⟦ T ⟧ Bs)
T⟦ const C ⟧² ℜs  = C⟦ C ⟧²
T⟦ abs K T ⟧² ℜs  = λ ℜ → T⟦ T ⟧² (ℜ , ℜs)
T⟦ app T U ⟧² ℜs  = T⟦ T ⟧² ℜs (T⟦ U ⟧² ℜs)
T⟦ var τ ⟧² ℜs    = τ⟦ τ ⟧² ℜs

-- Type shorthands

app₂ :  ∀ {Σ K L M} → Typ Σ (K ⇒ (L ⇒ M)) → Typ Σ K → Typ Σ L → Typ Σ M
app₂ T U V = app (app T U) V

capp :  ∀ {Σ K L} → TConst (K ⇒ L) → Typ Σ K → Typ Σ L
capp C = app (const C)

capp₂ :  ∀ {Σ K L M} → TConst (K ⇒ (L ⇒ M)) → Typ Σ K → Typ Σ L → Typ Σ M
capp₂ C = app₂ (const C)

_⊗_ : ∀ {Σ α β} → Typ Σ (set α) → Typ Σ (set β) → Typ Σ (set (α ⊔ β))
_⊗_ = capp₂ prod

_⊸_ : ∀ {Σ α β} → Typ Σ (set α) → Typ Σ (set β) → Typ Σ (set (α ⊔ β))
_⊸_ = capp₂ fun

_≼_ : ∀ {Σ} → Typ Σ time → Typ Σ time → Typ Σ (set o)
_≼_ = capp₂ leq

_≺_ : ∀ {Σ} → Typ Σ time → Typ Σ time → Typ Σ (set o)
_≺_ = capp₂ lt

Π : ∀ {Σ α} K → Typ (K ∷ Σ) (set α) → Typ Σ (set (level K ⊔ α))
Π K T = capp (univ K) (abs K T)

tvar₀ : ∀ {Σ K} → Typ (K ∷ Σ) K
tvar₀ = var zero

tvar₁ : ∀ {Σ K L} → Typ (L ∷ K ∷ Σ) K
tvar₁ = var (suc zero)

tvar₂ : ∀ {Σ K L M} → Typ (M ∷ L ∷ K ∷ Σ) K
tvar₂ = var (suc (suc zero))

tvar₃ : ∀ {Σ K L M N} → Typ (N ∷ M ∷ L ∷ K ∷ Σ) K
tvar₃ = var (suc (suc (suc zero)))

rset : Level → Kind
rset α = time ⇒ set α

rset₀ : Kind
rset₀ = rset o

prodʳ : ∀ {Σ α β} → Typ Σ (rset α ⇒ (rset β ⇒ rset (α ⊔ β)))
prodʳ {Σ} {α} {β} = abs (rset α) (abs (rset β) (abs time (app tvar₂ tvar₀ ⊗ app tvar₁ tvar₀)))

_⊗ʳ_ : ∀ {Σ α β} → Typ Σ (rset α) → Typ Σ (rset β) → Typ Σ (rset (α ⊔ β))
_⊗ʳ_ = app₂ prodʳ

funʳ : ∀ {Σ α β} → Typ Σ (rset α ⇒ (rset β ⇒ rset (α ⊔ β)))
funʳ {Σ} {α} {β} = abs (rset α) (abs (rset β) (abs time (app tvar₂ tvar₀ ⊸ app tvar₁ tvar₀)))

_⊸ʳ_ : ∀ {Σ α β} → Typ Σ (rset α) → Typ Σ (rset β) → Typ Σ (rset (α ⊔ β))
_⊸ʳ_ = app₂ funʳ

always : ∀ {Σ α} → Typ Σ (set α ⇒ rset α)
always {Σ} {α} = abs (set α) (abs time tvar₁)

½interval : ∀ {Σ α} → Typ Σ (rset α ⇒ (time ⇒ (time ⇒ set α)))
½interval {Σ} {α} = abs (rset α) (abs time (abs time (Π time 
  ((tvar₂ ≺ tvar₀) ⊸ ((tvar₀ ≼ tvar₁) ⊸ app tvar₃ tvar₀)))))

_⟨_,_] : ∀ {Σ α} → Typ Σ (rset α) → Typ Σ time → Typ Σ time → Typ Σ (set α)
T ⟨ t , u ] = app (app (app ½interval T) t) u

-- Contexts

data Typs (Σ : Kinds) : Set where
  [] : Typs Σ
  _∷_ : ∀ {α} → (Typ Σ (set α)) → Typs Σ → Typs Σ

tlevels : ∀ {Σ} → Typs Σ → Level
tlevels []       = o
tlevels (T ∷ Γ) = tlevel T ⊔ tlevels Γ

Γ⟦_⟧ : ∀ {Σ} (Γ : Typs Σ) → Σ⟦ Σ ⟧ → Set (tlevels Γ)
Γ⟦ [] ⟧    As = ⊤
Γ⟦ T ∷ Γ ⟧ As = T⟦ T ⟧ As × Γ⟦ Γ ⟧ As

Γ⟦_⟧² : ∀ {Σ} (Γ : Typs Σ) {As Bs} (ℜs : Σ ∋ As ↔* Bs) → (Γ⟦ Γ ⟧ As → Γ⟦ Γ ⟧ Bs → Set (tlevels Γ))
Γ⟦ [] ⟧²    ℜs tt       tt       = ⊤
Γ⟦ T ∷ Γ ⟧² ℜs (a , as) (b , bs) = T⟦ T ⟧² ℜs a b × Γ⟦ Γ ⟧² ℜs as bs

-- Weakening of type variables

τweaken : ∀ {Σ Υ K} → (Σ ⊑ Υ) → TVar K Σ → TVar K Υ
τweaken id           x       = x
τweaken (keep K Σ⊑Υ) zero    = zero
τweaken (keep K Σ⊑Υ) (suc x) = suc (τweaken Σ⊑Υ x)
τweaken (skip K Σ⊑Υ) x       = suc (τweaken Σ⊑Υ x)

τweaken⟦_⟧ : ∀ {Σ Υ K} (τ : TVar K Σ) (Σ⊑Υ : Σ ⊑ Υ) (As : Σ⟦ Υ ⟧) → 
  τ⟦ τ ⟧ (⊑⟦ Σ⊑Υ ⟧ As) ≡ τ⟦ τweaken Σ⊑Υ τ ⟧ As
τweaken⟦ τ ⟧     id           As       = refl
τweaken⟦ zero ⟧  (keep K Σ⊑Υ) (A , As) = refl
τweaken⟦ suc τ ⟧ (keep K Σ⊑Υ) (A , As) = τweaken⟦ τ ⟧ Σ⊑Υ As
τweaken⟦ τ ⟧     (skip K Σ⊑Υ) (A , As) = τweaken⟦ τ ⟧ Σ⊑Υ As

τweaken⟦_⟧² : ∀ {Σ Υ K} (τ : TVar K Σ) (Σ⊑Υ : Σ ⊑ Υ) {As Bs} (ℜs : Υ ∋ As ↔* Bs) → 
  τ⟦ τ ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs) ≡ 
    struct K (τweaken⟦ τ ⟧ Σ⊑Υ As) (τ⟦ τweaken Σ⊑Υ τ ⟧² ℜs) (τweaken⟦ τ ⟧ Σ⊑Υ Bs)
τweaken⟦ τ ⟧²     id           ℜs       = refl
τweaken⟦ zero ⟧²  (keep K Σ⊑Υ) (ℜ , ℜs) = refl
τweaken⟦ suc τ ⟧² (keep K Σ⊑Υ) (ℜ , ℜs) = τweaken⟦ τ ⟧² Σ⊑Υ ℜs
τweaken⟦ τ ⟧²     (skip K Σ⊑Υ) (ℜ , ℜs) = τweaken⟦ τ ⟧² Σ⊑Υ ℜs

-- Weakening of types

weaken : ∀ {Σ Υ K} → (Σ ⊑ Υ) → Typ Σ K → Typ Υ K
weaken Σ⊑Υ (const C)  = const C
weaken Σ⊑Υ (abs K T)  = abs K (weaken (keep K Σ⊑Υ) T)
weaken Σ⊑Υ (app T U)  = app (weaken Σ⊑Υ T) (weaken Σ⊑Υ U)
weaken Σ⊑Υ (var τ)    = var (τweaken Σ⊑Υ τ)

weaken⟦_⟧ : ∀ {Σ Υ K} (T : Typ Σ K) (Σ⊑Υ : Σ ⊑ Υ) (As : Σ⟦ Υ ⟧) → 
  T⟦ T ⟧ (⊑⟦ Σ⊑Υ ⟧ As) ≡ T⟦ weaken Σ⊑Υ T ⟧ As
weaken⟦ const C ⟧ Σ⊑Υ As = refl
weaken⟦ abs K T ⟧ Σ⊑Υ As = ext (λ A → weaken⟦ T ⟧ (keep K Σ⊑Υ) (A , As))
weaken⟦ app T U ⟧ Σ⊑Υ As = apply (weaken⟦ T ⟧ Σ⊑Υ As) (weaken⟦ U ⟧ Σ⊑Υ As) 
weaken⟦ var τ ⟧   Σ⊑Υ As = τweaken⟦ τ ⟧ Σ⊑Υ As
  
weaken⟦_⟧² : ∀ {Σ Υ K} (T : Typ Σ K) (Σ⊑Υ : Σ ⊑ Υ) {As Bs} (ℜs : Υ ∋ As ↔* Bs) → 
  T⟦ T ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs) ≡ struct K (weaken⟦ T ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ T ⟧² ℜs) (weaken⟦ T ⟧ Σ⊑Υ Bs)
weaken⟦ const C ⟧² Σ⊑Υ ℜs = refl
weaken⟦ abs K {L} T ⟧² Σ⊑Υ {As} {Bs} ℜs =
  iext (λ A → iext (λ B → ext (λ ℜ → begin
    T⟦ abs K T ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs) ℜ
  ≡⟨ weaken⟦ T ⟧² (keep K Σ⊑Υ) (ℜ , ℜs) ⟩
    struct L 
      (weaken⟦ T ⟧ (keep K Σ⊑Υ) (A , As)) 
      (T⟦ weaken (keep K Σ⊑Υ) T ⟧² (ℜ , ℜs)) 
      (weaken⟦ T ⟧ (keep K Σ⊑Υ) (B , Bs))
  ≡⟨ struct-ext K L 
       (λ A → weaken⟦ T ⟧ (keep K Σ⊑Υ) (A , As)) 
       (λ ℜ → T⟦ weaken (keep K Σ⊑Υ) T ⟧² (ℜ , ℜs)) 
       (λ B → weaken⟦ T ⟧ (keep K Σ⊑Υ) (B , Bs)) ℜ ⟩
    struct (K ⇒ L) 
      (weaken⟦ abs K T ⟧ Σ⊑Υ As)
      (T⟦ weaken Σ⊑Υ (abs K T) ⟧² ℜs) 
      (weaken⟦ abs K T ⟧ Σ⊑Υ Bs) ℜ
  ∎)))
weaken⟦ app {K} {L} T U ⟧² Σ⊑Υ {As} {Bs} ℜs = 
  begin
    T⟦ app T U ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs)
  ≡⟨ cong (T⟦ T ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs)) (weaken⟦ U ⟧² Σ⊑Υ ℜs) ⟩
    T⟦ T ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs)
      (struct K (weaken⟦ U ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ U ⟧² ℜs) (weaken⟦ U ⟧ Σ⊑Υ Bs))
  ≡⟨ cong (λ X → X (struct K (weaken⟦ U ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ U ⟧² ℜs) (weaken⟦ U ⟧ Σ⊑Υ Bs)))
       (weaken⟦ T ⟧² Σ⊑Υ ℜs) ⟩
    (struct (K ⇒ L) (weaken⟦ T ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ T ⟧² ℜs) (weaken⟦ T ⟧ Σ⊑Υ Bs))
      (struct K (weaken⟦ U ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ U ⟧² ℜs) (weaken⟦ U ⟧ Σ⊑Υ Bs))
  ≡⟨ struct-apply K L 
       (weaken⟦ T ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ T ⟧² ℜs) (weaken⟦ T ⟧ Σ⊑Υ Bs) 
       (weaken⟦ U ⟧ Σ⊑Υ As) (T⟦ weaken Σ⊑Υ U ⟧² ℜs) (weaken⟦ U ⟧ Σ⊑Υ Bs) ⟩
    struct L
      (weaken⟦ app T U ⟧ Σ⊑Υ As)
      (T⟦ weaken Σ⊑Υ (app T U) ⟧² ℜs) 
      (weaken⟦ app T U ⟧ Σ⊑Υ Bs)
  ∎
weaken⟦ var τ ⟧² Σ⊑Υ ℜs = τweaken⟦ τ ⟧² Σ⊑Υ ℜs

-- Weakening on type contexts

weakens : ∀ {Σ Υ} → (Σ ⊑ Υ) → Typs Σ → Typs Υ
weakens Σ⊑Υ []      = []
weakens Σ⊑Υ (T ∷ Γ) = weaken Σ⊑Υ T ∷ weakens Σ⊑Υ Γ

weakens⟦_⟧ : ∀ {Σ Υ} (Γ : Typs Σ) (Σ⊑Υ : Σ ⊑ Υ) (As : Σ⟦ Υ ⟧) → 
  Γ⟦ Γ ⟧ (⊑⟦ Σ⊑Υ ⟧ As) → Γ⟦ weakens Σ⊑Υ Γ ⟧ As
weakens⟦ [] ⟧    Σ⊑Υ As tt       = tt
weakens⟦ T ∷ Γ ⟧ Σ⊑Υ As (B , Bs) = (cast (weaken⟦ T ⟧ Σ⊑Υ As) B , weakens⟦ Γ ⟧ Σ⊑Υ As Bs)

weakens⟦_⟧² : ∀ {Σ Υ} (Γ : Typs Σ) (Σ⊑Υ : Σ ⊑ Υ) {As Bs} (ℜs : Υ ∋ As ↔* Bs) {as bs} → 
  Γ⟦ Γ ⟧² (⊑⟦ Σ⊑Υ ⟧² ℜs) as bs → 
  Γ⟦ weakens Σ⊑Υ Γ ⟧² ℜs (weakens⟦ Γ ⟧ Σ⊑Υ As as) (weakens⟦ Γ ⟧ Σ⊑Υ Bs bs)
weakens⟦ [] ⟧²    Σ⊑Υ ℜs tt
  = tt
weakens⟦ T ∷ Γ ⟧² Σ⊑Υ ℜs (aℜb , asℜbs) 
  = ( struct-cast (T⟦ weaken Σ⊑Υ T ⟧² ℜs) 
        (weaken⟦ T ⟧ Σ⊑Υ _) (weaken⟦ T ⟧ Σ⊑Υ _) (cast² (weaken⟦ T ⟧² Σ⊑Υ ℜs) aℜb)
    , weakens⟦ Γ ⟧² Σ⊑Υ ℜs asℜbs)

-- Susbtitution on type variables under a context

τsubstn+ : ∀ Σ {Υ K L} → TVar K (Σ ++ (L ∷ Υ)) → Typ Υ L → Typ (Σ ++ Υ) K
τsubstn+ []      zero    U = U
τsubstn+ []      (suc τ) U = var τ
τsubstn+ (K ∷ Σ) zero    U = var zero
τsubstn+ (K ∷ Σ) (suc τ) U = weaken (skip K id) (τsubstn+ Σ τ U)

τsubstn+_⟦_⟧⟦_⟧ : ∀ Σ {Υ K L} (τ : TVar K (Σ ++ (L ∷ Υ))) (U : Typ Υ L) 
  (As : Σ⟦ Σ ⟧) (Bs : Σ⟦ Υ ⟧) →
    τ⟦ τ ⟧ (Σ ∋ As ++ (L ∷ Υ) ∋ (T⟦ U ⟧ Bs , Bs)) ≡ 
      T⟦ τsubstn+ Σ τ U ⟧ (Σ ∋ As ++ Υ ∋ Bs)
τsubstn+ []      ⟦ zero  ⟧⟦ U ⟧ tt       Bs = refl
τsubstn+ []      ⟦ suc τ ⟧⟦ U ⟧ tt       Bs = refl
τsubstn+ (K ∷ Σ) ⟦ zero  ⟧⟦ U ⟧ (A , As) Bs = refl
τsubstn+ (K ∷ Σ) ⟦ suc τ ⟧⟦ U ⟧ (A , As) Bs = trans 
  (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Bs) 
  (weaken⟦ τsubstn+ Σ τ U ⟧ (skip K id) (A , (Σ ∋ As ++ _ ∋ Bs)))

τsubstn+_⟦_⟧⟦_⟧² : ∀ Σ {Υ L K} (τ : TVar K (Σ ++ (L ∷ Υ))) (U : Typ Υ L) {As Bs Cs Ds} 
  (ℜs : Σ ∋ As ↔* Bs) → (ℑs : Υ ∋ Cs ↔* Ds) →
    τ⟦ τ ⟧² (Σ ∋ ℜs ++² (L ∷ Υ) ∋ (T⟦ U ⟧² ℑs , ℑs)) ≡ 
      struct K 
        (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Cs) 
        (T⟦ τsubstn+ Σ τ U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs) )
        (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ Bs Ds)
τsubstn+ []      ⟦ zero  ⟧⟦ U ⟧² tt       ℑs = refl
τsubstn+ []      ⟦ suc τ ⟧⟦ U ⟧² tt       ℑs = refl
τsubstn+ (J ∷ Σ) ⟦ zero  ⟧⟦ U ⟧² (ℜ , ℜs) ℑs = refl
τsubstn+_⟦_⟧⟦_⟧² (J ∷ Σ) {Υ} {L} {K} (suc τ) U {A , As} {B , Bs} {Cs} {Ds} (ℜ , ℜs) ℑs = 
  begin
    τ⟦ τ ⟧² (Σ ∋ ℜs ++² (L ∷ Υ) ∋ (T⟦ U ⟧² ℑs , ℑs))
  ≡⟨ τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧² ℜs ℑs ⟩
    struct K 
      (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Cs)
      (T⟦ τsubstn+ Σ τ U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
      (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ Bs Ds)
  ≡⟨ cong (λ X → struct K (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Cs) X (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ Bs Ds)) 
       (weaken⟦ τsubstn+ Σ τ U ⟧² (skip J id) (ℜ , (Σ ∋ ℜs ++² Υ ∋ ℑs))) ⟩
    struct K 
      (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Cs) 
      (struct K
        (weaken⟦ τsubstn+ Σ τ U ⟧ (skip J id) (A , (Σ ∋ As ++ Υ ∋ Cs))) 
        (T⟦ weaken (skip J id) (τsubstn+ Σ τ U) ⟧² (ℜ , (Σ ∋ ℜs ++² Υ ∋ ℑs))) 
        (weaken⟦ τsubstn+ Σ τ U ⟧ (skip J id) (B , (Σ ∋ Bs ++ Υ ∋ Ds)))) 
      (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ Bs Ds)
  ≡⟨ struct-trans K 
       (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Cs) 
       (weaken⟦ τsubstn+ Σ τ U ⟧ (skip J id) (A , (Σ ∋ As ++ Υ ∋ Cs)))
       (T⟦ weaken (skip J id) (τsubstn+ Σ τ U) ⟧² (ℜ , (Σ ∋ ℜs ++² Υ ∋ ℑs)))
       (weaken⟦ τsubstn+ Σ τ U ⟧ (skip J id) (B , (Σ ∋ Bs ++ Υ ∋ Ds)))
       (τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ Bs Ds) ⟩
    struct K 
      (τsubstn+ (J ∷ Σ) ⟦ suc τ ⟧⟦ U ⟧ (A , As) Cs) 
      (T⟦ τsubstn+ (J ∷ Σ) (suc τ) U ⟧² (ℜ , (Σ ∋ ℜs ++² Υ ∋ ℑs)) )
      (τsubstn+ (J ∷ Σ) ⟦ suc τ ⟧⟦ U ⟧ (B , Bs) Ds)    
  ∎

-- Substitution on types under a context

substn+ : ∀ Σ {Υ K L} → Typ (Σ ++ (L ∷ Υ)) K → Typ Υ L → Typ (Σ ++ Υ) K
substn+ Σ (const C) U = const C
substn+ Σ (abs K T) U = abs K (substn+ (K ∷ Σ) T U)
substn+ Σ (app S T) U = app (substn+ Σ S U) (substn+ Σ T U)
substn+ Σ (var τ)   U = τsubstn+ Σ τ U

substn+_⟦_⟧⟦_⟧ : ∀ Σ {Υ K L} (T : Typ (Σ ++ (L ∷ Υ)) K) (U : Typ Υ L) 
  (As : Σ⟦ Σ ⟧) (Bs : Σ⟦ Υ ⟧) →
    T⟦ T ⟧ (Σ ∋ As ++ (L ∷ Υ) ∋ (T⟦ U ⟧ Bs , Bs)) ≡ 
      T⟦ substn+ Σ T U ⟧ (Σ ∋ As ++ Υ ∋ Bs)
substn+ Σ ⟦ const C ⟧⟦ U ⟧ As Bs = refl
substn+ Σ ⟦ abs K T ⟧⟦ U ⟧ As Bs = ext (λ A → substn+ K ∷ Σ ⟦ T ⟧⟦ U ⟧ (A , As) Bs)
substn+ Σ ⟦ app S T ⟧⟦ U ⟧ As Bs = apply (substn+ Σ ⟦ S ⟧⟦ U ⟧ As Bs) (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Bs)
substn+ Σ ⟦ var τ   ⟧⟦ U ⟧ As Bs = τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧ As Bs

substn+_⟦_⟧⟦_⟧² : ∀ Σ {Υ L K} (T : Typ (Σ ++ (L ∷ Υ)) K) (U : Typ Υ L) {As Bs Cs Ds} 
  (ℜs : Σ ∋ As ↔* Bs) → (ℑs : Υ ∋ Cs ↔* Ds) →
    T⟦ T ⟧² (Σ ∋ ℜs ++² (L ∷ Υ) ∋ (T⟦ U ⟧² ℑs , ℑs)) ≡ 
      struct K 
        (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Cs) 
        (T⟦ substn+ Σ T U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs) )
        (substn+ Σ ⟦ T ⟧⟦ U ⟧ Bs Ds)
substn+ Σ ⟦ const C ⟧⟦ U ⟧² ℜs ℑs = refl
substn+_⟦_⟧⟦_⟧² Σ {Υ} {L} (abs J {K} T) U {As} {Bs} {Cs} {Ds} ℜs ℑs = 
  iext (λ A → iext (λ B → ext (λ ℜ → begin
    T⟦ abs J T ⟧² (Σ ∋ ℜs ++² (L ∷ Υ) ∋ (T⟦ U ⟧² ℑs , ℑs)) ℜ
  ≡⟨ substn+ (J ∷ Σ) ⟦ T ⟧⟦ U ⟧² (ℜ , ℜs) ℑs ⟩
    struct K 
      (substn+ J ∷ Σ ⟦ T ⟧⟦ U ⟧ (A , As) Cs) 
      (T⟦ substn+ (J ∷ Σ) T U ⟧² ((J ∷ Σ) ∋ (ℜ , ℜs) ++² Υ ∋ ℑs)) 
      (substn+ J ∷ Σ ⟦ T ⟧⟦ U ⟧ (B , Bs) Ds)
  ≡⟨ struct-ext J K 
       (λ A → substn+ J ∷ Σ ⟦ T ⟧⟦ U ⟧ (A , As) Cs) 
       (λ ℜ → T⟦ substn+ (J ∷ Σ) T U ⟧² ((J ∷ Σ) ∋ ℜ , ℜs ++² Υ ∋ ℑs))
       (λ B → substn+ J ∷ Σ ⟦ T ⟧⟦ U ⟧ (B , Bs) Ds) ℜ ⟩
    struct (J ⇒ K) 
      (substn+ Σ ⟦ abs J T ⟧⟦ U ⟧ As Cs) 
      (T⟦ substn+ Σ (abs J T) U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs)) 
      (substn+ Σ ⟦ abs J T ⟧⟦ U ⟧ Bs Ds) ℜ
  ∎)))
substn+_⟦_⟧⟦_⟧² Σ {Υ} {L} (app {J} {K} S T) U {As} {Bs} {Cs} {Ds} ℜs ℑs = 
  begin
    T⟦ app S T ⟧² (Σ ∋ ℜs ++² L ∷ Υ ∋ (T⟦ U ⟧² ℑs , ℑs))
  ≡⟨ cong (T⟦ S ⟧² (Σ ∋ ℜs ++² L ∷ Υ ∋ (T⟦ U ⟧² ℑs , ℑs))) (substn+ Σ ⟦ T ⟧⟦ U ⟧² ℜs ℑs) ⟩
    T⟦ S ⟧² (Σ ∋ ℜs ++² L ∷ Υ ∋ (T⟦ U ⟧² ℑs , ℑs))
      (struct J 
         (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Cs)
         (T⟦ substn+ Σ T U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
         (substn+ Σ ⟦ T ⟧⟦ U ⟧ Bs Ds))
  ≡⟨ cong (λ X → X (struct J 
       (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Cs)
       (T⟦ substn+ Σ T U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
       (substn+ Σ ⟦ T ⟧⟦ U ⟧ Bs Ds))) 
       (substn+ Σ ⟦ S ⟧⟦ U ⟧² ℜs ℑs) ⟩
    struct (J ⇒ K) 
      (substn+ Σ ⟦ S ⟧⟦ U ⟧ As Cs) 
      (T⟦ substn+ Σ S U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
      (substn+ Σ ⟦ S ⟧⟦ U ⟧ Bs Ds) 
      (struct J 
         (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Cs)
         (T⟦ substn+ Σ T U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
         (substn+ Σ ⟦ T ⟧⟦ U ⟧ Bs Ds))
  ≡⟨ struct-apply J K 
       (substn+ Σ ⟦ S ⟧⟦ U ⟧ As Cs) 
       (T⟦ substn+ Σ S U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs)) 
       (substn+ Σ ⟦ S ⟧⟦ U ⟧ Bs Ds) 
       (substn+ Σ ⟦ T ⟧⟦ U ⟧ As Cs)
       (T⟦ substn+ Σ T U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
       (substn+ Σ ⟦ T ⟧⟦ U ⟧ Bs Ds) ⟩
    struct K 
      (substn+ Σ ⟦ app S T ⟧⟦ U ⟧ As Cs)
      (T⟦ substn+ Σ (app S T) U ⟧² (Σ ∋ ℜs ++² Υ ∋ ℑs))
      (substn+ Σ ⟦ app S T ⟧⟦ U ⟧ Bs Ds)
  ∎
substn+ Σ ⟦ var τ ⟧⟦ U ⟧² ℜs ℑs = τsubstn+ Σ ⟦ τ ⟧⟦ U ⟧² ℜs ℑs

-- Substitution on types

substn : ∀ {Σ K L} → Typ (L ∷ Σ) K → Typ Σ L → Typ Σ K
substn = substn+ []

substn⟦_⟧⟦_⟧ : ∀ {Σ K L} (T : Typ (L ∷ Σ) K) (U : Typ Σ L) (As : Σ⟦ Σ ⟧)→
  T⟦ T ⟧ (T⟦ U ⟧ As , As) ≡ T⟦ substn T U ⟧ As
substn⟦ T ⟧⟦ U ⟧ = substn+ [] ⟦ T ⟧⟦ U ⟧ tt

substn⟦_⟧⟦_⟧² : ∀ {Σ K L} (T : Typ (L ∷ Σ) K) (U : Typ Σ L) {As Bs} (ℜs : Σ ∋ As ↔* Bs) →
  T⟦ T ⟧² (T⟦ U ⟧² ℜs , ℜs) ≡ 
    struct K (substn⟦ T ⟧⟦ U ⟧ As) (T⟦ substn T U ⟧² ℜs) (substn⟦ T ⟧⟦ U ⟧ Bs)
substn⟦ T ⟧⟦ U ⟧² = substn+ [] ⟦ T ⟧⟦ U ⟧² tt

-- Eta-beta equivalence on types

data _∋_≣_ {Σ} : ∀ K → Typ Σ K → Typ Σ K → Set where
  abs : ∀ K {L T U} → (L ∋ T ≣ U) → ((K ⇒ L) ∋ abs K T ≣ abs K U)
  app : ∀ {K L F G T U} → ((K ⇒ L) ∋ F ≣ G) → (K ∋ T ≣ U) → (L ∋ app F T ≣ app G U)
  beta : ∀ {K L} T U → (L ∋ app (abs K T) U ≣ substn T U)
  eta : ∀ {K L} T → ((K ⇒ L) ∋ T ≣ abs K (app (weaken (skip K id) T) tvar₀))
  ≣-refl : ∀ {K T} → (K ∋ T ≣ T)
  ≣-sym : ∀ {K T U} → (K ∋ T ≣ U) → (K ∋ U ≣ T)
  ≣-trans : ∀ {K T U V} → (K ∋ T ≣ U) → (K ∋ U ≣ V) → (K ∋ T ≣ V)

≣⟦_⟧ : ∀ {Σ K} {T U : Typ Σ K} → (K ∋ T ≣ U) → ∀ As → T⟦ T ⟧ As ≡ T⟦ U ⟧ As
≣⟦ abs K T≣U ⟧       As = ext (λ A → ≣⟦ T≣U ⟧ (A , As))
≣⟦ app F≣G T≣U ⟧     As = apply (≣⟦ F≣G ⟧ As) (≣⟦ T≣U ⟧ As)
≣⟦ beta T U ⟧        As = substn⟦ T ⟧⟦ U ⟧ As
≣⟦ eta {K} T ⟧       As = ext (λ A → apply (weaken⟦ T ⟧ (skip K id) (A , As)) refl)
≣⟦ ≣-refl ⟧          As = refl
≣⟦ ≣-sym T≣U ⟧       As = sym (≣⟦ T≣U ⟧ As)
≣⟦ ≣-trans T≣U U≣V ⟧ As = trans (≣⟦ T≣U ⟧ As) (≣⟦ U≣V ⟧ As)

≣⟦_⟧² : ∀ {Σ K} {T U : Typ Σ K} (T≣U : K ∋ T ≣ U) {As Bs} (ℜs : Σ ∋ As ↔* Bs) → 
  T⟦ T ⟧² ℜs ≡ struct K (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs)
≣⟦ abs K {L} {T} {U} T≣U ⟧² {As} {Bs} ℜs = 
  iext (λ A → iext (λ B → ext (λ ℜ → begin
    T⟦ T ⟧² (ℜ , ℜs)
  ≡⟨ ≣⟦ T≣U ⟧² (ℜ , ℜs) ⟩
    struct L (≣⟦ T≣U ⟧ (A , As)) (T⟦ U ⟧² (ℜ , ℜs)) (≣⟦ T≣U ⟧ (B , Bs))
  ≡⟨ struct-ext K L (λ A → ≣⟦ T≣U ⟧ (A , As)) (λ ℜ' → T⟦ U ⟧² (ℜ' , ℜs)) (λ B → ≣⟦ T≣U ⟧ (B , Bs)) ℜ ⟩
    struct (K ⇒ L) (≣⟦ abs K T≣U ⟧ As) (T⟦ abs K U ⟧² ℜs) (≣⟦ abs K T≣U ⟧ Bs) ℜ
  ∎)))
≣⟦ app {K} {L} {F} {G} {T} {U} F≣G T≣U ⟧² {As} {Bs} ℜs = 
  begin
    T⟦ app F T ⟧² ℜs
  ≡⟨ cong (T⟦ F ⟧² ℜs) (≣⟦ T≣U ⟧² ℜs) ⟩
    T⟦ F ⟧² ℜs (struct K (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs))
  ≡⟨ cong (λ X → X (struct K (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs)))
       (≣⟦ F≣G ⟧² ℜs) ⟩
    struct (K ⇒ L) (≣⟦ F≣G ⟧ As) (T⟦ G ⟧² ℜs) (≣⟦ F≣G ⟧ Bs)
      (struct K (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs))
  ≡⟨ struct-apply K L
       (≣⟦ F≣G ⟧ As) (T⟦ G ⟧² ℜs) (≣⟦ F≣G ⟧ Bs)
       (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs) ⟩
    struct L (≣⟦ app F≣G T≣U ⟧ As) (T⟦ app G U ⟧² ℜs) (≣⟦ app F≣G T≣U ⟧ Bs)
  ∎
≣⟦ beta T U ⟧² ℜs = substn⟦ T ⟧⟦ U ⟧² ℜs
≣⟦ eta {K} {L} T ⟧² {As} {Bs} ℜs = iext (λ A → iext (λ B → ext (λ ℜ → 
  begin
    T⟦ T ⟧² ℜs ℜ
  ≡⟨ cong (λ X → X ℜ) (weaken⟦ T ⟧² (skip K id) (ℜ , ℜs)) ⟩
    struct (K ⇒ L) 
      (weaken⟦ T ⟧ (skip K id) (A , As))
      (T⟦ weaken (skip K id) T ⟧² (ℜ , ℜs))
      (weaken⟦ T ⟧ (skip K id) (B , Bs)) ℜ
  ≡⟨ struct-apply K L 
       (weaken⟦ T ⟧ (skip K id) (A , As)) 
       (T⟦ weaken (skip K id) T ⟧² (ℜ , ℜs)) 
       (weaken⟦ T ⟧ (skip K id) (B , Bs)) refl ℜ refl ⟩
    struct L 
      (apply (weaken⟦ T ⟧ (skip K id) (A , As)) refl)
      (T⟦ weaken (skip K id) T ⟧² (ℜ , ℜs) ℜ)
      (apply (weaken⟦ T ⟧ (skip K id) (B , Bs)) refl)
  ≡⟨ struct-ext K L
       (λ A → apply (weaken⟦ T ⟧ (skip K id) (A , As)) refl) 
       (λ ℜ → T⟦ weaken (skip K id) T ⟧² (ℜ , ℜs) ℜ) 
       (λ B → apply (weaken⟦ T ⟧ (skip K id) (B , Bs)) refl) ℜ ⟩
    struct (K ⇒ L) 
      (≣⟦ eta T ⟧ As)
      (T⟦ abs K (app (weaken (skip K id) T) (var zero)) ⟧² ℜs)
      (≣⟦ eta T ⟧ Bs) ℜ
  ∎)))
≣⟦ ≣-refl ⟧² ℜs = refl
≣⟦ ≣-sym {K} {T} {U} T≣U ⟧² {As} {Bs} ℜs = 
  struct-sym K (≣⟦ T≣U ⟧ As) (≣⟦ T≣U ⟧ Bs) (≣⟦ T≣U ⟧² ℜs)
≣⟦ ≣-trans {K} {T} {U} {V} T≣U U≣V ⟧² {As} {Bs} ℜs =
  begin
    T⟦ T ⟧² ℜs
  ≡⟨ ≣⟦ T≣U ⟧² ℜs ⟩
    struct K (≣⟦ T≣U ⟧ As) (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ Bs)
  ≡⟨ cong (λ X → struct K (≣⟦ T≣U ⟧ As) X (≣⟦ T≣U ⟧ Bs)) (≣⟦ U≣V ⟧² ℜs) ⟩
    struct K (≣⟦ T≣U ⟧ As) (struct K (≣⟦ U≣V ⟧ As) (T⟦ V ⟧² ℜs) (≣⟦ U≣V ⟧ Bs)) (≣⟦ T≣U ⟧ Bs)
  ≡⟨ struct-trans K (≣⟦ T≣U ⟧ As) (≣⟦ U≣V ⟧ As) (T⟦ V ⟧² ℜs) (≣⟦ U≣V ⟧ Bs) (≣⟦ T≣U ⟧ Bs) ⟩
    struct K (≣⟦ ≣-trans T≣U U≣V ⟧ As) (T⟦ V ⟧² ℜs) (≣⟦ ≣-trans T≣U U≣V ⟧ Bs)
  ∎

-- Variables

data Var {Σ : Kinds} {α} (T : Typ Σ (set α)) : Typs Σ → Set where
  zero : ∀ {Γ} → Var T (T ∷ Γ)
  suc : ∀ {β Γ} {U : Typ Σ (set β)} → Var T Γ → Var T (U ∷ Γ)

x⟦_⟧ : ∀ {Σ} {Γ : Typs Σ} {α} {T : Typ Σ (set α)} → 
  Var T Γ → (As : Σ⟦ Σ ⟧) → (as : Γ⟦ Γ ⟧ As) → (T⟦ T ⟧ As)
x⟦ zero ⟧  As (a , as) = a
x⟦ suc x ⟧ As (a , as) = x⟦ x ⟧ As as

x⟦_⟧² : ∀ {Σ} {Γ : Typs Σ} {α} {T : Typ Σ (set α)} (x : Var T Γ) → 
  ∀ {As Bs} (ℜs : Σ ∋ As ↔* Bs) {as bs} → 
    (Γ⟦ Γ ⟧² ℜs as bs) → (T⟦ T ⟧² ℜs (x⟦ x ⟧ As as) (x⟦ x ⟧ Bs bs))
x⟦ zero ⟧²  ℜs (aℜb , asℜbs) = aℜb
x⟦ suc x ⟧² ℜs (aℜb , asℜbs) = x⟦ x ⟧² ℜs asℜbs

-- Constants

data Const {Σ : Kinds} : ∀ {α} → Typ Σ (set α) → Set where
  pair : ∀ {α β} → Const (Π (set α) (Π (set β) (tvar₁ ⊸ (tvar₀ ⊸ (tvar₁ ⊗ tvar₀)))))
  fst : ∀ {α β} → Const (Π (set α) (Π (set β) ((tvar₁ ⊗ tvar₀) ⊸ tvar₁)))
  snd : ∀ {α β} → Const (Π (set α) (Π (set β) ((tvar₁ ⊗ tvar₀) ⊸ tvar₀)))
  ≼-refl : Const (Π time (tvar₀ ≼ tvar₀))
  ≼-trans : Const (Π time (Π time (Π time ((tvar₂ ≼ tvar₁) ⊸ ((tvar₁ ≼ tvar₀) ⊸ (tvar₂ ≼ tvar₀))))))
  ≼-absurd : ∀ {α} → Const (Π (set α) (Π time (Π time ((tvar₁ ≺ tvar₀) ⊸ ((tvar₀ ≼ tvar₁) ⊸ tvar₂)))))
  ≼-case : ∀ {α} → Const (Π (set α) (Π time (Π time (((tvar₁ ≼ tvar₀) ⊸ tvar₂) ⊸ (((tvar₀ ≺ tvar₁) ⊸ tvar₂) ⊸ tvar₂)))))

absurd : ∀ {α} {A : Set α} b → True b → True (not b) → A
absurd true  tt ()
absurd false () tt

cond : ∀ {α} {A : Set α} b → (True (not b) → A) → (True b → A) → A
cond true  f g = g tt
cond false f g = f tt

c⟦_⟧ : ∀ {Σ} {α} {T : Typ Σ (set α)} → 
  Const T → (As : Σ⟦ Σ ⟧) → (T⟦ T ⟧ As)
c⟦ pair ⟧     As = λ A B a b → (a , b)
c⟦ fst ⟧      As = λ A B → proj₁
c⟦ snd ⟧      As = λ A B → proj₂
c⟦ ≼-refl ⟧   As = ≤-refl
c⟦ ≼-trans ⟧  As = ≤-trans
c⟦ ≼-absurd ⟧ As = λ A t u → absurd (t < u)
c⟦ ≼-case ⟧   As = λ A t u → cond (u < t)

cond² : ∀ {α} {A A′ : Set α} (ℜ : A → A′ → Set α) b →
  ∀ {f f′} → (∀ b× → ℜ (f b×) (f′ b×)) →
    ∀ {g g′} → (∀ b✓ → ℜ (g b✓) (g′ b✓)) →
      ℜ (cond b f g) (cond b f′ g′)
cond² ℜ true  fℜf′ gℜg′ = gℜg′ tt
cond² ℜ false fℜf′ gℜg′ = fℜf′ tt

c⟦_⟧² : ∀ {Σ} {α} {T : Typ Σ (set α)} (c : Const T) → 
  ∀ {As Bs} (ℜs : Σ ∋ As ↔* Bs) → 
    (T⟦ T ⟧² ℜs (c⟦ c ⟧ As) (c⟦ c ⟧ Bs))
c⟦ pair ⟧²       ℜs = λ ℜ ℑ aℜb cℑd → (aℜb , cℑd)
c⟦ fst ⟧²        ℜs = λ ℜ ℑ → proj₁
c⟦ snd ⟧²        ℜs = λ ℜ ℑ → proj₂
c⟦ ≼-refl ⟧²     ℜs = _
c⟦ ≼-trans ⟧²    ℜs = _
c⟦ ≼-absurd ⟧²   ℜs = λ ℜ {t} t≡t {u} u≡u {t<u} tt {u≤t} tt → absurd (t < u) t<u u≤t
c⟦ ≼-case {α} ⟧² ℜs = lemma where
  lemma : ∀ {A A′ : Set α} (ℜ : A → A′ → Set α) →
    ∀ {t t′} → (t ≡ t′) → ∀ {u u′} → (u ≡ u′) →
      ∀ {f f′} → (∀ {t≤u t′≤u′} → ⊤ → ℜ (f t≤u) (f′ t′≤u′)) →
        ∀ {g g′} → (∀ {u<t u′<t′} → ⊤ → ℜ (g u<t) (g′ u′<t′)) →
          ℜ (cond (u < t) f g) (cond (u′ < t′) f′ g′)
  lemma ℜ {t} refl {u} refl fℜf′ gℜg′ = 
    cond² ℜ (u < t) (λ t≤u → fℜf′ {t≤u} {t≤u} tt) (λ u<t → gℜg′ {u<t} {u<t} tt)
  
-- Expressions

data Exp {Σ : Kinds} (Γ : Typs Σ) : ∀ {α} → Typ Σ (set α) → Set where
  const : ∀ {α} {T : Typ Σ (set α)} → Const T → Exp Γ T
  abs : ∀ {α β} (T : Typ Σ (set α)) {U : Typ Σ (set β)} (M : Exp (T ∷ Γ) U) → Exp Γ (T ⊸ U)
  app : ∀ {α β} {T : Typ Σ (set α)} {U : Typ Σ (set β)} (M : Exp Γ (T ⊸ U)) (N : Exp Γ T) → Exp Γ U
  var : ∀ {α} {T : Typ Σ (set α)} → Var T Γ → Exp Γ T
  tabs : ∀ K {α} {T : Typ (K ∷ Σ) (set α)} (M : Exp (weakens (skip K id) Γ) T) → Exp Γ (Π K T)
  tapp : ∀ {K α} {T : Typ (K ∷ Σ) (set α)} → Exp Γ (Π K T) → ∀ U → Exp Γ (substn T U)
  eq : ∀ {α T U} → (set α ∋ T ≣ U) → (Exp Γ T) → (Exp Γ U)

ctxt : ∀ {Σ Γ α T} → Exp {Σ} Γ {α} T → Typs Σ
ctxt {Σ} {Γ} M = Γ

M⟦_⟧ : ∀ {Σ} {Γ : Typs Σ} {α} {T : Typ Σ (set α)} → 
  Exp Γ T → (As : Σ⟦ Σ ⟧) → (as : Γ⟦ Γ ⟧ As) → (T⟦ T ⟧ As)
M⟦ const c ⟧  As as = c⟦ c ⟧ As
M⟦ abs T M ⟧  As as = λ a → M⟦ M ⟧ As (a , as)
M⟦ app M N ⟧  As as = M⟦ M ⟧ As as (M⟦ N ⟧ As as)
M⟦ var x ⟧    As as = x⟦ x ⟧ As as
M⟦ tabs K M ⟧ As as = λ A → 
  M⟦ M ⟧ (A , As) (weakens⟦ ctxt (tabs K M) ⟧ (skip K id) (A , As) as)
M⟦ tapp {T = T} M U ⟧ As as = 
  cast (substn⟦ T ⟧⟦ U ⟧ As) (M⟦ M ⟧ As as (T⟦ U ⟧ As))
M⟦ eq T≣U M ⟧ As as = cast (≣⟦ T≣U ⟧ As) (M⟦ M ⟧ As as)

M⟦_⟧² : ∀ {Σ} {Γ : Typs Σ} {α} {T : Typ Σ (set α)} (M : Exp Γ T) → 
  ∀ {As Bs} (ℜs : Σ ∋ As ↔* Bs) {as bs} → 
    (Γ⟦ Γ ⟧² ℜs as bs) → (T⟦ T ⟧² ℜs (M⟦ M ⟧ As as) (M⟦ M ⟧ Bs bs))
M⟦ const c ⟧²  ℜs asℜbs = c⟦ c ⟧² ℜs
M⟦ abs T M ⟧²  ℜs asℜbs = λ aℜb → M⟦ M ⟧² ℜs (aℜb , asℜbs)
M⟦ app M N ⟧²  ℜs asℜbs = M⟦ M ⟧² ℜs asℜbs (M⟦ N ⟧² ℜs asℜbs)
M⟦ var x  ⟧²   ℜs asℜbs = x⟦ x ⟧² ℜs asℜbs
M⟦ tabs K M ⟧² ℜs asℜbs = λ ℜ → 
  M⟦ M ⟧² (ℜ , ℜs) (weakens⟦ ctxt (tabs K M) ⟧² (skip K id) (ℜ , ℜs) asℜbs)
M⟦ tapp {T = T} M U ⟧² ℜs asℜbs = 
  struct-cast (T⟦ substn T U ⟧² ℜs) (substn⟦ T ⟧⟦ U ⟧ _) (substn⟦ T ⟧⟦ U ⟧ _)
    (cast² (substn⟦ T ⟧⟦ U ⟧² ℜs) (M⟦ M ⟧² ℜs asℜbs (T⟦ U ⟧² ℜs)))
M⟦ eq {α} {T} {U} T≣U M ⟧² {As} {Bs} ℜs asℜbs = 
  struct-cast (T⟦ U ⟧² ℜs) (≣⟦ T≣U ⟧ As) (≣⟦ T≣U ⟧ Bs) (cast² (≣⟦ T≣U ⟧² ℜs) (M⟦ M ⟧² ℜs asℜbs))

-- Types with a chosen free world variable

_∷ʳ_ : Kinds → Kind → Kinds
[]      ∷ʳ K = K ∷ []
(T ∷ Σ) ∷ʳ K = T ∷ (Σ ∷ʳ K)

TVar+ : Kind → Kinds → Set
TVar+ K Σ = TVar K (Σ ∷ʳ rset₀)

Typ+ : Kinds → Kind → Set
Typ+ Σ = Typ (Σ ∷ʳ rset₀)

wvar : ∀ Σ → TVar+ rset₀ Σ
wvar []      = zero
wvar (K ∷ Σ) = suc (wvar Σ)

world : ∀ {Σ} → Typ+ Σ rset₀
world {Σ} = var (wvar Σ)

World : Time → Set
World t = ⊤

taut : ∀ {Σ α} → Typ+ Σ (rset α ⇒ set α)
taut {Σ} {α} = abs (rset α) (Π time 
  (app (world {time ∷ rset α ∷ Σ}) tvar₀ ⊸ app tvar₁ tvar₀))

signal : ∀ {Σ α} → Typ+ Σ (rset α ⇒ rset α)
signal {Σ} {α} = abs (rset α) (abs time (Π time ((tvar₁ ≼ tvar₀) ⊸ 
  ((world {time ∷ time ∷ rset α ∷ Σ} ⟨ tvar₁ , tvar₀ ]) ⊸ app tvar₂ tvar₀))))

▧ : ∀ {Σ α} → Typ+ Σ (rset α) → Typ+ Σ (rset α)
▧ {Σ} = app (signal {Σ})

-- Surface types

data STyp : Kind → Set where
  ⟨_⟩ : ∀ {α} → STyp (set α) → STyp (rset α)
  [_] : ∀ {α} → STyp (rset α) → STyp (set α)
  _⊠_ _↦_ : ∀ {α β} → STyp (set α) → STyp (set β) → STyp (set (α ⊔ β))
  _∧_ _⇒_ : ∀ {α β} → STyp (rset α) → STyp (rset β) → STyp (rset (α ⊔ β))
  □ : ∀ {α} → STyp (rset α) → STyp (rset α)

⟪_⟫ : ∀ {K} → STyp K → Typ+ [] K
⟪ ⟨ T ⟩ ⟫ = app always ⟪ T ⟫
⟪ [ T ] ⟫ = app (taut {[]}) ⟪ T ⟫
⟪ T ⊠ U ⟫ = ⟪ T ⟫ ⊗ ⟪ U ⟫
⟪ T ↦ U ⟫ = ⟪ T ⟫ ⊸ ⟪ U ⟫
⟪ T ∧ U ⟫ = ⟪ T ⟫ ⊗ʳ ⟪ U ⟫
⟪ T ⇒ U ⟫ = ⟪ T ⟫ ⊸ʳ ⟪ U ⟫
⟪ □ T ⟫   = ▧ {[]} ⟪ T ⟫

T⟪_⟫ : ∀ {K} → STyp K → K⟦ K ⟧
T⟪ T ⟫ = T⟦ ⟪ T ⟫ ⟧ (World , tt)

-- Signals of T are iso to □ T

Signal : ∀ {α} → RSet α → RSet α
Signal A s = ∀ t → True (s ≤ t) → A t

sig : ∀ {α} (T : STyp (rset α)) s → 
  T⟪ □ T ⟫ s → Signal T⟪ T ⟫ s
sig T s σ t s≤t = σ t s≤t _

sig⁻¹ : ∀ {α} (T : STyp (rset α)) s → 
  Signal T⟪ T ⟫ s → T⟪ □ T ⟫ s
sig⁻¹ T s σ t s≤t _ = σ t s≤t

sig-iso : ∀ {α} (T : STyp (rset α)) s σ → 
  (sig T s (sig⁻¹ T s σ) ≡ σ)
sig-iso T s σ = refl

sig-iso⁻¹ : ∀ {α} (T : STyp (rset α)) s σ →
  (sig⁻¹ T s (sig T s σ) ≡ σ)
sig-iso⁻¹ T s σ = refl

-- Signal functions from T to U are iso to □ T ⇒ □ U

SF : ∀ {α β} → RSet α → RSet β → RSet (α ⊔ β)
SF A B s = Signal A s → Signal B s

sf : ∀ {α β} (T : STyp (rset α)) (U : STyp (rset β)) s →
  T⟪ □ T ⇒ □ U ⟫ s → SF T⟪ T ⟫ T⟪ U ⟫ s
sf T U s f σ = sig U s (f (sig⁻¹ T s σ))

sf⁻¹ : ∀ {α β} (T : STyp (rset α)) (U : STyp (rset β)) s →
   SF T⟪ T ⟫ T⟪ U ⟫ s → T⟪ □ T ⇒ □ U ⟫ s
sf⁻¹ T U s f σ = sig⁻¹ U s (f (sig T s σ))

sf-iso : ∀ {α β} (T : STyp (rset α)) (U : STyp (rset β)) s f → 
  (sf T U s (sf⁻¹ T U s f) ≡ f)
sf-iso T U s f = refl

sf-iso⁻¹ : ∀ {α β} (T : STyp (rset α)) (U : STyp (rset β)) s f → 
  (sf⁻¹ T U s (sf T U s f) ≡ f)
sf-iso⁻¹ T U s f = refl

-- Causality

mutual

  _at_⊨_≈[_]_ : ∀ {α} (T : STyp (rset α)) s → T⟪ T ⟫ s → Time → T⟪ T ⟫ s → Set α
  ⟨ T ⟩   at s ⊨ a       ≈[ u ] b       = T ⊨ a ≈[ u ] b
  (T ∧ U) at s ⊨ (a , b) ≈[ u ] (c , d) = (T at s ⊨ a ≈[ u ] c) × (U at s ⊨ b ≈[ u ] d)
  (T ⇒ U) at s ⊨ f       ≈[ u ] g       = ∀ a b → (T at s ⊨ a ≈[ u ] b) → (U at s ⊨ f a ≈[ u ] g b)
  □ T     at s ⊨ σ       ≈[ u ] τ       = (∀ t s≤t → True (t ≤ u) → (T at t ⊨ σ t s≤t _ ≈[ u ] τ t s≤t _))

  _⊨_≈[_]_ : ∀ {α} → (T : STyp (set α)) → T⟪ T ⟫ → Time → T⟪ T ⟫ → Set α
  [ T ]   ⊨ σ       ≈[ u ] τ       = ∀ s → True (s ≤ u) → (T at s ⊨ σ s _ ≈[ u ] τ s _)
  (T ⊠ U) ⊨ (a , b) ≈[ u ] (c , d) = (T ⊨ a ≈[ u ] c) × (U ⊨ b ≈[ u ] d)
  (T ↦ U) ⊨ f       ≈[ u ] g       = ∀ a b → (T ⊨ a ≈[ u ] b) → (U ⊨ f a ≈[ u ] g b)

Causal : ∀ {α β} (T : STyp (set α)) (U : STyp (set β)) → T⟪ T ↦ U ⟫ → Set (α ⊔ β)
Causal T U f = ∀ u σ τ → 
  (T ⊨ σ ≈[ u ] τ) → (U ⊨ f σ ≈[ u ] f τ)

-- Parametricity implies causality

ℜ[_] : Time → (rset o ∋ World ↔ World)
ℜ[ u ] {t} s≡t tt tt = True (t ≤ u)

mutual

  ℜ-impl-≈_at : ∀ {α} (T : STyp (rset α)) s u → True (s ≤ u) → ∀ a b →
    (T⟦ ⟪ T ⟫ ⟧² (ℜ[ u ] , tt) refl a b) → (T at s ⊨ a ≈[ u ] b)
  ℜ-impl-≈ ⟨ T ⟩   at s u s≤u a b aℜb
    = ℜ-impl-≈ T u a b aℜb
  ℜ-impl-≈ (T ∧ U) at s u s≤u (a , b) (c , d) (aℜc , bℜd) 
    = (ℜ-impl-≈ T at s u s≤u a c aℜc , ℜ-impl-≈ U at s u s≤u b d bℜd)
  ℜ-impl-≈ (T ⇒ U) at s u s≤u f g fℜg
    = λ a b a≈b → ℜ-impl-≈ U at s u s≤u (f a) (g b) (fℜg (≈-impl-ℜ T at s u s≤u a b a≈b))
  ℜ-impl-≈_at (□ T) s u s≤u σ τ σℜτ = λ t s≤t t≤u → 
    ℜ-impl-≈ T at t u t≤u (σ t s≤t _) (τ t s≤t _) 
      (σℜτ refl tt (λ {r} _ _ {r≤t} _ → ≤-trans r t u r≤t t≤u))

  ≈-impl-ℜ_at : ∀ {α} (T : STyp (rset α)) s u → True (s ≤ u) → ∀ a b →
     (T at s ⊨ a ≈[ u ] b) → (T⟦ ⟪ T ⟫ ⟧² (ℜ[ u ] , tt) refl a b)
  ≈-impl-ℜ ⟨ T ⟩   at s u s≤u a b a≈b
    = ≈-impl-ℜ T u a b a≈b
  ≈-impl-ℜ (T ∧ U) at s u s≤u (a , b) (c , d) (a≈c , b≈d)
    = (≈-impl-ℜ T at s u s≤u a c a≈c , ≈-impl-ℜ U at s u s≤u b d b≈d)
  ≈-impl-ℜ (T ⇒ U) at s u s≤u f g f≈g
    = λ {a} {b} aℜb → ≈-impl-ℜ U at s u s≤u (f a) (g b) (f≈g a b (ℜ-impl-≈ T at s u s≤u a b aℜb))
  ≈-impl-ℜ (□ T)   at s u s≤u σ τ σ≈τ = lemma where
    lemma : T⟦ ⟪ □ T ⟫ ⟧² (ℜ[ u ] , tt) {s} refl σ τ
    lemma {t} refl {s≤t} {s≤t′} tt kℜk′ with irrel (s ≤ t) s≤t s≤t′
    lemma {t} refl {s≤t}        tt kℜk′ | refl
      = ≈-impl-ℜ T at t u t≤u (σ t s≤t _) (τ t s≤t _) (σ≈τ t s≤t t≤u) where
        t≤u : True (t ≤ u)
        t≤u with switch (s < t)
        t≤u | (true , s<t)  = kℜk′ {t} refl {s<t} {s<t} tt {≤-refl t} {≤-refl t} tt 
        t≤u | (false , t≤s) = ≤-trans t s u t≤s s≤u

  ℜ-impl-≈ : ∀ {α} (T : STyp (set α)) (u : Time) (a b : T⟪ T ⟫) →
    (T⟦ ⟪ T ⟫ ⟧² (ℜ[ u ] , tt) a b) → (T ⊨ a ≈[ u ] b)
  ℜ-impl-≈ (T ⊠ U) u (a , b) (c , d) (aℜc , bℜd)
    = (ℜ-impl-≈ T u a c aℜc , ℜ-impl-≈ U u b d bℜd)
  ℜ-impl-≈ (T ↦ U) u f g fℜg
    = λ a b a≈b → ℜ-impl-≈ U u (f a) (g b) (fℜg (≈-impl-ℜ T u a b a≈b))
  ℜ-impl-≈ [ T ] u σ τ σℜτ
    = λ s s≤u → ℜ-impl-≈ T at s u s≤u (σ s _) (τ s _) (σℜτ refl s≤u)

  ≈-impl-ℜ : ∀ {α} (T : STyp (set α)) (u : Time) (a b : T⟪ T ⟫) →
    (T ⊨ a ≈[ u ] b) → (T⟦ ⟪ T ⟫ ⟧² (ℜ[ u ] , tt) a b)
  ≈-impl-ℜ (T ⊠ U) u (a , b) (c , d) (a≈c , b≈d)
    = (≈-impl-ℜ T u a c a≈c , ≈-impl-ℜ U u b d b≈d)
  ≈-impl-ℜ (T ↦ U) u f g f≈g
    = λ {a} {b} aℜb → ≈-impl-ℜ U u (f a) (g b) (f≈g a b (ℜ-impl-≈ T u a b aℜb))
  ≈-impl-ℜ [ T ] u σ τ σ≈τ = lemma where
    lemma : T⟦ ⟪ [ T ] ⟫ ⟧² (ℜ[ u ] , tt) σ τ
    lemma {s} refl s≤u = ≈-impl-ℜ T at s u s≤u (σ s _) (τ s _) (σ≈τ s s≤u)

-- Every F-omega function is causal

causality : ∀ {α β} (T : STyp (set α)) (U : STyp (set β)) (M : Exp [] ⟪ T ↦ U ⟫) → 
  Causal T U (M⟦ M ⟧ (World , tt) tt)
causality T U M u
  = ℜ-impl-≈ (T ↦ U) u
      (M⟦ M ⟧ (World , tt) tt) 
      (M⟦ M ⟧ (World , tt) tt) 
      (M⟦ M ⟧² (ℜ[ u ] , _) tt)
