open import FRP.JS.Model.Util using 
  ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; begin_ ; _≡⟨_⟩_ ; _∎ ; ≡-relevant ; _∘_ )
open import FRP.JS.Nat using ( zero ; suc ) renaming ( ℕ to ♭ℕ ; _+_ to add )

module FRP.JS.Model.DNat where

infixr 5 _,_
infixr 5 _+_

_+♭_ = add

add-unit : ∀ n → (add n 0) ≡ n
add-unit zero    = refl
add-unit (suc n) = cong suc (add-unit n)

add-assoc : ∀ m n → (add (add m n) ≡ ((add m) ∘ (add n)))
add-assoc zero    n = refl
add-assoc (suc m) n = cong (_∘_ suc) (add-assoc m n)

-- "Difference nats" are isomorphic to ℕ but have _+_ associative up 
-- to beta-reduction, not just up to _≡_.

record ℕ : Set where
  constructor _,_
  field
    fun : ♭ℕ → ♭ℕ
    .fun✓ : fun ≡ add (fun 0)

open ℕ public

-- Convert ℕ to ♭ℕ and back

♯ : ♭ℕ → ℕ
♯ n = (add n , cong add (sym (add-unit n)))

♭ : ℕ → ♭ℕ
♭ (f , f✓) = f 0

-- Constants

♯0 = ♯ 0
♯1 = ♯ 1

-- Addition

_+_ : ℕ → ℕ → ℕ
(f , f✓) + (g , g✓) = ((f ∘ g) , f∘g✓) where
  .f∘g✓ : (f ∘ g) ≡ add (f (g 0))
  f∘g✓ = begin
      f ∘ g
    ≡⟨ cong₂ _∘_ f✓ g✓ ⟩
      add (f 0) ∘ add (g 0)
    ≡⟨ sym (add-assoc (f 0) (g 0)) ⟩
      add (add (f 0) (g 0))
    ≡⟨ cong (λ X → add (X (g 0))) (sym f✓) ⟩
      add (f (g 0))
    ∎

--Isomorphism which respects +

inject : ∀ m n → (fun m ≡ fun n) → (m ≡ n)
inject (f , f✓) (.f , g✓) refl = refl

iso : ∀ n → ♯ (♭ n) ≡ n
iso n = inject (♯ (♭ n)) n (sym (≡-relevant (fun✓ n)))

iso⁻¹ : ∀ n → ♭ (♯ n) ≡ n
iso⁻¹ = add-unit

iso-resp-+ : ∀ m n → ♭ (m + n) ≡ (♭ m +♭ ♭ n)
iso-resp-+ (f , f✓) (g , g✓) = cong (λ X → X (g 0)) (≡-relevant f✓) 

-- Addition forms a monoid on the nose

+-assoc : ∀ l m n → (((l + m) + n) ≡ (l + (m + n)))
+-assoc l m n = refl

+-unit₁ : ∀ n → ((♯0 + n) ≡ n)
+-unit₁ n = refl

+-unit₂ : ∀ n → ((n + ♯0) ≡ n)
+-unit₂ n = refl
