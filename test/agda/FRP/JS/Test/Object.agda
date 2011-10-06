open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ) renaming ( _==[_]_  to _==?[_]_ )
open import FRP.JS.Nat using ( ℕ ; zero ; suc ; _==_ ; _<_ )
open import FRP.JS.Object using ( Object ; IObject ; [] ; _↦_∷_ ; object ; ⟨⟩ ; _==[_]_ ; _⊆[_]_ ; lookup ; lookup? ; map ; filter )
open import FRP.JS.QUnit using ( TestSuite ; ok ; test ; _,_ )

module FRP.JS.Test.Object where

_==*_ : Object ℕ → Object ℕ → Bool
xs ==* ys = xs ==[ _==_ ] ys

_⊆*_ : Object ℕ → Object ℕ → Bool
xs ⊆* ys = xs ⊆[ _==_ ] ys

_==?_ : Maybe ℕ → Maybe ℕ → Bool
xs ==? ys = xs ==?[ _==_ ] ys

_==??_ : Maybe (Maybe ℕ) → Maybe (Maybe ℕ) → Bool
xs ==?? ys = xs ==?[ _==?_ ] ys

iincr : ∀ {ks ks✓} → IObject ℕ ks ks✓ → IObject ℕ ks ks✓
iincr []           = []
iincr (k ↦ n ∷ ns) = k ↦ suc n ∷ iincr ns

incr : Object ℕ → Object ℕ
incr (object ns) = object (iincr ns)

⟨a↦0⟩ = object ("a" ↦ 0 ∷ [])
⟨a↦1⟩ = object ("a" ↦ 1 ∷ [])
⟨a↦0,b↦1⟩ = object ("a" ↦ 0 ∷ "b" ↦ 1 ∷ [])
⟨a↦1,b↦2⟩ = object ("a" ↦ 1 ∷ "b" ↦ 2 ∷ [])
⟨b↦0⟩ = object ("b" ↦ 0 ∷ [])
⟨b↦2⟩ = object ("b" ↦ 2 ∷ [])
⟨a↦n⟩ = object ("a" ↦ nothing {A = ℕ} ∷ [])
⟨a↦j0⟩ = object ("a" ↦ just 0 ∷ [])

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "⟨⟩ == ⟨⟩" (⟨⟩ ==* ⟨⟩)
    , ok "⟨a↦0⟩ == ⟨⟩" (not (⟨a↦0⟩ ==* ⟨⟩))
    , ok "⟨⟩ == ⟨a↦0⟩" (not (⟨⟩ ==* ⟨a↦0⟩))
    , ok "⟨a↦0⟩ == ⟨a↦0⟩" (⟨a↦0⟩ ==* ⟨a↦0⟩)
    , ok "⟨a↦0⟩ == ⟨a↦1⟩" (not (⟨a↦0⟩ ==* ⟨a↦1⟩))
    , ok "⟨a↦0⟩ == ⟨a↦0,b↦1⟩" (not (⟨a↦0⟩ ==* ⟨a↦0,b↦1⟩))
    , ok "⟨a↦0,b↦1⟩ == ⟨a↦0⟩" (not (⟨a↦0,b↦1⟩ ==* ⟨a↦0⟩))
    , ok "⟨a↦0,b↦1⟩ == ⟨a↦0,b↦1⟩" (⟨a↦0,b↦1⟩ ==* ⟨a↦0,b↦1⟩) )
  , test "⊆" 
    ( ok "⟨⟩ ⊆ ⟨⟩" (⟨⟩ ⊆* ⟨⟩)
    , ok "⟨a↦0⟩ ⊆ ⟨⟩" (not (⟨a↦0⟩ ⊆* ⟨⟩))
    , ok "⟨⟩ ⊆ ⟨a↦0⟩" (⟨⟩ ⊆* ⟨a↦0⟩)
    , ok "⟨a↦0⟩ ⊆ ⟨a↦0⟩" (⟨a↦0⟩ ⊆* ⟨a↦0⟩)
    , ok "⟨a↦0⟩ ⊆ ⟨a↦1⟩" (not (⟨a↦0⟩ ⊆* ⟨a↦1⟩))
    , ok "⟨a↦0⟩ ⊆ ⟨a↦0,b↦1⟩" (⟨a↦0⟩ ⊆* ⟨a↦0,b↦1⟩)
    , ok "⟨a↦0,b↦1⟩ ⊆ ⟨a↦0⟩" (not (⟨a↦0,b↦1⟩ ⊆* ⟨a↦0⟩))
    , ok "⟨a↦0,b↦1⟩ ⊆ ⟨a↦0,b↦1⟩" (⟨a↦0,b↦1⟩ ⊆* ⟨a↦0,b↦1⟩) )
  , test "lookup" 
    ( ok "lookup ⟨a↦0⟩ a" (lookup ⟨a↦0⟩ "a" == 0)
    , ok "lookup ⟨a↦0,b↦1⟩ a" (lookup ⟨a↦0,b↦1⟩ "b" == 1)
    , ok "lookup ⟨a↦0,b↦1⟩ a" (lookup ⟨a↦0,b↦1⟩ "a" == 0)
    , ok "lookup ⟨a↦0,b↦1⟩ b" (lookup ⟨a↦0,b↦1⟩ "b" == 1)
    , ok "lookup ⟨a↦j0⟩ a" (lookup ⟨a↦j0⟩ "a" ==? just 0)
    , ok "lookup ⟨a↦n⟩ a" (lookup ⟨a↦n⟩ "a" ==? nothing)
    , ok "lookup? ⟨⟩    a" (lookup? ⟨⟩ "a" ==? nothing)
    , ok "lookup? ⟨a↦0⟩ a" (lookup? ⟨a↦0⟩ "a" ==? just 0)
    , ok "lookup? ⟨a↦0⟩ b" (lookup? ⟨a↦0⟩ "b" ==? nothing)
    , ok "lookup? ⟨a↦0,b↦1⟩ a" (lookup? ⟨a↦0,b↦1⟩ "a" ==? just 0)
    , ok "lookup? ⟨a↦0,b↦1⟩ b" (lookup? ⟨a↦0,b↦1⟩ "b" ==? just 1)
    , ok "lookup? ⟨a↦0,b↦1⟩ c" (lookup? ⟨a↦0,b↦1⟩ "c" ==? nothing)
    , ok "lookup? ⟨a↦j0⟩ a" (lookup? ⟨a↦j0⟩ "a" ==?? just (just 0))
    , ok "lookup? ⟨a↦n⟩ a" (lookup? ⟨a↦n⟩ "a" ==?? just nothing) )
  , test "map" 
    ( ok "map suc ⟨⟩" (map suc ⟨⟩ ==* ⟨⟩)
    , ok "map suc ⟨a↦0⟩" (map suc ⟨a↦0⟩ ==* ⟨a↦1⟩)
    , ok "map suc ⟨a↦0,b↦1⟩" (map suc ⟨a↦0,b↦1⟩ ==* ⟨a↦1,b↦2⟩)
    , ok "incr ⟨⟩" (map suc ⟨⟩ ==* incr ⟨⟩)
    , ok "incr ⟨a↦0⟩" (map suc ⟨a↦0⟩ ==* incr ⟨a↦0⟩)
    , ok "incr ⟨a↦0,b↦1⟩" (map suc ⟨a↦0,b↦1⟩ ==* incr ⟨a↦0,b↦1⟩) )
  , test "filter" 
    ( ok "filter 0< ⟨a↦1,b↦2⟩" (filter (_<_ 0) ⟨a↦1,b↦2⟩ ==* ⟨a↦1,b↦2⟩)
    , ok "filter 1< ⟨a↦1,b↦2⟩" (filter (_<_ 1) ⟨a↦1,b↦2⟩ ==* ⟨b↦2⟩)
    , ok "filter 2< ⟨a↦1,b↦2⟩" (filter (_<_ 2) ⟨a↦1,b↦2⟩ ==* ⟨⟩) ) )
