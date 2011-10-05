open import FRP.JS.Nat using ( ℕ ; suc ; _+_ ; _==_ ; _<_ )
open import FRP.JS.Array using ( Array ; IArray ; [] ; _∷_ ; [_] ; ⟨⟩ ; ⟨_⟩ ; lookup ; lookup? ; map ; filter ; _==[_]_ ; _⊆[_]_ ; _++_ )
open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ) renaming ( _==[_]_ to _==?[_]_ )
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Array where

_==*_ : Array ℕ → Array ℕ → Bool
xs ==* ys = xs ==[ _==_ ] ys

_⊆*_ : Array ℕ → Array ℕ → Bool
xs ⊆* ys = xs ⊆[ _==_ ] ys

_==?_ : Maybe ℕ → Maybe ℕ → Bool
xs ==? ys = xs ==?[ _==_ ] ys

iincr : ∀ {m n} → IArray ℕ m n → IArray ℕ m n
iincr []       = []
iincr (n ∷ ns) = suc n ∷ iincr ns

incr : Array ℕ → Array ℕ
incr [ ns ] = [ iincr ns ]

⟨0⟩ = ⟨ 0 ⟩
⟨1⟩ = ⟨ 1 ⟩
⟨2⟩ = ⟨ 2 ⟩
⟨3⟩ = ⟨ 3 ⟩
⟨0,1⟩ = ⟨0⟩ ++ ⟨1⟩
⟨0,2⟩ = ⟨0⟩ ++ ⟨2⟩
⟨1,2⟩ = ⟨1⟩ ++ ⟨2⟩
⟨2,3⟩ = ⟨2⟩ ++ ⟨3⟩

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "⟨⟩ == ⟨⟩" (⟨⟩ ==* ⟨⟩) 
    , ok "⟨⟩ == ⟨0⟩" (not (⟨⟩ ==* ⟨0⟩))
    , ok "⟨0⟩ == ⟨⟩" (not (⟨0⟩ ==* ⟨⟩))
    , ok "⟨0⟩ == ⟨0⟩" (⟨0⟩ ==* ⟨0⟩)
    , ok "⟨⟩ == ⟨0,1⟩" (not (⟨⟩ ==* ⟨0,1⟩))
    , ok "⟨0,1⟩ == ⟨⟩" (not (⟨0,1⟩ ==* ⟨⟩))
    , ok "⟨1⟩ == ⟨0,1⟩" (not (⟨1⟩ ==* ⟨0,1⟩))
    , ok "⟨0⟩ == ⟨0,1⟩" (not (⟨0⟩ ==* ⟨0,1⟩))
    , ok "⟨0,1⟩ == ⟨0,1⟩" (⟨0,1⟩ ==* ⟨0,1⟩)
    , ok "⟨0,1⟩ == ⟨0,2⟩" (not (⟨0,1⟩ ==* ⟨0,2⟩))
    , ok "⟨0,1⟩ == ⟨1,2⟩" (not (⟨0,1⟩ ==* ⟨1,2⟩)) )
  , test "⊆" 
    ( ok "⟨⟩ ⊆ ⟨⟩" (⟨⟩ ⊆* ⟨⟩) 
    , ok "⟨⟩ ⊆ ⟨0⟩" (⟨⟩ ⊆* ⟨0⟩)
    , ok "⟨0⟩ ⊆ ⟨⟩" (not (⟨0⟩ ⊆* ⟨⟩))
    , ok "⟨0⟩ ⊆ ⟨0⟩" (⟨0⟩ ⊆* ⟨0⟩)
    , ok "⟨⟩ ⊆ ⟨0,1⟩" (⟨⟩ ⊆* ⟨0,1⟩)
    , ok "⟨0,1⟩ ⊆ ⟨⟩" (not (⟨0,1⟩ ⊆* ⟨⟩))
    , ok "⟨1⟩ ⊆ ⟨0,1⟩" (not (⟨1⟩ ⊆* ⟨0,1⟩))
    , ok "⟨0⟩ ⊆ ⟨0,1⟩" (⟨0⟩ ⊆* ⟨0,1⟩)
    , ok "⟨0,1⟩ ⊆ ⟨0,1⟩" (⟨0,1⟩ ⊆* ⟨0,1⟩)
    , ok "⟨0,1⟩ ⊆ ⟨0,2⟩" (not (⟨0,1⟩ ⊆* ⟨0,2⟩))
    , ok "⟨0,1⟩ ⊆ ⟨1,2⟩" (not (⟨0,1⟩ ⊆* ⟨1,2⟩)) )
  , test "lookup" 
    ( ok "lookup? ⟨1,2⟩ 0" (lookup? ⟨1,2⟩ 0 ==? just 1)
    , ok "lookup? ⟨1,2⟩ 1" (lookup? ⟨1,2⟩ 1 ==? just 2)
    , ok "lookup? ⟨1,2⟩ 2" (lookup? ⟨1,2⟩ 2 ==? nothing)
    , ok "lookup ⟨1,2⟩ 0" (lookup ⟨1,2⟩ 0 == 1)
    , ok "lookup ⟨1,2⟩ 1" (lookup ⟨1,2⟩ 1 == 2) )
  , test "map" 
    ( ok "map suc ⟨⟩" (map suc ⟨⟩ ==* ⟨⟩)
    , ok "map suc ⟨1⟩" (map suc ⟨1⟩ ==* ⟨2⟩)
    , ok "map suc ⟨1,2⟩" (map suc ⟨1,2⟩ ==* ⟨2,3⟩)
    , ok "incr ⟨⟩" (map suc ⟨⟩ ==* incr ⟨⟩)
    , ok "incr ⟨1⟩" (map suc ⟨1⟩ ==* incr ⟨1⟩)
    , ok "incr ⟨1,2⟩" (map suc ⟨1,2⟩ ==* incr ⟨1,2⟩) )
  , test "filter" 
    ( ok "filter 0< ⟨1,2⟩" (filter (_<_ 0) ⟨1,2⟩ ==* ⟨1,2⟩)
    , ok "filter 1< ⟨1,2⟩" (filter (_<_ 1) ⟨1,2⟩ ==* ⟨2⟩)
    , ok "filter 2< ⟨1,2⟩" (filter (_<_ 2) ⟨1,2⟩ ==* ⟨⟩) ) )
