open import FRP.JS.Nat using ( ℕ ; suc ; _+_ ; _==_ )
open import FRP.JS.Array using ( Array ; IArray ; [] ; _∷_ ; [_] ; lookup? ; map ; _==[_]_ )
open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.Maybe using ( Maybe ; just ; nothing ) renaming ( _==[_]_ to _==?[_]_ )
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.Array where

_==*_ : Array ℕ → Array ℕ → Bool
xs ==* ys = xs ==[ _==_ ] ys

_==?_ : Maybe ℕ → Maybe ℕ → Bool
xs ==? ys = xs ==?[ _==_ ] ys

iincr : ∀ {m n} → IArray ℕ m n → IArray ℕ m n
iincr []       = []
iincr (n ∷ ns) = suc n ∷ iincr ns

incr : Array ℕ → Array ℕ
incr [ ns ] = [ iincr ns ]

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "[] == []" ([ [] ] ==* [ [] ]) 
    , ok "[] == [0]" (not ([ [] ] ==* [ 0 ∷ [] ]))
    , ok "[0] == []" (not ([ 0 ∷ [] ] ==* [ [] ]))
    , ok "[0] == [0]" ([ 0 ∷ [] ] ==* [ 0 ∷ [] ])
    , ok "[] == [0,1]" (not ([ [] ] ==* [ 0 ∷ 1 ∷ [] ]))
    , ok "[0,1] == []" (not ([ 0 ∷ 1 ∷ [] ] ==* [ [] ]))
    , ok "[1] == [0,1]" (not ([ 1 ∷ [] ] ==* [ 0 ∷ 1 ∷ [] ]))
    , ok "[0] == [0,1]" (not ([ 0 ∷ [] ] ==* [ 0 ∷ 1 ∷ [] ]))
    , ok "[0,1] == [0,1]" ([ 0 ∷ 1 ∷ [] ] ==* [ 0 ∷ 1 ∷ [] ]) )
  , test "lookup?" 
    ( ok "lookup? [1,2] 0" (lookup? [ 1 ∷ 2 ∷ [] ] 0 ==? just 1)
    , ok "lookup? [1,2] 1" (lookup? [ 1 ∷ 2 ∷ [] ] 1 ==? just 2)
    , ok "lookup? [1,2] 2" (lookup? [ 1 ∷ 2 ∷ [] ] 2 ==? nothing) )
  , test "map" 
    ( ok "map suc []" (map suc [ [] ] ==* [ [] ])
    , ok "map suc [1]" (map suc [ 1 ∷ [] ] ==* [ 2 ∷ [] ])
    , ok "map suc [1,2]" (map suc ([ 1 ∷ 2 ∷ [] ]) ==* [ 2 ∷ 3 ∷ [] ])
    , ok "incr []" (map suc [ [] ] ==* incr [ [] ])
    , ok "incr [1]" (map suc [ 1 ∷ [] ] ==* incr [ 1 ∷ [] ])
    , ok "incr [1,2]" (map suc ([ 1 ∷ 2 ∷ [] ]) ==* incr [ 1 ∷ 2 ∷ [] ]) ) )
