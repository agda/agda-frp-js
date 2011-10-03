open import FRP.JS.Nat using ( ℕ ; suc ; _+_ ) renaming ( _==_ to _===_ )
open import FRP.JS.List using ( List ; [] ; _∷_ ; [_] ; _++_ ; map ; foldr ; foldl ; build ; _==[_]_ )
open import FRP.JS.Bool using ( Bool ; not )
open import FRP.JS.True using ()
open import FRP.JS.QUnit using ( TestSuite ; ok ; ok! ; test ; _,_ )

module FRP.JS.Test.List where

infixr 2 _==_

_==_ : List ℕ → List ℕ → Bool
xs == ys = xs ==[ _===_ ] ys

tests : TestSuite
tests = 
  ( test "==" 
    ( ok "[] == []" ([] == []) 
    , ok "[] == [0]" (not ([] == (0 ∷ [])))
    , ok "[0] == []" (not ((0 ∷ []) == []))
    , ok "[0] == [0]" ((0 ∷ []) == (0 ∷ []))
    , ok "[] == [0,1]" (not ([] == (0 ∷ 1 ∷ [])))
    , ok "[0,1] == []" (not ((0 ∷ 1 ∷ []) == []))
    , ok "[1] == [0,1]" (not ((1 ∷ []) == (0 ∷ 1 ∷ [])))
    , ok "[0] == [0,1]" (not ((0 ∷ []) == (0 ∷ 1 ∷ [])))
    , ok "[0,1] == [0,1]" ((0 ∷ 1 ∷ []) == (0 ∷ 1 ∷ [])) )
  , test "[_]" 
    ( ok "[1] == 1 ∷ []" ([ 1 ] == 1 ∷ []) 
    , ok "[1] == [0]" (not ([ 1 ] == [ 0 ])) )
  , test "++" 
    ( ok "[] ++ []" ([] ++ [] == [])
    , ok "[] ++ [1]" ([] ++ [ 1 ] == [ 1 ])
    , ok "[0] ++ []" ([ 0 ] ++ [] == [ 0 ])
    , ok "[0] ++ [1]" ([ 0 ] ++ [ 1 ] == 0 ∷ [ 1 ])
    , ok "[0] ++ [1] ++ [2]" ([ 0 ] ++ [ 1 ] ++ [ 2 ] == (0 ∷ 1 ∷ [ 2 ])) )
  , test "foldl" 
    ( ok "foldl + []" (foldl _+_ 0 [] === 0)
    , ok "foldl + [1]" (foldl _+_ 0 [ 1 ] === 1)
    , ok "foldl + [1,2]" (foldl _+_ 0 (1 ∷ [ 2 ]) === 3) )
  , test "foldr" 
    ( ok "foldr + []" (foldr _+_ 0 [] === 0)
    , ok "foldr + [1]" (foldr _+_ 0 [ 1 ] === 1)
    , ok "foldr + [1,2]" (foldr _+_ 0 (1 ∷ [ 2 ]) === 3) )
  , test "map" 
    ( ok "map suc []" (map suc [] == [])
    , ok "map suc [1]" (map suc [ 1 ] == [ 2 ])
    , ok "map suc [1,2]" (map suc (1 ∷ [ 2 ]) == 2 ∷ [ 3 ]) )
  , test "build" 
    ( ok "build suc 0" (build suc 0 == [])
    , ok "build suc 1" (build suc 1 == [ 1 ])
    , ok "build suc 2" (build suc 2 == 1 ∷ [ 2 ]) ) )
