module FRP.JS.Level where

infixl 6 _⊔_

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# COMPILED_JS zero 0 #-}
{-# COMPILED_JS suc  function(x) { return x + 1; } #-}
{-# COMPILED_JS _⊔_  function(x) { return function(y) { return Math.max(x,y); }; } #-}

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}
