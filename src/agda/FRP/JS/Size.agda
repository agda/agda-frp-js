module FRP.JS.Size where

postulate
  Size : Set
  ↑_   : Size → Size
  ∞    : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ↑_   #-}
{-# BUILTIN SIZEINF ∞    #-}
{-# COMPILED_JS     ↑_ function(x) { return null; } #-}
{-# COMPILED_JS     ∞  null #-}
