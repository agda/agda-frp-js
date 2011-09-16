open import FRP.JS.Bool using ( Bool )

module FRP.JS.String where

infixr 5 _++_
infix 4 _==_

-- Data.String doesn't have bindings for JavaScript, so we define String here.

postulate
  String : Set

{-# BUILTIN STRING String #-}

private
 primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

_++_ : String → String → String
_++_ = primStringAppend

{-# COMPILED_JS _++_ function(x) { return function(y) { return x + y; }; } #-}

_==_ : String → String → Bool
_==_ = primStringEquality

{-# COMPILED_JS _==_ function(x) { return function(y) { return x === y; }; } #-}
