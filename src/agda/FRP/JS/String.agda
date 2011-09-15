module FRP.JS.String where

-- Data.String doesn't have bindings for JavaScript, so we define String here.

postulate
  String : Set

{-# BUILTIN STRING String #-}
