open import FRP.JS.Bool using ( Bool ; true ; false )

module FRP.JS.Maybe where

-- Data.Maybe doesn't have bindings for JavaScript, so we define Maybe here.

-- We'd like to use JavaScript's built-in null as the
-- representation of nothing, and use x as the representation of just
-- x.  Unfortunately this doens't work for nested Maybes, as it
-- identifies nothing and just nothing at type Maybe Maybe A, which in
-- turn breaks parametericity. Instead, we link to a JS library which
-- provides functions box and unbox such that box(x) !== null,
-- unbox(box(x)) === x, and if x !== box^n (null) then x ==
-- box(x). Note that for never-null types (e.g. String), values
-- of type Maybe T are either null or values of type T, which
-- corresponds to the JavaScript idiom (for example, a lookup in an
-- array of strings can be translated to native array lookup).

data Maybe {α} (A : Set α) : Set α where
  just : (a : A) → Maybe A
  nothing : Maybe A

{-# COMPILED_JS Maybe function(x,v) { 
  if (x === null) { return v.nothing(); } 
  else { return v.just(require("agda.box").unbox(x)); }
} #-}
{-# COMPILED_JS just require("agda.box").box #-}
{-# COMPILED_JS nothing null #-}

_==[_]_ : ∀ {α β A B} → Maybe {α} A → (A → B → Bool) → Maybe {β} B → Bool
just a  ==[ p ] just b  = p a b
just a  ==[ p ] nothing = false
nothing ==[ p ] just b  = false
nothing ==[ p ] nothing = true
