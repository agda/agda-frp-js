module FRP.JS where

open import FRP.JS.Nat public using ( ℕ ; zero ; suc ; _+_ ; _*_ )
open import FRP.JS.DOM public using ( DOM ; text ; element ; [] ; _++_ )
open import FRP.JS.Time public using ( Time ; Delay ; _ms ; _sec ; _min ; every ; toUTCString )
open import FRP.JS.RSet public using ( RSet ; ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.Behaviour public using ( Beh ; [_] ) renaming ( map to mapB )
open import FRP.JS.Event public using ( Evt ) renaming ( map to mapE )
