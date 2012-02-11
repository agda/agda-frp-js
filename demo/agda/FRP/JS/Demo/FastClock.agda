open import FRP.JS.String using ( String )
open import FRP.JS.Time using ( Time ; _+_ )
open import FRP.JS.Behaviour using ( Beh ; map ; [_] ; join )
open import FRP.JS.DOM using ( DOM ; text )
open import FRP.JS.RSet using ( ⟦_⟧; ⟨_⟩ )
open import FRP.JS.Time using ( toUTCString ; every )
open import FRP.JS.Delay using ( _sec ; _min )

module FRP.JS.Demo.FastClock where

model : ⟦ Beh ⟨ Time ⟩ ⟧
model = map (λ t → t + 5 min) (every (1 sec))

view : ∀ {w} → ⟦ Beh (DOM w) ⟧
view = join (map (λ t → text [ toUTCString t ]) model)

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = view
