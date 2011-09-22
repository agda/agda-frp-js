open import FRP.JS.Behaviour using ( Beh ; [_] ; map )
open import FRP.JS.Event using ( Evt ; tag )
open import FRP.JS.DOM using
  ( DOM ; click ; element ; text ; _++_ ; element+ ; text+ ; listen+ ; _+++_ )
open import FRP.JS.RSet using ( RSet ; ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.Product using ( _∧_ ; _,_ )
open import FRP.JS.Demo.Calculator.Model using 
  ( Button ; State ; digit ; op ; clear ; eq ; plus ; minus ; times ; button$ ; state$ ; model )

module FRP.JS.Demo.Calculator.View where

button : ∀ {w} → Button → ⟦ Beh (DOM w) ∧ Evt ⟨ Button ⟩ ⟧
button b = listen+ click (λ _ → b) (element+ "button" (text+ [ button$ b ]))

keypad : ∀ {w} → ⟦ Beh (DOM w) ∧ Evt ⟨ Button ⟩ ⟧
keypad =
  element+ "div" (button (digit 7) +++ button (digit 8)  +++ button (digit 9) ) +++
  element+ "div" (button (digit 4) +++ button (digit 5)  +++ button (digit 6) ) +++
  element+ "div" (button (digit 1) +++ button (digit 2)  +++ button (digit 3) ) +++
  element+ "div" (button (op eq)   +++ button (digit 0)  +++ button clear     ) +++
  element+ "div" (button (op plus) +++ button (op minus) +++ button (op times))

display : ∀ {w} → ⟦ Beh ⟨ State ⟩ ⇒ Beh (DOM w) ⟧
display σ = element "div" (text (map state$ σ))

view : ∀ {w} → ⟦ Beh (DOM w) ⟧
view with keypad
... | (dom , evt) = display (model evt) ++ dom