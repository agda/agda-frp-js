open import FRP.JS.Behaviour using ( Beh ; [_] ; map ; accumHoldBy )
open import FRP.JS.Event using ( Evt ; tag )
open import FRP.JS.DOM using ( DOM ; element ; text ; listen ; click ; _++_ ; element+ ; _+++_ )
open import FRP.JS.RSet using ( RSet ; ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.Nat using ( ℕ ; _+_ ; _*_ ; _∸_ )
open import FRP.JS.Nat.Show using ( show )
open import FRP.JS.Time using ( Time )
open import FRP.JS.String using ( String )
open import FRP.JS.Bool using ( Bool ; true ; false )
open import FRP.JS.Product using ( _∧_ ; _,_ )

module FRP.JS.Demo.Calculator.Model where

data Op : Set where
  plus minus times eq : Op

data Button : Set where
  digit : ℕ → Button
  op : Op → Button
  clear : Button

data State : Set where
  state : ℕ → ℕ → Bool → Op → State

init : State
init = state 0 0 false eq

eval : ℕ → Op → ℕ → ℕ
eval m plus  n = m + n
eval m minus n = m ∸ n
eval m times n = m * n
eval m eq    n = n

step : State → Button → State
step (state m n true  p) (digit d) = state m (n * 10 + d) true  p
step (state m n false p) (digit d) = state n d            true  p
step (state m n true  p) (op q)    = state n (eval m p n) false q
step (state m n false p) (op q)    = state m (eval m p n) false q
step (state m n b     p) clear     = state 0 0            false eq

button$ : Button → String
button$ (digit d)   = show d
button$ (op plus)   = "+"
button$ (op minus)  = "-"
button$ (op times)  = "×"
button$ (op eq)     = "="
button$ clear       = "C"

state$ : State → String
state$ (state m n b p) = show n

model : ⟦ Evt ⟨ Button ⟩ ⇒ Beh ⟨ State ⟩ ⟧
model = accumHoldBy step init