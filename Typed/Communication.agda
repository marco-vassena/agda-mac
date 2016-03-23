module Typed.Communication where

open import Typed.Base
open import Data.Nat public

data Event (l : Label) : Set where
  NoStep : Event l
  Step : Event l
  Done : Event l 
  Fork : (h : Label) (n : ℕ) (p : l ⊑ h) -> Event l
  ∙ : Event l

data Message : Label -> Set where
   _,_,_ : (l : Label) -> (n : ℕ) -> Event l -> Message l
