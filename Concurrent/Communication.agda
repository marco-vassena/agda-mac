module Concurrent.Communication where

open import Types public
open import Data.Nat

data Event (l : Label) : Set where
  NoStep : Event l 
  Step : Event l 
  Done : Event l
  Fork : (h : Label) (n : ℕ) -> l ⊑ h -> Event l
  ∙ : Event l

data Message : Label -> Set where
   _,_,_ : (l : Label) (n : ℕ) (e : Event l) -> Message l
