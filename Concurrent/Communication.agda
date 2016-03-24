module Concurrent.Communication where

open import Types
open import Data.Nat public

data Event : Set where
  NoStep : Event
  Step : Event
  Done : Event
  Fork : (h : Label) (n : ℕ) -> Event
  ∙ : Event

data Message : Label -> Set where
   _,_,_ : (l : Label) (n : ℕ) (e : Event) -> Message l
