module Typed.Event where

open import Typed.Base

-- TODO:
-- Do we actually need to produce l × n ?
-- The scheduler does know them already from the transition  s₁ ⟶ s₂ ↑ γ, specifically from s₁

data Event : Set where
  NoStep : Label -> ℕ -> Event
  Step : Label -> ℕ -> Event 
  Done : Label -> ℕ -> Event
  Fork : ∀ {l'} -> Label -> ℕ -> Thread l' -> Event
  

