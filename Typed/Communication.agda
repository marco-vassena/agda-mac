module Typed.Communication where

open import Typed.Base

-- My own bulleted naturals
data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ
  ∙ : ℕ

data Event : Set where
  NoStep : Event
  Step : Event 
  Done : Event
  Fork : Label -> ℕ -> Event 
  

record Message : Set where
  constructor _,_,_
  field getLabel : Label
  field getThread# : ℕ
  field getEvent : Event 
