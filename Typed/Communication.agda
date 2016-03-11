module Typed.Communication where

open import Typed.Base

data Event : Set where
  NoStep : Event
  Step : Event 
  Done : Event
  Fork : ∀ {l} -> Thread l -> Event
  

record Message : Set where
  constructor _,_,_
  field getLabel : Label
  field getThread# : ℕ
  field getEvent : Event 
