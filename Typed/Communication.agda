module Typed.Communication where

open import Typed.Base

data Event : Set where
  NoStep : Event
  Step : Event 
  Done : Event
  -- TODO The scheduler doesn't need the thread itself, but rather
  -- the position of the spawned thread in the pool
  Fork : ∀ {l} -> Thread l -> Event 
  

record Message : Set where
  constructor _,_,_
  field getLabel : Label
  field getThread# : ℕ
  field getEvent : Event 
