module Concurrent.Calculus (State : Set) where

open import Data.List
open import Sequential -- TODO remove

-- Define here Pools!

-------------------------------------------------------------------------------
-- The global configuration is a thread pool paired with some shared split memory Σ
data Global (ls : List Label) : Set where
  ⟨_,_,_⟩ : State -> (Σ : Store ls) -> (ps : Pools ls) -> Global ls
 
