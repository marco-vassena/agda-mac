open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure
open import Data.Product

module Concurrent.Security.Scheduler
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε : Label -> State -> State) -- Erasure function of the scheduler state
  (_≈ˢ-⟨_⟩_ : State -> Label -> State -> Set)
  (_≈ˢ-⟨_~_~_⟩_ : State -> ℕ -> Label -> ℕ -> State -> Set)
  where

open import Concurrent.Security.Erasure

_≈ˢ-⟨_,_⟩_ : ∀ {lₐ} -> State -> ℕ -> ℕ -> State -> Set
_≈ˢ-⟨_,_⟩_ {lₐ} s₁ n m s₂ = s₁ ≈ˢ-⟨ n ~ lₐ ~ m ⟩ s₂

data Aligned {l} (s₁ s₂ s₁' : State) (m : Message l) (lₐ : Label) : Set where
  low : ∀ {s₂'} -> s₁' ⟶ s₂' ↑ m -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' -> Aligned s₁ s₂ s₁' m lₐ

data HighStep (lₐ h : Label) (n : ℕ) (e : Event) (s₁ s₂ s₁' : State) (n₁ n₂ : ℕ) : Set where
  high : ∀ { s₂'} -> ¬ h ⊑ lₐ ->  s₁' ⟶ s₂' ↑ ⟪ h , n , e ⟫ -> s₁ ≈ˢ-⟨ n₁ ~ lₐ ~ n₂ ⟩ s₂' -> HighStep lₐ h n e s₁ s₂ s₁' n₁ n₂

