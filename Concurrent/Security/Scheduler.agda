open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure
open import Data.Product

module Concurrent.Security.Scheduler
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε : Label -> State -> State) -- Erasure function of the scheduler state
  where

open import Concurrent.Security.Erasure

-- Low equivalence
_≈ˢ_ : {{lₐ : Label}} -> State -> State -> Set
_≈ˢ_ {{lₐ}} s₁ s₂ = (ε lₐ s₁) ≡ (ε lₐ s₂)

_≈ˢ-⟨_⟩_ : State -> Label -> State -> Set
s₁ ≈ˢ-⟨ lₐ ⟩ s₂ = s₁ ≈ˢ s₂


data Aligner {l} (m : Message l) (lₐ : Label) (s₁ : State) : State -> ℕ -> Set where
  aligned : ∀ {s₂} -> s₁ ⟶ s₂ ↑ m -> Aligner m lₐ s₁ s₂ 0
  high : ∀ {h n n' s₃} -> ¬ (h ⊑ lₐ) -> ((e : Event) -> ∃ (λ s₂ → s₁ ⟶ s₂ ↑ ⟪ h , n , e ⟫ × Aligner m lₐ s₂ s₃ n')) -> Aligner m lₐ s₁ s₃ (suc n')


_,_⊢_⟶⋆_↑_ : ∀ {l} -> ℕ -> Label -> State -> State -> Message l -> Set
n , lₐ ⊢ s₁ ⟶⋆ s₂ ↑ m = Aligner m lₐ s₁ s₂ n
