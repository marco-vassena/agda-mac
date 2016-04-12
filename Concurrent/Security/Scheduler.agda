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

-- The proof that eventually the scheduler will trigger the message m
data Confluent {l} (m : Message l) (lₐ : Label) (s : State) (sᶠ : State) : ℕ -> Set where
  aligned : ∀ {s₂} -> s ⟶ s₂ ↑ m -> sᶠ ≈ˢ-⟨ lₐ ⟩ s₂  -> Confluent m lₐ s sᶠ 0
  high : ∀ {h n n'} -> ¬ (h ⊑ lₐ) -> (∀ {e} -> e ≢ ∙ -> ∃ (λ s₂ → s ⟶ s₂ ↑ ⟪ h , n , e ⟫ × Confluent m lₐ s sᶠ n')) -> Confluent m lₐ s sᶠ (suc n')

-- _,_⊢_⟶⋆_↑_ : ∀ {l} -> ℕ -> Label -> State -> State -> Message l -> Set
-- n , lₐ ⊢ s₁ ⟶⋆ s₂ ↑ m = Aligner m lₐ s₁ s₂ n
