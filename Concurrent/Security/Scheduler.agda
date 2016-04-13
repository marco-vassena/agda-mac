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
  (offset₁ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ℕ)
  (offset₂ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ℕ)
  (align : ∀ {lₐ s₁ s₂} -> (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq ~ lₐ ~ offset₂ eq ⟩ s₂)
  
  where

open import Concurrent.Security.Erasure

-- Low equivalence
-- We will need this at some point 
-- _≈ˢ_ : {{lₐ : Label}} -> State -> State -> Set
-- _≈ˢ_ {{lₐ}} s₁ s₂ = (ε lₐ s₁) ≡ (ε lₐ s₂)

-- _≈ˢ-⟨_⟩_ : State -> Label -> State -> Set
-- s₁ ≈ˢ-⟨ lₐ ⟩ s₂ = s₁ ≈ˢ s₂

-- data CloseUpStep {h lₐ s₁ s₁'} (m : Message h) (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₁') : Set where
--   cus : ∀ {s₂'} -> s₁' ⟶ s₂' ↑ m -> (eq' : s₁ ≈ˢ-⟨ lₐ ⟩ s₂' ) -> offset eq > offset eq' -> CloseUpStep m eq

-- data Aligner {l lₐ s₁ s₁'} (m : Message l) (s₂ : State) (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₁') : Set where
--   aligned : ∀ {s₂'} ->  s₁' ⟶ s₂' ↑ m -> Aligner m s₂ eq
--   high : ∀ {h n} -> ¬ (h ⊑ lₐ) -> ({e : Event} -> e ≢ ∙ -> CloseUpStep ⟪ h , n , e ⟫ eq) -> Aligner m s₂ eq


_≈ˢ-⟨_,_⟩_ : ∀ {lₐ} -> State -> ℕ -> ℕ -> State -> Set
_≈ˢ-⟨_,_⟩_ {lₐ} s₁ n m s₂ = s₁ ≈ˢ-⟨ n ~ lₐ ~ m ⟩ s₂

-- s₁ ≈-⟨ suc n , lₐ , m ⟩ s₁'

open import Data.Product using (∃ ; _×_)
open import Data.Sum

data Aligned {l} (s₁ s₂ s₁' : State) (m : Message l) (lₐ : Label) : Set where
  low : ∀ {s₂'} -> s₁' ⟶ s₂' ↑ m -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' -> Aligned s₁ s₂ s₁' m lₐ

data HighStep (lₐ h : Label) (n : ℕ) (e : Event) (s₁ s₂ s₁' : State) (n₁ n₂ : ℕ) : Set where
  high : ∀ { s₂'} -> ¬ h ⊑ lₐ ->  s₁' ⟶ s₂' ↑ ⟪ h , n , e ⟫ -> s₁ ≈ˢ-⟨ n₁ ~ lₐ ~ n₂ ⟩ s₂' -> HighStep lₐ h n e s₁ s₂ s₁' n₁ n₂

