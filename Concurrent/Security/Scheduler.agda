open import Lattice
open import Scheduler using (Scheduler)
open import Relation.Binary.PropositionalEquality

module Concurrent.Security.Scheduler (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Types 𝓛
open import Scheduler 𝓛
open Scheduler.Scheduler 𝓛 𝓢

open import Concurrent.Security.Erasure

open import Data.Nat


_≈ˢ-⟨_,_⟩_ : ∀ {lₐ} -> State -> ℕ -> ℕ -> State -> Set
_≈ˢ-⟨_,_⟩_ {lₐ} s₁ n m s₂ = s₁ ≈ˢ-⟨ n ~ lₐ ~ m ⟩ s₂

data Aligned {l} (s₁ s₂ s₁' : State) (m : Message l) (lₐ : Label) : Set where
  low : ∀ {s₂'} -> s₁' ⟶ s₂' ↑ m -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' -> Aligned s₁ s₂ s₁' m lₐ

data HighStep (lₐ h : Label) (n : ℕ) (e : Event h) (s₁ s₂ s₁' : State) (n₁ n₂ : ℕ) : Set where
  high : ∀ { s₂'} -> ¬ h ⊑ lₐ ->  s₁' ⟶ s₂' ↑ (h , n , e) -> s₁ ≈ˢ-⟨ n₁ ~ lₐ ~ n₂ ⟩ s₂' -> HighStep lₐ h n e s₁ s₂ s₁' n₁ n₂
