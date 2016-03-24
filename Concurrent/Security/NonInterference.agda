open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure

module Concurrent.Security.NonInterference
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε-state : Label -> State -> State) -- Erasure function of the scheduler state
  (ε-sch-dist : ∀ {s₁ s₂ l lₐ} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ⟶ (ε-state lₐ s₂) ↑ (εᴹ x m))
  (ε-sch-≡ : ∀ {s₁ s₂ l lₐ} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ≡ (ε-state lₐ s₂))

  (deterministic-scheduler : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃ )

  where


open import Concurrent.Determinism State _⟶_↑_ deterministic-scheduler
open import Concurrent.Security.Distributivity State _⟶_↑_ ε-state ε-sch-dist ε-sch-≡
open import Concurrent.Semantics State _⟶_↑_


-- Global l-equivalence

data _≈ᵍ_ {{lₐ : Label}} {ls : List Label} (g₁ g₂ : Global ls) : Set where
  εᵍ-≡ : εᵍ lₐ g₁ ≡ εᵍ lₐ g₂ -> g₁ ≈ᵍ g₂

unlift-≈ᵍ : ∀ {lₐ ls} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ g₂ -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂
unlift-≈ᵍ (εᵍ-≡ x) = x

simulation↪ : ∀ {ls l n} {{lₐ : Label}} {g₁ g₂ g₁' g₂' : Global ls} ->
                    g₁ ≈ᵍ g₂ ->
                    l , n ⊢ g₁ ↪ g₁' ->
                    l , n ⊢ g₂ ↪ g₂' ->
                    g₁' ≈ᵍ g₂'
simulation↪ {{lₐ}} p s₁ s₂ = εᵍ-≡ (aux (unlift-≈ᵍ p) (εᵍ-dist lₐ s₁) (εᵍ-dist lₐ s₂))
  where aux : ∀ {ls l n} {t₁ t₂ t₃ t₄ : Global ls} -> t₁ ≡ t₂ -> l , n ⊢ t₁ ↪ t₃ -> l , n ⊢ t₂ ↪ t₄ -> t₃ ≡ t₄
        aux refl s₁ s₂ = determinism↪ s₁ s₂
