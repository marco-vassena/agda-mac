-- Abstract definitions of schedulers

open import Lattice public

module Scheduler (𝓛 : Lattice) where

open Lattice.Lattice 𝓛

open import Data.Nat
--open import Data.Product using (∃) --TODO remove
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Event (l : Label) : Set where
  NoStep : Event l 
  Step : Event l 
  Done : Event l
  Fork : (h : Label) (n : ℕ) -> l ⊑ h -> Event l
  ∙ : Event l

-- Erasure of labeled events
εᴱ : ∀ {l} -> Label -> Event l -> Event l
εᴱ lₐ (Fork h n p) with h ⊑? lₐ
εᴱ lₐ (Fork h n p) | yes _ = Fork h n p
εᴱ lₐ (Fork h n p) | no ¬p = Step
εᴱ lₐ e = e

data Message : Label -> Set where
   _,_,_ : (l : Label) (n : ℕ) (e : Event l) -> Message l

-- Erasure of labeled messages
εᴹ : ∀ {l lₐ} -> Dec (l ⊑ lₐ) -> Message l -> Message l
εᴹ {._} {lₐ} (yes p) (l , n , e) = l , n , εᴱ lₐ e
εᴹ (no ¬p) (l , n , e) = l , n , ∙


record Scheduler : Set₁ where
  constructor Sch
  field
    State : Set
    _⟶_↑_ : ∀ {l} -> State -> State -> Message l -> Set
    εˢ  : Label -> State -> State
    ε-sch-dist : ∀ {s₁ s₂ l lₐ} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m -> (εˢ lₐ s₁) ⟶ (εˢ lₐ s₂) ↑ (εᴹ x m)
    ε-sch-≡ : ∀ {s₁ s₂ l lₐ} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (εˢ lₐ s₁) ≡ (εˢ lₐ s₂) -- TODO use low-equivalence
    deterministic-scheduler : ∀ {l n e} {s₁ s₂ s₃ : State} -> s₁ ⟶ s₂ ↑ (l , n , e) -> s₁ ⟶ s₃ ↑ (l , n , e) -> s₂ ≡ s₃

    _≈ˢ-⟨_⟩_ : State -> Label -> State -> Set -- Low-equivalence data-type, TODO better name?
    _≈ˢ-⟨_~_~_⟩_ : State -> ℕ -> Label -> ℕ -> State -> Set 
    offset₁ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ℕ
    offset₂ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ℕ
    align : ∀ {lₐ s₁ s₂} -> (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq ~ lₐ ~ offset₂ eq ⟩ s₂
    forget : ∀ {lₐ s₁ s₂ n m} -> s₁ ≈ˢ-⟨ n ~ lₐ ~ m ⟩ s₂ -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂


open Scheduler
