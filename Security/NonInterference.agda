module Security.NonInterference where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_)
open import Typed.Proofs renaming (determinism to determinismᵗ)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)
open import Untyped.Proofs renaming (preservation to preservationᵘ)
open import Conversion.Proofs
open import Security.Distributivity
open import Relation.Binary.PropositionalEquality

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
data _≈ᵗ_ {{l : Label}} {τ : Ty} (c₁ c₂ : CTermᵗ τ) : Set where
  εᶜ-≡ : εᶜ l c₁ ≡ εᶜ l c₂ -> c₁ ≈ᵗ c₂

-- Non-interference for typed small step
-- As expected we need only determinism.
non-interferenceᵗ : ∀ {l τ} {c₁ c₂ c₁' c₂' : CTermᵗ τ} -> c₁ ≈ᵗ c₂ -> c₁ ⟼ᵗ c₁' -> c₂ ⟼ᵗ c₂' -> c₁' ≈ᵗ c₂'
non-interferenceᵗ {l} (εᶜ-≡ eq) s₁ s₂ = εᶜ-≡ (aux eq (εᶜ-distributes l s₁) (εᶜ-distributes l s₂))
  where aux : ∀ {τ} {c₁ c₂ c₃ c₄ : CTermᵗ τ} -> c₁ ≡ c₂ -> c₁ ⟼ᵗ c₃ -> c₂ ⟼ᵗ c₄ -> c₃ ≡ c₄
        aux refl s₁ s₂ = determinismᵗ s₁ s₂

data _≈ᵘ_ {{l : Label}} (c₁ c₂ : CTermᵘ) : Set where
  εᶜ-≡ : ∀ {τ} -> (p : c₁ :: τ) (q : c₂ :: τ) -> (⟪_⟫ c₁ {{p}}) ≈ᵗ (⟪_⟫ c₂ {{q}}) -> c₁ ≈ᵘ c₂

-- Main result, non-interference for untyped terms
-- Assuming that the two initial terms c₁ and c₂ are low-equivalent,
-- if they reduce to two terms c₁' and c₂', they are also low equivalent.
non-interferenceᵘ : ∀ {l} {c₁ c₂ c₁' c₂' : CTermᵘ} -> c₁ ≈ᵘ c₂ -> c₁ ⟼ᵘ c₁' -> c₂ ⟼ᵘ c₂' -> c₁' ≈ᵘ c₂'
non-interferenceᵘ (εᶜ-≡ p q eq) s₁ s₂ = εᶜ-≡ (preservationᵘ p s₁) (preservationᵘ q s₂) (non-interferenceᵗ eq step⟪ s₁ ⟫ step⟪ s₂ ⟫)
