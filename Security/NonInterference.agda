module Security.NonInterference where

open import Typed.Semantics
open import Typed.Proofs
open import Security.Distributivity
open import Relation.Binary.PropositionalEquality

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
data _≈ˡ_ {{l : Label}} {τ : Ty} (c₁ c₂ : CTerm τ) : Set where
  εᶜ-≡ : εᶜ l c₁ ≡ εᶜ l c₂ -> c₁ ≈ˡ c₂

-- Non-interference
-- As expected we need only determinism.
non-interference : ∀ {l τ} {c₁ c₂ c₁' c₂' : CTerm τ} -> c₁ ≈ˡ c₂ -> c₁ ⟼ c₁' -> c₂ ⟼ c₂' -> c₁' ≈ˡ c₂'
non-interference {l} (εᶜ-≡ eq) s₁ s₂ = εᶜ-≡ (aux eq (εᶜ-distributes l s₁) (εᶜ-distributes l s₂))
  where aux : ∀ {τ} {c₁ c₂ c₃ c₄ : CTerm τ} -> c₁ ≡ c₂ -> c₁ ⟼ c₃ -> c₂ ⟼ c₄ -> c₃ ≡ c₄
        aux refl s₁ s₂ = determinism s₁ s₂
