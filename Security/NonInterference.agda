module Security.NonInterference where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⇝_ to _⇝ᵗ_)
open import Typed.Proofs renaming (determinism⇝ to determinismᵗ)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⇝_ to _⇝ᵘ_)
open import Untyped.Proofs renaming (preservation⇝ to preservationᵘ)
open import Conversion.Proofs
open import Security.Distributivity
open import Relation.Binary.PropositionalEquality

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
data _≈ᵗ_ {{l : Label}} {τ : Ty} (c₁ c₂ : CTermᵗ τ) : Set where
  εᶜ-≡ : εᶜ l c₁ ≡ εᶜ l c₂ -> c₁ ≈ᵗ c₂

-- Non-interference for typed terms.
-- As expected we need only determinism of the small step semantics and distributivity of εᶜ.
non-interferenceᵗ : ∀ {l τ} {c₁ c₂ c₁' c₂' : CTermᵗ τ} -> c₁ ≈ᵗ c₂ -> c₁ ⇝ᵗ c₁' -> c₂ ⇝ᵗ c₂' -> c₁' ≈ᵗ c₂'
non-interferenceᵗ {l} (εᶜ-≡ eq) s₁ s₂ = εᶜ-≡ (aux eq (εᶜ-dist l s₁) (εᶜ-dist l s₂))
  where aux : ∀ {τ} {c₁ c₂ c₃ c₄ : CTermᵗ τ} -> c₁ ≡ c₂ -> c₁ ⇝ᵗ c₃ -> c₂ ⇝ᵗ c₄ -> c₃ ≡ c₄
        aux refl s₁ s₂ = determinismᵗ s₁ s₂

-- Non-interference for untyped terms
-- Assuming that the two initial terms c₁ and c₂ are low-equivalent,
-- if they reduce to two terms c₁' and c₂', they are also low equivalent.
-- 
-- The theorem more formally says that given:
-- c₁ :: τ , c₂ :: τ, ⟪ c₁ ⟫ ≈ᵗ ⟪ c₂ ⟫, c₁ ⟼ᵘ c₁', c₂ ⟼ᵘ c₂'
-- then
-- ⟪ c₁' ⟫ ≈ᵗ ⟪ c₂' ⟫
non-interferenceᵘ : ∀ {l} {τ : Ty} {c₁ c₂ c₁' c₂' : CTermᵘ} -> 
                      (p₁ : c₁ :: τ) (p₂ : c₂ :: τ) -> (⟪_⟫ c₁ {{p₁}}) ≈ᵗ (⟪_⟫ c₂ {{p₂}}) -> 
                      (s₁ : c₁ ⇝ᵘ c₁') (s₂ : c₂ ⇝ᵘ c₂') -> 
                      let q₁ = preservationᵘ p₁ s₁
                          q₂ = preservationᵘ p₂ s₂ in (⟪_⟫ c₁' {{q₁}}) ≈ᵗ (⟪_⟫  c₂' {{q₂}})
non-interferenceᵘ p₁ p₂ eq s₁ s₂ = non-interferenceᵗ eq step⟪ s₁ ⟫ step⟪ s₂ ⟫
