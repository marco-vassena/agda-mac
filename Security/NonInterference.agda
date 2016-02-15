module Security.NonInterference where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_ ; Program to Programᵗ)
open import Typed.Proofs renaming (determinism to determinismᵗ)
-- open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
-- open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)
-- open import Untyped.Proofs renaming (preservation to preservationᵘ)
-- open import Conversion.Proofs
open import Security.Distributivity
open import Relation.Binary.PropositionalEquality

-- Low Equivalence
-- Two terms are low equivalent if they are equivalent after erasing them with label l.
data _≈ᵗ_ {{l : Label}} {ls : List Label} {τ : Ty} (p₁ p₂ : Programᵗ ls τ) : Set where
  ε-≡ : εᵖ l p₁ ≡ εᵖ l p₂ -> p₁ ≈ᵗ p₂

-- Non-interference for typed terms:
--
-- p₁ ≈ᵗ p₂ , p₁ ⟼ᵗ p₁' , p₂ ⟼ᵗ p₂'
-- then
-- p₁' ≈ᵗ p₂' 
--
-- By distributivity of ε the reductions steps are mapped in reductions of the erased terms:
-- p₁ ⟼ᵗ p₁'     to      (ε lₐ p₁) ⟼ᵗ (ε lₐ p₁')
-- p₂ ⟼ᵗ p₂'     to      (ε lₐ p₂) ⟼ᵗ (ε lₐ p₂')
-- Since the source terms are equivalent (ε lₐ p₁ ≡ ε lₐ p₂) by definition of low equivalence (p₁ ≈ᵗ p₂)
-- and the semantics is deterministic then the reduced erased terms are equivalent (ε lₐ p₁' ≡ ε lₐ p₂')
-- This implies that p₁' and p₂' are low-equivalent (p₁ ≈ᵗ p₂).
non-interferenceᵗ : ∀ {l ls τ} {p₁ p₂ p₁' p₂' : Programᵗ ls τ} -> p₁ ≈ᵗ p₂ -> p₁ ⟼ᵗ p₁' -> p₂ ⟼ᵗ p₂' -> p₁' ≈ᵗ p₂'
non-interferenceᵗ {l} (ε-≡ eq) s₁ s₂ = ε-≡ (aux eq (εᵖ-dist l s₁) (εᵖ-dist l s₂))
  where aux : ∀ {τ ls} {p₁ p₂ p₃ p₄ : Programᵗ ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ᵗ p₃ -> p₂ ⟼ᵗ p₄ -> p₃ ≡ p₄
        aux refl s₁ s₂ = determinismᵗ s₁ s₂

-- Non-interference for untyped terms
-- Assuming that the two initial terms c₁ and c₂ are low-equivalent,
-- if they reduce to two terms c₁' and c₂', they are also low equivalent.
-- 
-- The theorem more formally says that given:
-- c₁ :: τ , c₂ :: τ, ⟪ c₁ ⟫ ≈ᵗ ⟪ c₂ ⟫, c₁ ⟼ᵘ c₁', c₂ ⟼ᵘ c₂'
-- then
-- ⟪ c₁' ⟫ ≈ᵗ ⟪ c₂' ⟫
-- non-interferenceᵘ : ∀ {l} {τ : Ty} {c₁ c₂ c₁' c₂' : CTermᵘ} -> 
--                       (p₁ : c₁ :: τ) (p₂ : c₂ :: τ) -> (⟪_⟫ c₁ {{p₁}}) ≈ᵗ (⟪_⟫ c₂ {{p₂}}) -> 
--                       (s₁ : c₁ ⟼ᵘ c₁') (s₂ : c₂ ⟼ᵘ c₂') -> 
--                       let q₁ = preservationᵘ p₁ s₁
--                           q₂ = preservationᵘ p₂ s₂ in (⟪_⟫ c₁' {{q₁}}) ≈ᵗ (⟪_⟫  c₂' {{q₂}})
-- non-interferenceᵘ p₁ p₂ eq s₁ s₂ = non-interferenceᵗ eq step⟪ s₁ ⟫ step⟪ s₂ ⟫
