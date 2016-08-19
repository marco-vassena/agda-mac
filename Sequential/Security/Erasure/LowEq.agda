module Sequential.Security.Erasure.LowEq where

open import Sequential.Semantics
open import Sequential.Security.Erasure.Base
open import Sequential.Security.Erasure.Graph

open import Relation.Binary.PropositionalEquality using (refl ; _≡_ ; sym ; trans) public
open import Relation.Binary.PropositionalEquality

open Program

--------------------------------------------------------------------------------
-- Store low-equivalnce

data _≈ˢ_ {{lₐ : Label}} {ls : List Label} (Σ₁ Σ₂ : Store ls) : Set where
  εˢ-≡ : εˢ lₐ Σ₁ ≡ εˢ lₐ Σ₂ -> Σ₁ ≈ˢ Σ₂

refl-≈ˢ : ∀ {l ls} {s : Store ls} -> s ≈ˢ s
refl-≈ˢ = εˢ-≡ refl

sym-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ : Store ls} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₁
sym-≈ˢ (εˢ-≡ x) = εˢ-≡ (sym x)

trans-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ s₃ : Store ls} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ s₃ -> Σ₁ ≈ˢ s₃
trans-≈ˢ (εˢ-≡ x) (εˢ-≡ x₁) = εˢ-≡ (trans x x₁)

_≈ˢ-⟨_⟩_ : ∀ {ls} -> Store ls -> Label -> Store ls -> Set
s₁ ≈ˢ-⟨ lₐ ⟩ s₂ = s₁ ≈ˢ s₂

--------------------------------------------------------------------------------
-- Term low-equivalence

data _≈_ {{lₐ : Label}} {Δ : Context} {τ : Ty} (t₁ t₂ : Term Δ τ) : Set where
  ε-≡ : ε lₐ t₁ ≡ ε lₐ t₂ -> t₁ ≈ t₂

refl-≈ : ∀ {l Δ τ} {t : Term Δ τ} -> t ≈ t
refl-≈ = ε-≡ refl

sym-≈ : ∀ {l Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈ t₂ -> t₂ ≈ t₁
sym-≈ (ε-≡ x) = ε-≡ (sym x)

trans-≈ : ∀ {l Δ τ} {t₁ t₂ t₃ : Term Δ τ} -> t₁ ≈ t₂ -> t₂ ≈ t₃ -> t₁ ≈ t₃
trans-≈ (ε-≡ x) (ε-≡ x₁) = ε-≡ (trans x x₁)

_≈-⟨_⟩_ : ∀ {τ Δ}  -> Term Δ τ -> Label -> Term Δ τ -> Set
t₁ ≈-⟨ lₐ ⟩ t₂ = t₁ ≈ t₂

--------------------------------------------------------------------------------
-- Program Low Equivalence

-- It is convenient for reasoning to define directly the equivalence of two programs as the low-equivalence
-- of their stores and terms. This is still equivalent to εᵖ lₐ p₁ ≡ εᵖ lₐ p₂
data _≈ᵖ_ {{l : Label}} {ls : List Label} {τ : Ty} (p₁ p₂ : Program ls τ) : Set where
  εᵖ-≡ : store p₁ ≈ˢ store p₂ -> term p₁ ≈ term p₂ -> p₁ ≈ᵖ p₂

_≈ᵖ-⟨_⟩_ : ∀ {τ ls} -> Program ls τ -> Label -> Program ls τ -> Set
p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ = p₁ ≈ᵖ p₂

refl-≈ᵖ : ∀ {l τ ls} {p : Program ls τ} -> p ≈ᵖ p
refl-≈ᵖ {p = p} = εᵖ-≡ refl-≈ˢ refl-≈ -- εᵖ-≡ ? ? 

sym-≈ᵖ : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₁
sym-≈ᵖ (εᵖ-≡ x y) = εᵖ-≡ (sym-≈ˢ x) (sym-≈ y) --  εᵖ-≡ (sym x)

trans-≈ᵖ : ∀ {l τ ls} {p₁ p₂ p₃ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₃ -> p₁ ≈ᵖ p₃
trans-≈ᵖ (εᵖ-≡ x₁ y₁) (εᵖ-≡ x₂ y₂) = εᵖ-≡ (trans-≈ˢ x₁ x₂) (trans-≈ y₁ y₂)

-- My definition of l-equivalence for programs corresponds to the equivalence of the erasure of two programs 
unlift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂
unlift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} (εᵖ-≡ (εˢ-≡ eq₁) (ε-≡ eq₂)) rewrite eq₁ | eq₂ = refl

lift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂ -> p₁ ≈ᵖ p₂
lift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} eq = εᵖ-≡ (εˢ-≡ (store-≡ eq)) (ε-≡ (term-≡ eq))

--------------------------------------------------------------------------------

-- Structural low-equivalence for reasoning more conveniently
data _≈′_ {{lₐ : Label}} {Δ : Context} {τ : Ty} (t₁ t₂ : Term Δ τ) : Set where
  LE : ∀ {t₁ᵉ t₂ᵉ} -> (e₁ : Erasure lₐ t₁ t₁ᵉ) (e₂ : Erasure lₐ t₂ t₂ᵉ) (eq : t₁ᵉ ≡ t₂ᵉ) -> t₁ ≈′ t₂


-- Equivalence between structural low-equivalence and propositional low-equivalence

≈′-≈ : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈′ t₂ -> t₁ ≈ t₂
≈′-≈ (LE e₁ e₂ eq) rewrite sym (Erasure-ε e₁) | sym (Erasure-ε e₂) = ε-≡ eq

≈-≈′ : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈ t₂ -> t₁ ≈′ t₂
≈-≈′ (ε-≡ x) = LE (ε-Erasure _) (ε-Erasure _) x

