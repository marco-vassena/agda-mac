open import Lattice

module Sequential.Security.Erasure.LowEq (𝓛 : Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Security.Erasure.Base 𝓛
open import Sequential.Security.Erasure.Graph 𝓛

open import Relation.Binary.PropositionalEquality

open Program

-- TODO make attacker level module parameter

--------------------------------------------------------------------------------
-- Store low-equivalnce

data _≈ˢ_ {lₐ : Label} {ls : List Label} (Σ₁ Σ₂ : Store ls) : Set where
  εˢ-≡ : εˢ lₐ Σ₁ ≡ εˢ lₐ Σ₂ -> Σ₁ ≈ˢ Σ₂

_≈ˢ-⟨_⟩_ : ∀ {ls} -> Store ls -> Label -> Store ls -> Set
s₁ ≈ˢ-⟨ lₐ ⟩ s₂ = _≈ˢ_ {lₐ} s₁ s₂

refl-≈ˢ : ∀ {l ls} {s : Store ls} -> s ≈ˢ-⟨ l ⟩ s
refl-≈ˢ = εˢ-≡ refl

sym-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ : Store ls} -> Σ₁ ≈ˢ-⟨ l ⟩ Σ₂ -> Σ₂ ≈ˢ Σ₁
sym-≈ˢ (εˢ-≡ x) = εˢ-≡ (sym x)

trans-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ s₃ : Store ls} -> Σ₁ ≈ˢ-⟨ l ⟩ Σ₂ -> Σ₂ ≈ˢ s₃ -> Σ₁ ≈ˢ s₃
trans-≈ˢ (εˢ-≡ x) (εˢ-≡ x₁) = εˢ-≡ (trans x x₁)


--------------------------------------------------------------------------------
-- Term low-equivalence

data _≈_ {lₐ : Label} {Δ : Context} {τ : Ty} (t₁ t₂ : Term Δ τ) : Set where
  ε-≡ : ε lₐ t₁ ≡ ε lₐ t₂ -> t₁ ≈ t₂

_≈-⟨_⟩_ : ∀ {τ Δ}  -> Term Δ τ -> Label -> Term Δ τ -> Set
t₁ ≈-⟨ lₐ ⟩ t₂ = _≈_ {lₐ} t₁ t₂

refl-≈ : ∀ {l Δ τ} {t : Term Δ τ} -> t ≈-⟨ l ⟩ t
refl-≈ = ε-≡ refl

sym-≈ : ∀ {l Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈-⟨ l ⟩ t₂ -> t₂ ≈ t₁
sym-≈ (ε-≡ x) = ε-≡ (sym x)

trans-≈ : ∀ {l Δ τ} {t₁ t₂ t₃ : Term Δ τ} -> t₁ ≈-⟨ l ⟩ t₂ -> t₂ ≈ t₃ -> t₁ ≈ t₃
trans-≈ (ε-≡ x) (ε-≡ x₁) = ε-≡ (trans x x₁)

data Structural≈  {Δ τ} (lₐ : Label) (t₁ t₂ : Term Δ τ) : Set where
  S-≈ : {tᵉ : Term Δ τ} -> Erasure lₐ t₁ tᵉ -> Erasure lₐ t₂ tᵉ -> Structural≈ lₐ t₁ t₂

-- Connection to Graph of the function to get a (sort of) cheap structural equivalence
≈-Structural : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈-⟨ lₐ ⟩ t₂ -> Structural≈ lₐ t₁ t₂ 
≈-Structural {lₐ} {t₁ = t₁} {t₂ = t₂} (ε-≡ eq) with  ε-Erasure {lₐ = lₐ} t₁ | ε-Erasure {lₐ = lₐ} t₂
... | a | b rewrite eq = S-≈ a b 

Structural-≈ : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> Structural≈ lₐ t₁ t₂ -> t₁ ≈-⟨ lₐ ⟩ t₂
Structural-≈ (S-≈ x y) with Erasure-ε x | Erasure-ε y
... | a | b = ε-≡ (trans a (sym b))

--------------------------------------------------------------------------------
-- Program Low Equivalence

-- It is convenient for reasoning to define directly the equivalence of two programs as the low-equivalence
-- of their stores and terms. This is still equivalent to εᵖ lₐ p₁ ≡ εᵖ lₐ p₂
data _≈ᵖ_ {l : Label} {ls : List Label} {τ : Ty} (p₁ p₂ : Program ls τ) : Set where
  εᵖ-≡ : store p₁ ≈ˢ-⟨ l ⟩ store p₂ -> term p₁ ≈-⟨ l ⟩ term p₂ -> p₁ ≈ᵖ p₂

_≈ᵖ-⟨_⟩_ : ∀ {τ ls} -> Program ls τ -> Label -> Program ls τ -> Set
p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ = _≈ᵖ_ {lₐ} p₁  p₂

refl-≈ᵖ : ∀ {l τ ls} {p : Program ls τ} -> p ≈ᵖ-⟨ l ⟩ p
refl-≈ᵖ {p = p} = εᵖ-≡ refl-≈ˢ refl-≈ -- εᵖ-≡ ? ? 

sym-≈ᵖ : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ-⟨ l ⟩ p₂ -> p₂ ≈ᵖ p₁
sym-≈ᵖ (εᵖ-≡ x y) = εᵖ-≡ (sym-≈ˢ x) (sym-≈ y) --  εᵖ-≡ (sym x)

trans-≈ᵖ : ∀ {l τ ls} {p₁ p₂ p₃ : Program ls τ} -> p₁ ≈ᵖ-⟨ l ⟩ p₂ -> p₂ ≈ᵖ p₃ -> p₁ ≈ᵖ p₃
trans-≈ᵖ (εᵖ-≡ x₁ y₁) (εᵖ-≡ x₂ y₂) = εᵖ-≡ (trans-≈ˢ x₁ x₂) (trans-≈ y₁ y₂)

-- My definition of l-equivalence for programs corresponds to the equivalence of the erasure of two programs 
unlift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂
unlift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} (εᵖ-≡ (εˢ-≡ eq₁) (ε-≡ eq₂)) rewrite eq₁ | eq₂ = refl

lift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂ -> p₁ ≈ᵖ p₂
lift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} eq = εᵖ-≡ (εˢ-≡ (store-≡ eq)) (ε-≡ (term-≡ eq))

--------------------------------------------------------------------------------

-- Structural low-equivalence for reasoning more conveniently
data _≈′_ {lₐ : Label} {Δ : Context} {τ : Ty} (t₁ t₂ : Term Δ τ) : Set where
  LE : ∀ {t₁ᵉ t₂ᵉ} -> (e₁ : Erasure lₐ t₁ t₁ᵉ) (e₂ : Erasure lₐ t₂ t₂ᵉ) (eq : t₁ᵉ ≡ t₂ᵉ) -> t₁ ≈′ t₂

_≈′-⟨_⟩_ : ∀ {Δ τ} -> Term Δ τ -> Label -> Term Δ τ -> Set
t₁ ≈′-⟨ lₐ ⟩ t₂ = _≈′_ {lₐ} t₁ t₂

-- Equivalence between structural low-equivalence and propositional low-equivalence

≈′-≈ : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈′-⟨ lₐ ⟩  t₂ -> t₁ ≈ t₂
≈′-≈ (LE e₁ e₂ eq) rewrite sym (Erasure-ε e₁) | sym (Erasure-ε e₂) = ε-≡ eq

≈-≈′ : ∀ {lₐ Δ τ} {t₁ t₂ : Term Δ τ} -> t₁ ≈-⟨ lₐ ⟩ t₂ -> t₁ ≈′ t₂
≈-≈′ (ε-≡ x) = LE (ε-Erasure _) (ε-Erasure _) x

