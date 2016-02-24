module Security.NonInterference where

open import Typed.Base
open import Typed.Semantics
open import Typed.Proofs
open import Security.Distributivity hiding (εˢ-≡)
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Move to Base

term-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> term p₁ ≡ term p₂
term-≡ refl = refl

store-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> store p₁ ≡ store p₂
store-≡ refl = refl

--------------------------------------------------------------------------------

data _≈ˢ_ {{lₐ : Label}} {ls : List Label} (s₁ s₂ : Store ls) : Set where
  εˢ-≡ : εˢ lₐ s₁ ≡ εˢ lₐ s₂ -> s₁ ≈ˢ s₂

refl-≈ˢ : ∀ {l ls} {s : Store ls} -> s ≈ˢ s
refl-≈ˢ = εˢ-≡ refl

sym-≈ˢ : ∀ {l ls} {s₁ s₂ : Store ls} -> s₁ ≈ˢ s₂ -> s₂ ≈ˢ s₁
sym-≈ˢ (εˢ-≡ x) = εˢ-≡ (sym x)

trans-≈ˢ : ∀ {l ls} {s₁ s₂ s₃ : Store ls} -> s₁ ≈ˢ s₂ -> s₂ ≈ˢ s₃ -> s₁ ≈ˢ s₃
trans-≈ˢ (εˢ-≡ x) (εˢ-≡ x₁) = εˢ-≡ (trans x x₁)

data _≈_ {{lₐ : Label}} {τ : Ty} (t₁ t₂ : CTerm τ) : Set where
  ε-≡ : ε lₐ t₁ ≡ ε lₐ t₂ -> t₁ ≈ t₂

refl-≈ : ∀ {l τ} {c : CTerm τ} -> c ≈ c
refl-≈ = ε-≡ refl

sym-≈ : ∀ {l τ} {c₁ c₂ : CTerm τ} -> c₁ ≈ c₂ -> c₂ ≈ c₁
sym-≈ (ε-≡ x) = ε-≡ (sym x)

trans-≈ : ∀ {l τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ≈ c₂ -> c₂ ≈ c₃ -> c₁ ≈ c₃
trans-≈ (ε-≡ x) (ε-≡ x₁) = ε-≡ (trans x x₁)


-- Low Equivalence
-- Two programs are low equivalent if they are equivalent after erasing them with label l.
data _≈ᵖ_ {{l : Label}} {ls : List Label} {τ : Ty} (p₁ p₂ : Program ls τ) : Set where
  εᵖ-≡ : store p₁ ≈ˢ store p₂ -> term p₁ ≈ term p₂ -> p₁ ≈ᵖ p₂

refl-≈ᵖ : ∀ {l τ ls} {p : Program ls τ} -> p ≈ᵖ p
refl-≈ᵖ {p = p} = εᵖ-≡ refl-≈ˢ refl-≈ -- εᵖ-≡ ? ? 

sym-≈ᵖ : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₁
sym-≈ᵖ (εᵖ-≡ x y) = εᵖ-≡ (sym-≈ˢ x) (sym-≈ y) --  εᵖ-≡ (sym x)

trans-≈ᵖ : ∀ {l τ ls} {p₁ p₂ p₃ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₃ -> p₁ ≈ᵖ p₃
trans-≈ᵖ (εᵖ-≡ x₁ y₁) (εᵖ-≡ x₂ y₂) = εᵖ-≡ (trans-≈ˢ x₁ x₂) (trans-≈ y₁ y₂)

lift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂
lift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} (εᵖ-≡ (εˢ-≡ eq₁) (ε-≡ eq₂)) rewrite eq₁ | eq₂ = refl

unlift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂ -> p₁ ≈ᵖ p₂
unlift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} eq = εᵖ-≡ (εˢ-≡ (store-≡ eq)) (ε-≡ (term-≡ eq))

--------------------------------------------------------------------------------

-- Single step simulation typed terms:
--
-- p₁ ≈ᵖ p₂ , p₁ ⟼ p₁' , p₂ ⟼ p₂'
-- then
-- p₁' ≈ᵖ p₂' 
--
-- By distributivity of ε the reductions steps are mapped in reductions of the erased terms:
-- p₁ ⟼ p₁'     to      (ε lₐ p₁) ⟼ (ε lₐ p₁')
-- p₂ ⟼ p₂'     to      (ε lₐ p₂) ⟼ (ε lₐ p₂')
-- Since the source terms are equivalent (ε lₐ p₁ ≡ ε lₐ p₂) by definition of low equivalence (p₁ ≈ᵖ p₂)
-- and the semantics is deterministic then the reduced erased terms are equivalent (ε lₐ p₁' ≡ ε lₐ p₂')
-- This implies that p₁' and p₂' are low-equivalent (p₁ ≈ᵖ p₂).
simulation : ∀ {l ls τ} {p₁ p₂ p₁' p₂' : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᵖ p₂'
simulation {l} eq s₁ s₂ = unlift-≈ᵖ (aux (lift-≈ᵖ eq) (εᵖ-dist l s₁) (εᵖ-dist l s₂))
  where aux : ∀ {τ ls} {p₁ p₂ p₃ p₄ : Program ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₃ -> p₂ ⟼ p₄ -> p₃ ≡ p₄
        aux refl s₁ s₂ = determinism s₁ s₂

-- Low-equivalence preserves values.
-- If a term is a value and it is low equivalent to another then also the second is a value.
isValue-eq : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> IsValue (term p₁) -> IsValue (term p₂)
isValue-eq refl isV = isV

open import Data.Sum
open import Data.Product

foobar : ∀ {{lₐ}} {τ} {t v : CTerm τ} -> IsValue v -> ε lₐ t ≡ ε lₐ v ->  IsValue (ε lₐ t) ⊎ ε lₐ t ≡ ∙  
foobar （） eq rewrite eq = inj₁ （）
foobar True eq rewrite eq = inj₁ True
foobar False eq rewrite eq = inj₁ False
foobar (Abs t₁) eq rewrite eq = inj₁ (Abs _)
foobar ξ eq rewrite eq = inj₁ ξ
foobar {{lₐ}} {τ = Mac lᵈ τ} (Mac t₁) eq with lᵈ ⊑? lₐ
foobar {{lₐ}} {Mac lᵈ τ} (Mac t₁) eq | yes p rewrite eq = inj₁ (Mac (ε lₐ t₁))
foobar {{lₐ}} {Mac lᵈ τ} {t = t} (Mac t₁) eq | no ¬p rewrite eq = inj₂ eq
foobar {{lₐ}} {τ = Mac lᵈ τ} (Macₓ e) eq with lᵈ ⊑? lₐ
foobar {{lₐ}} {Mac lᵈ τ} (Macₓ e) eq | yes p rewrite eq = inj₁ (Macₓ (ε lₐ e))
foobar {{lₐ}} {Mac lᵈ τ} {t = t} (Macₓ e) eq | no ¬p rewrite eq = inj₂ eq 
foobar {{lₐ}} {Res lᵈ τ} (Res t₁) eq with lᵈ ⊑? lₐ
foobar {{lₐ}} {Res lᵈ τ} (Res t₁) eq | yes p rewrite eq = inj₁ (Res (ε lₐ t₁))
foobar {{lₐ}} {Res lᵈ τ} (Res t₁) eq | no ¬p rewrite eq = inj₁ (Res ∙)
foobar {{lₐ}} {Res lᵈ τ} (Resₓ e) eq with lᵈ ⊑? lₐ
foobar {{lₐ}} {Res lᵈ τ} (Resₓ e) eq | yes p rewrite eq = inj₁ (Resₓ (ε lₐ e))
foobar {{lₐ}} {Res lᵈ τ} (Resₓ e) eq | no ¬p rewrite eq = inj₁ (Res ∙)
foobar zero eq rewrite eq = inj₁ zero
foobar {{lₐ}} (suc n) eq rewrite eq = inj₁ (suc (ε lₐ n))

-- egg : ∀ {{lₐ}} {τ} {t v : CTerm τ} -> IsValue v -> ε lₐ t ≡ ε lₐ v ->  IsValue (ε lₐ t) ⊎ ε lₐ t ≡ ∙  
-- egg 

foo : ∀ {τ ls} {p₁ p₂ : Program ls τ} -> p₁ ⟼⋆ p₂ -> term p₁ ≡ ∙ -> term p₁ ≡ term p₂
foo [] eq = refl
foo (Pure Hole ∷ ss) refl = foo ss refl

bar : ∀ {τ ls} {p₁ p₂ : Program ls τ} -> p₁ ⟼⋆ p₂ -> term p₁ ≡ ∙ -> store p₁ ≡ store p₂
bar [] eq = refl
bar (Pure Hole ∷ ss) refl = bar ss refl


-- foo ss refl

-- Multi-step simulation
simulation⋆ : ∀ {lₐ τ ls} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⟼⋆ v₁ -> IsValue (term v₁) -> p₂ ⟼⋆ v₂ -> IsValue (term v₂) -> v₁ ≈ᵖ v₂
simulation⋆ eq [] isV₁ [] isV₂ = eq
simulation⋆ (εᵖ-≡ x (ε-≡ eq)) [] isV₁ (s₄ ∷ ss₂) isV₂ with foobar isV₁ (sym eq)
simulation⋆ {lₐ} (εᵖ-≡ x₁ (ε-≡ eq)) [] isV₁ (s ∷ ss) isV₂ | inj₁ x = ⊥-elim (valueNotRedex _ x (Step (εᵖ-dist lₐ s)))
simulation⋆ {lₐ} {τ} (εᵖ-≡ (εˢ-≡ eq₁) (ε-≡ eq₂)) [] isV₁ (s ∷ ss) isV₂ | inj₂ y
  = εᵖ-≡ (εˢ-≡ (trans eq₁ (bar (εᵖ-dist⋆ lₐ (s ∷ ss)) y))) (ε-≡ (trans eq₂ (foo (εᵖ-dist⋆ lₐ (s ∷ ss)) y))) -- (εˢ-≡ (εˢ-≡⋆ lₐ {!!} {!s ∷ ss!})
simulation⋆ {lₐ} eq (s ∷ ss₁) isV₁ [] isV₂ = {!!} -- foobar eq s ss₁ isV₂ isV₁ -- ⊥-elim (valueNotRedex {!!} {!!} (Step (εᵖ-dist lₐ x)))
simulation⋆ eq (s₁ ∷ ss₁) isV₁ (s₂ ∷ ss₂) isV₂ with simulation eq s₁ s₂
... | p = simulation⋆ p ss₁ isV₁ ss₂ isV₂

non-interference  : ∀ {l ls τ} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⇓ v₁ -> p₂ ⇓ v₂ -> v₁ ≈ᵖ v₂
non-interference eq (BigStep isV₁ ss₁) (BigStep isV₂ ss₂) = simulation⋆ eq ss₁ isV₁ ss₂ isV₂
