module Security.NonInterference where

open import Typed.Base
open import Typed.Semantics
open import Typed.Proofs
open import Security.Distributivity
open import Relation.Binary.PropositionalEquality

-- Low Equivalence
-- Two terms are low equivalent if they are equivalent after erasing them with label l.
data _≈_ {{l : Label}} {ls : List Label} {τ : Ty} (p₁ p₂ : Program ls τ) : Set where
  ε-≡ : εᵖ l p₁ ≡ εᵖ l p₂ -> p₁ ≈ p₂

refl-≈ : ∀ {l τ ls} {p : Program ls τ} -> p ≈ p
refl-≈ = ε-≡ refl

sym-≈ : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ≈ p₂ -> p₂ ≈ p₁
sym-≈ (ε-≡ x) = ε-≡ (sym x)

trans-≈ : ∀ {l τ ls} {p₁ p₂ p₃ : Program ls τ} -> p₁ ≈ p₂ -> p₂ ≈ p₃ -> p₁ ≈ p₃
trans-≈ (ε-≡ p) (ε-≡ q) = ε-≡ (trans p q)

≈-term : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≈ p₂ -> ε lₐ (term p₁) ≡ ε lₐ (term p₂)
≈-term {lₐ} {p₁ = ⟨ s₁ ∥ t₁ ⟩} {⟨ s₂ ∥ t₂ ⟩} (ε-≡ eq) with εᵖ lₐ ⟨ s₁ ∥ t₁ ⟩ | εᵖ lₐ ⟨ s₂ ∥ t₂ ⟩
≈-term {lₐ} {ls} {τ} {⟨ s₁ ∥ t₁ ⟩} {⟨ s₂ ∥ t₂ ⟩} (ε-≡ refl) | ⟨ x ∥ x₁ ⟩ | .(⟨ x ∥ x₁ ⟩) = {!!}

-- Single step simulation typed terms:
--
-- p₁ ≈ p₂ , p₁ ⟼ p₁' , p₂ ⟼ p₂'
-- then
-- p₁' ≈ p₂' 
--
-- By distributivity of ε the reductions steps are mapped in reductions of the erased terms:
-- p₁ ⟼ p₁'     to      (ε lₐ p₁) ⟼ (ε lₐ p₁')
-- p₂ ⟼ p₂'     to      (ε lₐ p₂) ⟼ (ε lₐ p₂')
-- Since the source terms are equivalent (ε lₐ p₁ ≡ ε lₐ p₂) by definition of low equivalence (p₁ ≈ p₂)
-- and the semantics is deterministic then the reduced erased terms are equivalent (ε lₐ p₁' ≡ ε lₐ p₂')
-- This implies that p₁' and p₂' are low-equivalent (p₁ ≈ p₂).
simulation : ∀ {l ls τ} {p₁ p₂ p₁' p₂' : Program ls τ} -> p₁ ≈ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ p₂'
simulation {l} (ε-≡ eq) s₁ s₂ = ε-≡ (aux eq (εᵖ-dist l s₁) (εᵖ-dist l s₂))
  where aux : ∀ {τ ls} {p₁ p₂ p₃ p₄ : Program ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₃ -> p₂ ⟼ p₄ -> p₃ ≡ p₄
        aux refl s₁ s₂ = determinism s₁ s₂

-- Low-equivalence preserves values.
-- If a term is a value and it is low equivalent to another then also the second is a value.
isValue-eq : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> IsValue (term p₁) -> IsValue (term p₂)
isValue-eq refl isV = isV

open import Data.Sum
open import Data.Product

-- bar : ∀ {{l}} {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ⟼⋆ p₂ -> (p₁ ≈ p₂) ⊎ {!!} --(∃ (λ p₁' ->  p₁ ⟼ p₁'))
-- bar ss = {!!}

-- foo : ∀ {lₐ ls τ} {p₁ p₂ v : Program ls τ} -> p₁ ≈ v -> p₁ ⟼⋆ p₂ -> IsValue (term v) -> IsValue (term p₂) -> p₂ ≈ v
-- foo eq ss isV₁ isV₂ with bar ss
-- foo eq ss isV₁ isV₂ | inj₁ x = trans-≈ (sym-≈ x) eq
-- foo eq ss isV₁ isV₂ | inj₂ t = {!!}

foobar : ∀ {{lₐ}} {τ} {t v : CTerm τ} -> IsValue v -> ε lₐ t ≡ ε lₐ v -> IsValue (ε lₐ t) ⊎ (ε lₐ t) ≡ ∙
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

foo : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ⟼⋆ p₂ -> term p₁ ≡ ∙ -> p₁ ≈ p₂
foo [] eq = refl-≈
foo (Pure Hole ∷ ss) refl = foo ss refl

-- Multi-step simulation
simulation⋆ : ∀ {lₐ ls τ} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ p₂ -> p₁ ⟼⋆ v₁ -> IsValue (term v₁) -> p₂ ⟼⋆ v₂ -> IsValue (term v₂) -> v₁ ≈ v₂
simulation⋆ eq [] isV₁ [] isV₂ = eq
simulation⋆ eq [] isV₁ (s₄ ∷ ss₂) isV₂ rewrite (≈-term eq) with foobar isV₁ (≈-term (sym-≈ eq))
simulation⋆ {lₐ} eq [] isV₁ (s₄ ∷ ss₂) isV₂ | inj₁ x = ⊥-elim (valueNotRedex _ x (Step (εᵖ-dist lₐ s₄)))
simulation⋆ (ε-≡ x) [] isV₁ (s₄ ∷ ss) isV₂ | inj₂ y = {!!} -- rewrite ε∙≡∙ {τ} {[]} lₐ = trans-≈ eq (foo (s ∷ ss) {!!})
--   = {!!} -- sym-≈ (foo (sym-≈ eq) (s ∷ ss₂) isV₁ isV₂)
simulation⋆ {lₐ} eq (s ∷ ss₁) isV₁ [] isV₂ = {!!} -- foobar eq s ss₁ isV₂ isV₁ -- ⊥-elim (valueNotRedex {!!} {!!} (Step (εᵖ-dist lₐ x)))
simulation⋆ eq (s₁ ∷ ss₁) isV₁ (s₂ ∷ ss₂) isV₂ with simulation eq s₁ s₂
... | p = simulation⋆ p ss₁ isV₁ ss₂ isV₂

non-interference  : ∀ {l ls τ} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ p₂ -> p₁ ⇓ v₁ -> p₂ ⇓ v₂ -> v₁ ≈ v₂
non-interference eq (BigStep isV₁ ss₁) (BigStep isV₂ ss₂) = simulation⋆ eq ss₁ isV₁ ss₂ isV₂
