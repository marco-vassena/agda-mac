module Concurrent.Security.Erasure where

open import Concurrent.Calculus
open import Concurrent.Semantics
open import Sequential.Security.Distributivity
open import Concurrent.Communication
open import Relation.Binary.PropositionalEquality

-- Erasure of thread pool
εᵗ : ∀ {n} {l lₐ : Label} -> Dec (l ⊑ lₐ) -> Pool l n -> Pool l n
εᵗ (yes p) [] = []
εᵗ (yes p) (t ◅ ts) = (ε-Mac _ (yes p) t) ◅ (εᵗ (yes p) ts)
εᵗ (yes p) ∙ = ∙
εᵗ (no ¬p) ts = ∙

ε-pools : ∀ {ls} -> Label -> Pools ls -> Pools ls
ε-pools lₐ [] = []
ε-pools lₐ (_◅_ {l = l} ts ps) = εᵗ (l ⊑? lₐ) ts ◅ (ε-pools lₐ ps)

εᴱ : ∀ {l} -> Label -> Event l -> Event l
εᴱ lₐ (Fork h n p) with h ⊑? lₐ
εᴱ lₐ (Fork h n p) | yes _ = Fork h n p
εᴱ lₐ (Fork h n p) | no ¬p = Step
εᴱ lₐ e = e

εᴹ : ∀ {l lₐ} -> Dec (l ⊑ lₐ) -> Message l -> Message l
εᴹ {._} {lₐ} (yes p) (l , n , e) = l , n , εᴱ lₐ e
εᴹ (no ¬p) (l , n , e) = l , n , ∙

--------------------------------------------------------------------------------

open import Data.Sum

εᵗ-extensional : ∀ {n l lₐ} (x y : Dec (l ⊑ lₐ)) (ts : Pool l n) -> εᵗ x ts ≡ εᵗ y ts
εᵗ-extensional (yes p) (yes p₁) [] = refl
εᵗ-extensional (yes p) (yes p₁) (x ◅ ts)
  rewrite ε-Mac-extensional (yes p) (yes p₁) x | εᵗ-extensional (yes p) (yes p₁) ts = refl
εᵗ-extensional (yes p) (yes p₁) ∙ = refl
εᵗ-extensional (yes p) (no ¬p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (yes p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (no ¬p₁) ts = refl

εᵗ∙≡∙ : ∀ {l lₐ} -> (x : Dec (l ⊑ lₐ)) -> (n : ℕ) -> εᵗ x ∙ ≡ (∙ {n = n})
εᵗ∙≡∙ (yes p) _ = refl
εᵗ∙≡∙ (no ¬p) _ = refl

ε-▻-≡ : ∀ {n l lₐ} (p : l ⊑ lₐ) (t : Thread l) (ts : Pool l n) -> εᵗ (yes p) (ts ▻ t) ≡ (εᵗ (yes p) ts ▻ ε-Mac lₐ (yes p) t)
ε-▻-≡ p t [] = refl
ε-▻-≡ p t (x ◅ ts) rewrite ε-▻-≡ p t ts = refl
ε-▻-≡ p t ∙ = refl

ε-IsValue : ∀ {τ l lₐ} {t : CTerm (Mac l τ)} -> (p : l ⊑ lₐ) -> IsValue t -> IsValue (ε-Mac lₐ (yes p) t)
ε-IsValue p (Mac t) = Mac (ε _ t)
ε-IsValue p (Macₓ e) = Macₓ (ε _ e)

