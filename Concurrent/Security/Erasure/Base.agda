open import Lattice
open import Scheduler using (Scheduler)

module Concurrent.Security.Erasure.Base (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Scheduler 𝓛
import Scheduler 𝓛 as S
open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Concurrent.Calculus 𝓛 𝓢
open import Sequential.Security.Erasure 𝓛
open import Concurrent.Communication --TODO remove
open import Concurrent.Semantics 𝓛 𝓢
open import Relation.Binary.PropositionalEquality

-- Erasure of thread pool
εᵗ : ∀ {n} {l lₐ : Label} -> Dec (l ⊑ lₐ) -> Pool l n -> Pool l n
εᵗ (yes p) [] = []
εᵗ (yes p) (t ◅ ts) = (ε-Mac _ (yes p) t) ◅ (εᵗ (yes p) ts)
εᵗ (yes p) ∙ = ∙
εᵗ (no ¬p) ts = ∙

-- Erasure of pools
εᴾ : ∀ {ls} -> Label -> Pools ls -> Pools ls
εᴾ lₐ [] = []
εᴾ lₐ (_◅_ {l = l} ts ps) = εᵗ (l ⊑? lₐ) ts ◅ (εᴾ lₐ ps)

--------------------------------------------------------------------------------

open import Data.Sum

εᵗ-extensional : ∀ {n l lₐ} (x y : Dec (l ⊑ lₐ)) (ts : Pool l n) -> εᵗ x ts ≡ εᵗ y ts
εᵗ-extensional (yes p) (yes p₁) [] = refl
εᵗ-extensional (yes p) (yes p₁) (x ◅ ts)
  with ε-Mac-extensional (yes p) (yes p₁) x | εᵗ-extensional (yes p) (yes p₁) ts
... | eq₁ | eq₂ rewrite  eq₁ | eq₂ = refl
εᵗ-extensional (yes p) (yes p₁) ∙ = refl
εᵗ-extensional (yes p) (no ¬p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (yes p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (no ¬p₁) ts = refl

εᵗ∙≡∙ : ∀ {l lₐ} -> (x : Dec (l ⊑ lₐ)) -> (n : ℕ) -> εᵗ x ∙ ≡ (∙ {n = n})
εᵗ∙≡∙ (yes p) _ = refl
εᵗ∙≡∙ (no ¬p) _ = refl

ε-▻-≡ : ∀ {n l lₐ} (p : l ⊑ lₐ) (t : Thread l) (ts : Pool l n) -> εᵗ (yes p) (ts ▻ t) ≡ (εᵗ (yes p) ts ▻ ε-Mac lₐ (yes p) t)
ε-▻-≡ p t [] = refl
ε-▻-≡ p t (x ◅ ts) with ε-▻-≡ p t ts
... | eq rewrite eq = refl
ε-▻-≡ p t ∙ = refl

ε-IsValue : ∀ {τ l lₐ} {t : CTerm (Mac l τ)} -> (p : l ⊑ lₐ) -> IsValue t -> IsValue (ε-Mac lₐ (yes p) t)
ε-IsValue p (Mac t) = Mac (ε _ t)
ε-IsValue p (Macₓ e) = Macₓ (ε _ e)

-- Erasure of global configuration
εᵍ : ∀ {ls} -> Label -> Global ls -> Global ls
εᵍ lₐ ⟨ s , Σ , ps ⟩ = ⟨ S.Scheduler.εˢ 𝓢 lₐ s , εˢ lₐ Σ , εᴾ lₐ ps ⟩ 

εᵉ : ∀ {lₐ l} -> Dec (l ⊑ lₐ) -> Effect l -> Effect l
εᵉ (yes p) ∙ = ∙
εᵉ (yes p) ∅ = ∅
εᵉ {lₐ} (yes p) (fork t) = fork (ε lₐ t)
εᵉ (no ¬p) e = ∙
                 
