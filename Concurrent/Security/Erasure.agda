open import Types
open import Concurrent.Communication as C

module Concurrent.Security.Erasure where

open import Sequential -- TODO remove
open import Concurrent.Base
open import Relation.Binary.PropositionalEquality
open import Sequential.Security.Distributivity

-- -- Erasure of thread pool
εᵗ : ∀ {n} {l lₐ : Label} -> Dec (l ⊑ lₐ) -> Pool l n -> Pool l n
εᵗ (yes p) [] = []
εᵗ (yes p) (t ◅ ts) = (ε-Mac _ (yes p) t) ◅ (εᵗ (yes p) ts)
εᵗ (yes p) ∙ = ∙
εᵗ (no ¬p) ts = ∙

ε-pools : ∀ {ls} -> Label -> Pools ls -> Pools ls
ε-pools lₐ [] = []
ε-pools lₐ (_◅_ {l = l} ts ps) = εᵗ (l ⊑? lₐ) ts ◅ (ε-pools lₐ ps)

εᴱ : Label -> C.Event -> C.Event
εᴱ lₐ (Fork h n) with h ⊑? lₐ
εᴱ lₐ (Fork h n) | yes p = Fork h n
εᴱ lₐ (Fork h n) | no ¬p = Step
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

fork-⊑ : ∀ {ls τ l h} {p₁ p₂ : Program ls (Mac l τ)} {t : Thread h }  -> p₁ ⟼ p₂ ↑ fork t -> l ⊑ h
fork-⊑ (fork p t s) = p

