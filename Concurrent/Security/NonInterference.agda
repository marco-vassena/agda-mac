open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure

module Concurrent.Security.NonInterference
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε-state : Label -> State -> State) -- Erasure function of the scheduler state
  (ε-sch-dist : ∀ {s₁ s₂ l lₐ} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ⟶ (ε-state lₐ s₂) ↑ (εᴹ x m))
  (ε-sch-≡ : ∀ {s₁ s₂ l lₐ} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ≡ (ε-state lₐ s₂))

  (deterministic-scheduler : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃ )

  where


open import Concurrent.Determinism State _⟶_↑_ deterministic-scheduler
open import Concurrent.Security.Distributivity State _⟶_↑_ ε-state ε-sch-dist ε-sch-≡
open import Concurrent.Semantics State _⟶_↑_
open import Concurrent.Calculus
open import Concurrent.Security.Erasure renaming (ε-pools to εᵖ)

open import Sequential.Security.Distributivity renaming (εˢ-≡ to high-stepˢ) hiding (εᵖ)
open import Sequential.Security.NonInterference hiding (_≈ᵖ_ ; non-interference)

open Global

--- TODO it seems that for some auxiliary lemmas we need a more structural definition of low equivalence
data _≈ᴾ_ {{lₐ : Label}} {ls : List Label} (ps₁ ps₂ : Pools ls) : Set where
  εᵖ-≡ : εᵖ lₐ ps₁ ≡ εᵖ lₐ ps₂ -> ps₁ ≈ᴾ ps₂

_≈ᴾ-⟨_⟩_ : ∀ {ls} -> Pools ls -> Label -> Pools ls -> Set
g₁ ≈ᴾ-⟨ lₐ ⟩ g₂ = g₁ ≈ᴾ g₂


data _≈ᵀ_ {{lₐ : Label}} (s₁ s₂ : State) : Set where
  ε-≡ : ε-state lₐ s₁ ≡ ε-state lₐ s₂ -> s₁ ≈ᵀ s₂

_≈ᵀ-⟨_⟩_ : State -> Label -> State -> Set
s₁ ≈ᵀ-⟨ lₐ ⟩ s₂ = s₁ ≈ᵀ s₂
 
-- Global l-equivalence
data _≈ᵍ_ {{lₐ : Label}} {ls : List Label} (g₁ g₂ : Global ls) : Set where
  ⟨_,_,_⟩ : state g₁ ≈ᵀ state g₂ -> storeᵍ g₁ ≈ˢ storeᵍ g₂ -> pools g₁ ≈ᴾ pools g₂ -> g₁ ≈ᵍ g₂

-- Global l-equivalence
-- data _≈ᵍ_ {{lₐ : Label}} {ls : List Label} (g₁ g₂ : Global ls) : Set where
--   εᵍ-≡ : εᵍ lₐ g₁ ≡ εᵍ lₐ g₂ -> g₁ ≈ᵍ g₂


--- Syntactic sugar to avoid ambiguities
_≈ᵍ-⟨_⟩_ : ∀ {ls} -> Global ls -> Label -> Global ls -> Set
g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ = g₁ ≈ᵍ g₂
 
unlift-≈ᵍ : ∀ {lₐ ls} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ g₂ -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂
unlift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} ⟨ ε-≡ x , εˢ-≡ x₁ , εᵖ-≡ x₂ ⟩
  rewrite x | x₁ | x₂ = refl

lift-≈ᵍ :  ∀ {lₐ ls} {g₁ g₂ : Global ls}  -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂ -> g₁ ≈ᵍ g₂
lift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} eq = ⟨ ε-≡ (state-≡ eq) , εˢ-≡ (storeᵍ-≡ eq) , εᵖ-≡ (pools-≡ eq) ⟩


-- simulation↪ : ∀ {ls l n} {{lₐ : Label}} {g₁ g₂ g₁' g₂' : Global ls} ->
--                     g₁ ≈ᵍ g₂ ->
--                     l , n ⊢ g₁ ↪ g₁' ->
--                     l , n ⊢ g₂ ↪ g₂' ->
--                     g₁' ≈ᵍ g₂'
-- simulation↪ {{lₐ}} p s₁ s₂ = εᵍ-≡ (aux (unlift-≈ᵍ p) (εᵍ-dist lₐ s₁) (εᵍ-dist lₐ s₂))
--   where aux : ∀ {ls l n} {t₁ t₂ t₃ t₄ : Global ls} -> t₁ ≡ t₂ -> l , n ⊢ t₁ ↪ t₃ -> l , n ⊢ t₂ ↪ t₄ -> t₃ ≡ t₄
--         aux refl s₁ s₂ = determinism↪ s₁ s₂

open import Data.Product
open import Sequential.Semantics

data Stuck {ls : List Label} {τ : Ty} (Σ : Store ls) (t : CTerm τ) : Set where
  stuck : ∀ {Σ' : Store ls} {t' : CTerm τ} -> ¬ (⟨ Σ ∥ t ⟩ ⟼ ⟨ Σ' ∥ t' ⟩) -> ¬ (IsValue t) -> Stuck Σ t

-- Stuck c = {!!}

data PStatus {ls : List Label} {τ : Ty} (Σ : Store ls) (t : CTerm τ) : Set where
  V : IsValue t -> PStatus Σ t
  R : Redex Σ t -> PStatus Σ t
  S : Stuck Σ t -> PStatus Σ t
  
postulate programStatus : ∀ {τ ls} -> (Σ : Store ls) (t : CTerm τ) -> PStatus Σ t

high-step : ∀ {lₐ l ls n} {g₁ g₂ : Global ls} -> ¬ (l ⊑ lₐ) -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂
high-step ¬p (step r₁ r₂ st sc w₁ w₂) = ⟨ (ε-≡ (ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , εᵖ-≡ (ε-write-≡ ¬p w₂) ⟩
high-step ¬p (fork r₁ r₂ r₃ st sc  w₁ w₂ w₃)
  = ⟨ ε-≡ (ε-sch-≡ ¬p sc) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , εᵖ-≡ (trans (ε-write-≡ ¬p w₂) (ε-write-≡ (trans-⋢ (fork-⊑ st) ¬p) w₃)) ⟩
high-step ¬p (hole r sc) = ⟨ ε-≡ (ε-sch-≡ ¬p sc) , εˢ-≡ refl , εᵖ-≡ refl ⟩
high-step ¬p (skip r₁ r₂ b sc) = ⟨ ε-≡ (ε-sch-≡ ¬p sc) , εˢ-≡ refl , εᵖ-≡ refl ⟩
high-step ¬p (exit r₁ r₂ isV sc) = ⟨ ε-≡ (ε-sch-≡ ¬p sc) , εˢ-≡ refl , εᵖ-≡ refl ⟩

-- lemma : ∀ {l n ls lₐ} {g₁ g₁' g₂ : Global ls} -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂' )
-- lemma (step r₁ r₂ st sc w₁ w₂) eq = {!!}
-- lemma (fork x x₁ x₂ x₃ x₄ x₅ x₆ x₇) eq = {!!}
-- lemma (hole x x₁) eq = _ , (eq , [])
-- lemma (skip x x₁ x₂ x₃) eq = {!!}
-- lemma (exit x x₁ x₂ x₃) eq = {!!}

lemma : ∀ {l n ls lₐ} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ lₐ) -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × l , n ⊢ g₁' ↪ g₂' )
lemma (yes p) s eq = {!!}
lemma (no ¬p) (step x x₁ x₂ x₃ x₄ x₅) eq = {!!}
lemma (no ¬p) (fork x x₁ x₂ x₃ x₄ x₅ x₆ x₇) eq = {!!}
lemma (no ¬p) (hole x x₁) eq = {!!}
lemma (no ¬p) (skip x x₁ x₂ x₃) eq = {!!}
lemma (no ¬p) (exit x x₁ x₂ x₃) eq = {!!}

-- -- I don't see how we can deduce from the hypothesis that a g₂' exists.
-- -- I can use distributivity and produce a step in the erased world, but how do I get back and get g₂' from it?
-- non-interference : ∀ {ls l n} {g₁ g₁' g₂ : Global ls} -> (lₐ : Label) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × (l , n ⊢ g₁' ↪ g₂'))
-- non-interference {g₁ = g₁} {g₁'} {g₂} lₐ (εᵍ-≡ x) s with εᵍ-dist lₐ s
-- ... | r = {!!} , ({!!} , {!r!})

-- TODO prove non-interference for multiple steps.
