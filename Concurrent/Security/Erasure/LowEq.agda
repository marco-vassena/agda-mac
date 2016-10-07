open import Lattice
open import Scheduler using (Scheduler)

module Concurrent.Security.Erasure.LowEq (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Types 𝓛
open import Scheduler 𝓛 as S
open Scheduler.Scheduler 𝓛 𝓢

open import Sequential.Calculus 𝓛
open import Sequential.Security.Erasure.Base 𝓛
open import Sequential.Security.Erasure.LowEq 𝓛 as Seq hiding (_≈ˢ-⟨_⟩_ ; sym-≈ˢ ; trans-≈ˢ) 
open import Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢
open import Concurrent.Security.Erasure.Base 𝓛 𝓢

open import Relation.Binary.PropositionalEquality
open import Data.Product


--------------------------------------------------------------------------------
-- TODO find good name/symbols for structural low-equivalence

mutual
  data _≌ᴾ_ {lₐ : Label} {l : Label} : ∀ {n m} -> Pool l n -> Pool l m -> Set where
    high : ∀ {n m} {p₁ : Pool l n} {p₂ : Pool l m} -> (¬p : ¬ (l ⊑ lₐ)) -> p₁ ≌ᴾ p₂
    nil : [] ≌ᴾ [] 
    cons : ∀ {n m} {p₁ : Pool l n} {p₂ : Pool l m} {t₁ t₂ : Thread l} -> l ⊑ lₐ -> t₁ ≈-⟨ lₐ ⟩ t₂ -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ -> (t₁ ◅ p₁) ≌ᴾ (t₂ ◅ p₂)
    bullet : ∀ {n m} -> (∙ {n = n}) ≌ᴾ (∙ {n = m})

  _≌ᴾ-⟨_⟩_ : ∀ {l n m} -> Pool l n -> Label -> Pool l m -> Set
  p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ = _≌ᴾ_ {lₐ} p₁ p₂ 

-- Is this equivalent to the definition of low-equivalence?
≌ᴾ-≡ : ∀ {l lₐ n} {p₁ : Pool l n} {p₂ : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ -> εᵗ x p₁ ≡ εᵗ x p₂
≌ᴾ-≡ (yes p) (high ¬p) = ⊥-elim (¬p p)
≌ᴾ-≡ (no ¬p) (high ¬p₁) = refl
≌ᴾ-≡ x nil = refl
≌ᴾ-≡ {l} {lₐ} (yes p) (cons {t₁ = t₁}  {t₂ = t₂} x₁ (ε-≡ eq) x₃)
  rewrite ≌ᴾ-≡ (yes p) x₃ | ε-Mac-extensional (yes p) (l ⊑? lₐ) t₁ | ε-Mac-extensional (yes p) (l ⊑? lₐ) t₂ | eq = refl
≌ᴾ-≡ (no ¬p) (cons x₁ x₂ x₃) = refl
≌ᴾ-≡ x bullet = refl

◅-≡ : ∀ {l n} {t₁ t₂ : Thread l} {ts₁ ts₂ : Pool l n} ->  _≡_ {A = Pool l (suc n)}(_◅_ {n = n} t₁ ts₁) (_◅_ {n = n} t₂ ts₂) -> (t₁ ≡ t₂) × (ts₁ ≡ ts₂)
◅-≡ refl = refl , refl

≡-≌ᴾ : ∀ {l lₐ n} {p₁ : Pool l n} {p₂ : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> εᵗ x p₁ ≡ εᵗ x p₂ -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂
≡-≌ᴾ {p₁ = []} {[]} x eq = nil
≡-≌ᴾ {p₁ = []} {∙} (yes p) ()
≡-≌ᴾ {p₁ = []} {∙} (no ¬p) refl = high ¬p
≡-≌ᴾ {l} {lₐ} {p₁ = x ◅ p₁} {x₁ ◅ p₂} (yes p) eq with ◅-≡ eq
... | eq₁ , eq₂ rewrite ε-Mac-extensional (yes p) (l ⊑? lₐ) x | ε-Mac-extensional (yes p) (l ⊑? lₐ) x₁ = cons p (ε-≡ eq₁) (≡-≌ᴾ (yes p) eq₂)
≡-≌ᴾ {p₁ = x ◅ p₁} {x₁ ◅ p₂} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = x ◅ p₁} {∙} (yes p) ()
≡-≌ᴾ {p₁ = x ◅ p₁} {∙} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {[]} (yes p) ()
≡-≌ᴾ {p₁ = ∙} {[]} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {x ◅ p₂} (yes p) ()
≡-≌ᴾ {p₁ = ∙} {x ◅ p₂} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {∙} x eq = bullet

--------------------------------------------------------------------------------
-- (ps₁ ps₂ : Pools ls)

mutual 
  data _≈ᴾ_ {lₐ : Label} : ∀ {ls} -> Pools ls -> Pools ls -> Set where
    _∷_ : ∀ {ls l n} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n} {u : Unique l ls} -> ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂ -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂ -> (ts₁ ◅ ps₁) ≈ᴾ (ts₂ ◅  ps₂)
    [] : [] ≈ᴾ []

  _≈ᴾ-⟨_⟩_ : ∀ {ls} -> Pools ls -> Label -> Pools ls -> Set
  p₁ ≈ᴾ-⟨ lₐ ⟩ p₂ = _≈ᴾ_ {lₐ} p₁ p₂ 

◅ᵖ-≡ⁿᵘ : ∀ {l n m ls} {u₁ u₂ : Unique l ls} {ps₁ ps₂ : Pools ls} {ts₁ : Pool l n} {ts₂ : Pool l m} -> _≡_ {A = Pools (l ∷ ls)} (_◅_ {{u = u₁}} ts₁ ps₁) (_◅_ {{u = u₂}} ts₂ ps₂)
            -> n ≡ m × u₁ ≡ u₂
◅ᵖ-≡ⁿᵘ refl = refl , refl

◅ᵖ-≡ : ∀ {l n ls} {u₁ u₂ : Unique l ls} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n} -> _≡_ {A = Pools (l ∷ ls)} (_◅_ {{u = u₁}} ts₁ ps₁) (_◅_ {{u = u₂}} ts₂ ps₂)
            -> ts₁ ≡ ts₂ × ps₁ ≡ ps₂
◅ᵖ-≡ refl = refl , refl


≡-≈ᴾ : ∀ {lₐ ls} {ps₁ ps₂ : Pools ls} -> εᴾ lₐ ps₁ ≡ εᴾ lₐ ps₂ -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂
≡-≈ᴾ {ps₁ = []} {[]} eq = []
≡-≈ᴾ {lₐ} {ps₁ = _◅_ {l = l} x ps₁} {x₁ ◅ ps₂} eq with ◅ᵖ-≡ⁿᵘ eq
... | eq₁ , eq₂ rewrite eq₁ | eq₂ with ◅ᵖ-≡ eq
... | eq₃ , eq₄ = ≡-≌ᴾ (l ⊑? lₐ) eq₃ ∷ ≡-≈ᴾ eq₄

≈ᴾ-≡ : ∀ {lₐ ls} {ps₁ ps₂ : Pools ls} -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂ -> εᴾ lₐ ps₁ ≡ εᴾ lₐ ps₂
≈ᴾ-≡ {lₐ} (_∷_ {l = l} ts ps) rewrite ≌ᴾ-≡ (l ⊑? lₐ) ts | ≈ᴾ-≡ ps = refl
≈ᴾ-≡ [] = refl

sym-≈ᴾ : ∀ {ls lₐ} {p₁ p₂ : Pools ls} -> p₁ ≈ᴾ-⟨ lₐ ⟩ p₂ -> p₂ ≈ᴾ p₁
sym-≈ᴾ eq = ≡-≈ᴾ (sym (≈ᴾ-≡ eq))

trans-≈ᴾ : ∀ {ls lₐ} {p₁ p₂ p₃ : Pools ls} -> p₁ ≈ᴾ-⟨ lₐ ⟩ p₂ -> p₂ ≈ᴾ p₃ -> p₁ ≈ᴾ p₃
trans-≈ᴾ a b = ≡-≈ᴾ (trans (≈ᴾ-≡ a) (≈ᴾ-≡ b))

--------------------------------------------------------------------------------

-- Since we cannot really do anything special with this, it would be best to define this as a synonym
-- data _≈ᵀ_ {{lₐ : Label}} (s₁ s₂ : State) : Set where
--   ε-≡ : ε-state lₐ s₁ ≡ ε-state lₐ s₂ -> s₁ ≈ᵀ s₂


-- _≈ᵀ_ : {lₐ : Label} (s₁ s₂ : State 𝓢) -> Set
-- _≈ᵀ_ {lₐ} s₁ s₂ = s₁ ≈ᵀ-⟨ lₐ ⟩ s₂

-- We need ≈ᵀ to be an isomoprphic to the ε based defintion
-- Then we can even prove that it is an equivalence relation

postulate ≈ˢ-≡ : ∀ {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> S.Scheduler.εˢ 𝓢 lₐ s₁ ≡ S.Scheduler.εˢ 𝓢 lₐ s₂
postulate ≡-≈ˢ : ∀ {lₐ s₁ s₂} -> S.Scheduler.εˢ 𝓢 lₐ s₁ ≡ S.Scheduler.εˢ 𝓢 lₐ s₂ -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂

postulate sym-≈ˢ : ∀ {lₐ} {s₁ s₂ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> s₂ ≈ˢ-⟨ lₐ ⟩ s₁
-- sym-≈ˢ x = sym x

postulate trans-≈ˢ : ∀ {lₐ} {s₁ s₂ s₃ : State} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> s₂ ≈ˢ-⟨ lₐ ⟩ s₃ -> s₁ ≈ˢ-⟨ lₐ ⟩ s₃
-- trans-≈ˢ x y = trans x y


-- --------------------------------------------------------------------------------

-- Global l-equivalence
mutual
  data _≈ᵍ_ {lₐ : Label} {ls : List Label} (g₁ g₂ : Global ls) : Set where
    ⟨_,_,_⟩ : state g₁ ≈ˢ-⟨ lₐ ⟩  state g₂ -> storeᵍ g₁ Seq.≈ˢ-⟨ lₐ ⟩ storeᵍ g₂ -> pools g₁ ≈ᴾ-⟨ lₐ ⟩ pools g₂ -> g₁ ≈ᵍ g₂

  _≈ᵍ-⟨_⟩_ : ∀ {ls} -> Global ls -> Label -> Global ls -> Set
  g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ = _≈ᵍ_ {lₐ} g₁ g₂

sym-≈ᵍ : ∀ {ls lₐ} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ -> g₂ ≈ᵍ-⟨ lₐ ⟩ g₁
sym-≈ᵍ ⟨ x , y , z ⟩ = ⟨ (sym-≈ˢ x) , (Seq.sym-≈ˢ y) , (sym-≈ᴾ z) ⟩

trans-≈ᵍ : ∀ {ls lₐ} {g₁ g₂ g₃ : Global ls} -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ -> g₂ ≈ᵍ-⟨ lₐ ⟩ g₃ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₃
trans-≈ᵍ ⟨ x₁ , y₁ , z₁ ⟩ ⟨ x₂ , y₂ , z₂ ⟩ = ⟨ trans-≈ˢ x₁ x₂ , Seq.trans-≈ˢ y₁ y₂ , trans-≈ᴾ z₁ z₂ ⟩

postulate refl-≈ᵍ : ∀ {lₐ ls} {g : Global ls}  -> g ≈ᵍ-⟨ lₐ ⟩ g
 
unlift-≈ᵍ : ∀ {lₐ ls} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂
unlift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} ⟨ x , εˢ-≡ y , z ⟩
  with ≈ˢ-≡ x | ≈ᴾ-≡ z
... | eq₁ | eq₂ rewrite eq₁ | eq₂ | y = refl

lift-≈ᵍ :  ∀ {lₐ ls} {g₁ g₂ : Global ls}  -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂
lift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} eq = ⟨ ≡-≈ˢ (state-≡ eq) , εˢ-≡ (storeᵍ-≡ eq) , ≡-≈ᴾ (pools-≡ eq) ⟩

--------------------------------------------------------------------------------
-- Easy access without explicit pattern matching,
-- TODO not useful remove

-- ≈ᵍ-≈ᴾ : ∀ {lₐ ls} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ -> pools g₁ ≈ᴾ-⟨ lₐ ⟩ pools g₂
-- ≈ᵍ-≈ᴾ ⟨ s₁≈s₂ , Σ₁≈Σ₂ , ps₁≈ps₂ ⟩ = ps₁≈ps₂

