open import Lattice public
open import Scheduler public

module Concurrent.Calculus (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Sequential.Calculus public

--------------------------------------------------------------------------------

-- Pool of threads at a certain label
data Pool (l : Label) : ℕ -> Set where
  [] : Pool l 0
  _◅_ : ∀ {n} -> Thread l -> Pool l n -> Pool l (suc n)
  ∙ : ∀ {n} -> Pool l n

infixr 3 _◅_

-- Enqueue
_▻_ : ∀ {n l} -> Pool l n -> Thread l -> Pool l (suc n)
[] ▻ t = t ◅ []
(x ◅ ts) ▻ t = x ◅ (ts ▻ t) 
∙ ▻ t = ∙

--------------------------------------------------------------------------------

-- A list of pools 
data Pools : List Label -> Set where
  [] : Pools []
  _◅_ : ∀ {l ls n} {{u : Unique l ls}} -> Pool l n -> Pools ls -> Pools (l ∷ ls)

open import Relation.Binary.PropositionalEquality

pools-unique : ∀ {l ls} -> (x y : l ∈ ls) -> Pools ls -> x ≡ y
pools-unique Here Here (x ◅ p) = refl
pools-unique Here (There y) (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique y u)
pools-unique (There x) Here (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique x u)
pools-unique (There x) (There y) (x₁ ◅ p) rewrite pools-unique x y p = refl

infixl 3 _▻_

--------------------------------------------------------------------------------

open Scheduler.Scheduler 𝓛 𝓢

-- The global configuration is a thread pool paired with some shared split memory Σ
record Global (ls : List Label) : Set where
  constructor ⟨_,_,_⟩
  field state : State
  field storeᵍ : Store ls
  field pools : Pools ls

open Global
open import Relation.Binary.PropositionalEquality

state-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> state g₁ ≡ state g₂
state-≡ refl = refl

storeᵍ-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> storeᵍ g₁ ≡ storeᵍ g₂
storeᵍ-≡ refl = refl

pools-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> pools g₁ ≡ pools g₂
pools-≡ refl = refl

