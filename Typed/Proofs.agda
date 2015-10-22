module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality

-- In principle once we prove the bijection between typed and untyped semantics
-- we can keep only one proof and derive the other.
-- For the time being I will postulate this
postulate determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
