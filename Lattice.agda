module Lattice where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

record Lattice : Set₁ where
  constructor Lat
  field
    Label : Set
    _⊑_ : Label -> Label -> Set
    _⊑?_ : (l₁ l₂ : Label) -> Dec (l₁ ⊑ l₂)

    -- Even though this lemma is not strictly necessary it does simplify
    -- some proofs.
    -- This decision is consistent with the corresponding Haskell type class which
    -- requires at most one instance for every pair of label.
    extensional : ∀ {l₁ l₂} -> (x y : Dec (l₁ ⊑ l₂)) -> x ≡ y
    
-- TODO add what other postulates about lattices we have
