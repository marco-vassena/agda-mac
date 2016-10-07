module Lattice where

open import Relation.Nullary

record Lattice : Set₁ where
  constructor _,_,_
  field
    Label : Set
    _⊑_ : Label -> Label -> Set
    _⊑?_ : (l₁ l₂ : Label) -> Dec (l₁ ⊑ l₂)

-- TODO add what other postulates about lattices we have
