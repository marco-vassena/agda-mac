module Concurrent.Calculus where

open import Data.List
open import Sequential.Calculus public
open import Data.Nat

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
