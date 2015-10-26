module Types where

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality

-- The security lattice (Label, _⊑_, _⊔_) is kept abstract
-- It will turned in a parameter to the module, but
-- at the moment Agda crashes with them

postulate Label : Set
postulate _⊑_ : Label -> Label -> Set
postulate _⊑?_ : (l h : Label) -> Dec (l ⊑ h)
postulate trans-⊑ : ∀ {l₁ l₂ l₃} -> l₁ ⊑ l₂ -> l₂ ⊑ l₃ -> l₁ ⊑ l₃

-- I am assuming extensionality between proofs of type ⊑.
-- I believe this make sense because labels and the relation ⊑ itself are abstract,
-- therefore given two proofs of l₁ ⊑ l₂ there is no way to distinguish between them.
-- As a result there is no way to distinguish two proofs in this formalization
-- therefore this assumption should not invalidate any of our results.
-- Essentially we are interested in the judgment of l₁ ⊑ l₂ in its broad sense, 
-- and not in its actual shape.
postulate extensional-⊑ : ∀ {l₁ l₂} -> (p q : l₁ ⊑ l₂) -> p ≡ q

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.List public
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit public
open import Data.Empty public

-- Types τ
data Ty : Set where
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : Label -> Ty -> Ty
  Labeled : Label -> Ty -> Ty
  Exception : Ty

infixr 3 _=>_

-- A context Δ is a list of types contained in an environment
Context : Set
Context = List Ty

-- Reference to a variable, bound during some abstraction.
data _∈_ : Ty -> Context -> Set where
 Here : ∀ {Δ τ} -> τ ∈ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ Δ -> α ∈ (β ∷ Δ)

-- Transform τ ∈ᵗ Δ in Fin
fin : ∀ {τ Δ} -> τ ∈ Δ -> Fin (length Δ)
fin Here = zero
fin (There p) = suc (fin p)
