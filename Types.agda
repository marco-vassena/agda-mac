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

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.List hiding (drop) public
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_) public
open import Data.Empty public

-- Types τ
data Ty : Set where
  （） : Ty
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : Label -> Ty -> Ty
  Labeled : Label -> Ty -> Ty
  Exception : Ty
  Ref : Label -> Ty -> Ty
  
infixr 3 _=>_

-- A context Δ is a list of types contained in an environment
Context : Set
Context = List Ty

-- Reference to a variable, bound during some abstraction.
data _∈_ : Ty -> Context -> Set where
 Here : ∀ {Δ τ} -> τ ∈ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ Δ -> α ∈ (β ∷ Δ)

-- Subset relation for lists (used for contexts in memory)
data _⊆_ {A : Set} : List A -> List A -> Set where
  base : [] ⊆ []
  drop : ∀ {xs ys : List A} {x : A} -> xs ⊆ ys -> xs ⊆ (x ∷ ys)
  cons : ∀ {xs ys : List A} {x : A} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

refl-⊆ : ∀ {A} -> (xs : List A) -> xs ⊆ xs
refl-⊆ [] = base
refl-⊆ (x ∷ xs) = cons (refl-⊆ xs)

extend-∈ : ∀ {Δ₁ Δ₂ τ} -> τ ∈ Δ₁ -> Δ₁ ⊆ Δ₂ -> τ ∈ Δ₂
extend-∈ () base
extend-∈ p (drop x) = There (extend-∈ p x)
extend-∈ Here (cons x) = Here
extend-∈ (There p) (cons x) = There (extend-∈ p x)

-- Transform τ ∈ᵗ Δ in Fin
fin : ∀ {τ Δ} -> τ ∈ Δ -> Fin (length Δ)
fin Here = zero
fin (There p) = suc (fin p)
