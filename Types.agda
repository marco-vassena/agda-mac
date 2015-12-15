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
open import Data.List hiding (drop ; _∷ʳ_ ; [_]) public
import Data.List as L
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

-- A list is a prefix of another
data _⊆_ {A : Set} : List A -> List A -> Set where
  base : ∀ {xs : List A} -> [] ⊆ xs
  cons : ∀ {xs ys x} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

refl-⊆ : ∀ {A} -> (xs : List A) -> xs ⊆ xs
refl-⊆ [] = base
refl-⊆ (x ∷ xs) = cons (refl-⊆ xs)

trans-⊆ : ∀ {A} {xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
trans-⊆ base q = base
trans-⊆ (cons p) (cons q) = cons (trans-⊆ p q)

snoc-⊆ : ∀ {A} {x : A} -> (xs : List A) -> xs ⊆ (xs L.∷ʳ x)
snoc-⊆ [] = base
snoc-⊆ (x₁ ∷ xs) = cons (snoc-⊆ xs)

-- Transform τ ∈ᵗ Δ in Fin
fin : ∀ {τ Δ} -> τ ∈ Δ -> Fin (length Δ)
fin Here = zero
fin (There p) = suc (fin p)
