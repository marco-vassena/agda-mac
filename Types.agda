module Types where

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality

-- The security lattice (Label, _⊑_, _⊔_) is kept abstract
-- It will turned in a parameter to the module, but
-- at the moment Agda crashes with them

postulate Label : Set
postulate _⊑_ : Label -> Label -> Set
postulate _⊑?_ : (l h : Label) -> Dec (l ⊑ h)

postulate refl-⊑ : ∀ {l} -> l ⊑ l
postulate trans-⊑ : ∀ {l₁ l₂ l₃} -> l₁ ⊑ l₂ -> l₂ ⊑ l₃ -> l₁ ⊑ l₃

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.List hiding (drop ; _∷ʳ_ ; [_]) public
import Data.List as L
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_) public
open import Data.Empty public
open import Data.Product using (_×_ ; _,_)

-- Types τ
data Ty : Set where
  （） : Ty
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : Label -> Ty -> Ty
  Res : Label -> Ty -> Ty
  Exception : Ty
  Nat : Ty
  
infixr 3 _=>_

Ref : Label -> Ty -> Ty
Ref l τ = Res l Nat

-- I will represents MVar also using integers like references
MVar : Label -> Ty -> Ty
MVar l τ = Res l Nat

-- A context Δ is a list of types contained in an environment
Context : Set
Context = List Ty

-- Reference to a variable, bound during some abstraction.
data _∈_ {A : Set} : A -> List A -> Set where
 Here : ∀ {Δ τ} -> τ ∈ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ Δ -> α ∈ (β ∷ Δ)

-- A list is a prefix of another
data _⊆_ {A : Set} : List A -> List A -> Set where
  base : ∀ {xs : List A} -> [] ⊆ xs
  cons : ∀ {xs ys x} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

refl-⊆ : ∀ {A} {xs : List A} -> xs ⊆ xs
refl-⊆ {_} {[]} = base
refl-⊆ {_} {x ∷ xs} = cons refl-⊆

trans-⊆ : ∀ {A} {xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
trans-⊆ base q = base
trans-⊆ (cons p) (cons q) = cons (trans-⊆ p q)

snoc-⊆ : ∀ {A} {xs : List A} {x : A} -> xs ⊆ (xs L.∷ʳ x)
snoc-⊆ {_} {[]} = base
snoc-⊆ {_} {x₁ ∷ xs} = cons snoc-⊆

-- Transform τ ∈ᵗ Δ in Fin
fin : ∀ {A : Set} {τ : A} {Δ : List A} -> τ ∈ Δ -> Fin (length Δ)
fin Here = zero
fin (There p) = suc (fin p)

extend-∈ : ∀ {A : Set} {τ : A} {Δ₁ Δ₂ : List A} -> τ ∈ Δ₁ -> Δ₁ ⊆ Δ₂ -> τ ∈ Δ₂
extend-∈ () base
extend-∈ Here (cons p) = Here
extend-∈ (There x) (cons p) = There (extend-∈ x p)

--------------------------------------------------------------------------------

-- Subset relation
data _⊆ˡ_ : List Ty -> List Ty -> Set where
  base : [] ⊆ˡ [] 
  cons : ∀ {α Δ₁ Δ₂} -> Δ₁ ⊆ˡ Δ₂ -> (α ∷ Δ₁) ⊆ˡ (α ∷ Δ₂)
  drop : ∀ {α Δ₁ Δ₂} -> Δ₁ ⊆ˡ Δ₂ -> Δ₁ ⊆ˡ (α ∷ Δ₂)

refl-⊆ˡ : ∀ {Δ} -> Δ ⊆ˡ Δ
refl-⊆ˡ {[]} = base
refl-⊆ˡ {x ∷ Δ} = cons refl-⊆ˡ

wken-∈ : ∀ {τ Δ₁ Δ₂} -> τ ∈ Δ₁ -> Δ₁ ⊆ˡ Δ₂ -> τ ∈ Δ₂
wken-∈ () base
wken-∈ Here (cons p) = Here
wken-∈ (There x) (cons p) = There (wken-∈ x p)
wken-∈ x (drop p) = There (wken-∈ x p)

infixr 2 _⊆ˡ_

--------------------------------------------------------------------------------
