module Typed.Base where

open import Types public
import Data.List as L
open import Relation.Binary.PropositionalEquality

data Term (Δ : Context) : Ty -> Set where
  （） : Term Δ （）

  True : Term Δ Bool 
  False : Term Δ Bool

  Var : ∀ {τ} -> τ ∈ Δ -> Term Δ τ
  Abs : ∀ {α β} -> Term (α ∷ Δ) β -> Term Δ (α => β)
  App : ∀ {α β} -> Term Δ (α => β) -> Term Δ α -> Term Δ β

  If_Then_Else_ : ∀ {α} -> Term Δ Bool -> Term Δ α -> Term Δ α -> Term Δ α

  Return : ∀ {{l}} {α} -> Term Δ α -> Term Δ (Mac l α)
  _>>=_ : ∀ {{l}} {α β} -> Term Δ (Mac l α) -> Term Δ (α => Mac l β) -> Term Δ (Mac l β)

  ξ : Term Δ Exception
  Throw : ∀ {{l α}} -> Term Δ Exception -> Term Δ (Mac l α)
  Catch : ∀ {{l}} {α} -> Term Δ (Mac l α) -> Term Δ (Exception => Mac l α) -> Term Δ (Mac l α)

  Mac : ∀ {{l}} {α} -> Term Δ α -> Term Δ (Mac l α)
  Macₓ : ∀ {{l}} {α} -> Term Δ Exception -> Term Δ (Mac l α)

  Res : ∀ {{l}} {α} -> Term Δ α -> Term Δ (Labeled l α)
  Resₓ : ∀ {{l}} {α} -> Term Δ Exception -> Term Δ (Labeled l α)

  label : ∀ {l h α} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Labeled h α))
  unlabel : ∀ {l h α} -> l ⊑ h -> Term Δ (Labeled l α) -> Term Δ (Mac h α)

  join : ∀ {l h α} -> l ⊑ h -> Term Δ (Mac h α) -> Term Δ (Mac l (Labeled h α))

  Ref : ∀ {{α}} {{l}} -> ℕ -> Term Δ (Ref l α)

  read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)

  write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)
  
  new : ∀ {α l h} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Ref h α))

  -- Erased term ∙
  ∙ : ∀ {{τ}} -> Term Δ τ

CTerm : Ty -> Set
CTerm τ = Term [] τ

--------------------------------------------------------------------------------

-- I will start first with concrete memory containing closed terms
-- to implement references and then abstract over that with a more
-- generic Store.
-- The question I cannot answer right now is given
-- a store Store (A : Ty -> Set) : (Δ : Context) : Set
-- how can I abstract over generic read/write operations?

data Memory : (Δ : Context) -> Set where
  [] : Memory []
  _∷_ : ∀ {τ Δ} -> CTerm τ -> Memory Δ -> Memory (τ ∷ Δ)
  ∙ : ∀ {{Δ}} -> Memory Δ

-- Memory access
_[_] : ∀ {τ Δ} -> Memory Δ -> τ ∈ Δ -> CTerm τ
[] [ () ]
(x ∷ m) [ Here ] = x
(x ∷ m) [ There r ] = _[_] m r
∙ [ r ] = ∙

-- Update
_[_]≔_ : ∀ {τ Δ} -> Memory Δ -> τ ∈ Δ -> CTerm τ -> Memory Δ
_ ∷ Γ [ Here ]≔ v = v ∷ Γ
x ∷ Γ [ There i ]≔ v = x ∷ (Γ [ i ]≔ v)
∙ [ _ ]≔ _ = ∙

infixr 2 _[_]≔_

-- Snoc
_∷ʳ_ : ∀ {τ Δ} -> Memory Δ -> CTerm τ ->  Memory (Δ L.∷ʳ τ) 
[] ∷ʳ c = c ∷ []
(x ∷ Γ) ∷ʳ c = x ∷ (Γ ∷ʳ c)
∙ ∷ʳ c = ∙

-- Move to Types
snoc=∈ : (τ : Ty) (Δ : Context) -> τ ∈ (Δ L.∷ʳ τ)
snoc=∈ τ [] = Here
snoc=∈ τ (x ∷ Δ) = There (snoc=∈ τ Δ)

--------------------------------------------------------------------------------
-- Typed 0-based indexes

data TypedIx (τ : Ty) : ℕ -> Context -> Set where
  Here : ∀ {Δ} -> TypedIx τ zero (τ ∷ Δ)
  There : ∀ {Δ n τ'} -> TypedIx τ n Δ -> TypedIx τ (suc n) (τ' ∷ Δ)

castIx : ∀ {Δ₁ Δ₂ τ n} -> TypedIx τ n Δ₁ -> Δ₁ ⊆ Δ₂ -> TypedIx τ n Δ₂
castIx Here (cons q) = Here
castIx (There p) (cons q) = There (castIx p q) 

newTypeIx : ∀ {τ} -> (Δ : Context) -> TypedIx τ (length Δ) (Δ L.∷ʳ τ)
newTypeIx [] = Here
newTypeIx (x ∷ Δ) = There (newTypeIx Δ)

# : ∀ {τ n Δ} -> TypedIx τ n Δ -> τ ∈ Δ
# Here = Here
# (There p) = There (# p)

uniqueIx : ∀ {τ n Δ} -> (ix jx : TypedIx τ n Δ) -> ix ≡ jx
uniqueIx Here Here = refl
uniqueIx (There ix) (There jx) rewrite uniqueIx ix jx = refl

-- Equality for memory (which only diregards ∙ with different Δ)
data _≅_ : ∀ {Δ₁ Δ₂} -> Memory Δ₁ ->  Memory Δ₂ -> Set where
  base : [] ≅ []
  cons : ∀ {τ Δ₁ Δ₂} {x : CTerm τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} -> m₁ ≅ m₂ -> (x ∷ m₁) ≅ (x ∷ m₂)
  hole : ∀ {Δ₁ Δ₂} -> (∙ {{Δ₁}}) ≅ (∙ {{Δ₂}})

refl-≅ : ∀ {Δᵐ} {m : Memory Δᵐ} -> m ≅ m
refl-≅ {m = []} = base
refl-≅ {m = x ∷ m} = cons refl-≅
refl-≅ {m = ∙} = hole

sym-≅ : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} -> m₁ ≅ m₂ -> m₂ ≅ m₁
sym-≅ base = base
sym-≅ (cons p) = cons (sym-≅ p)
sym-≅ hole = hole

trans-≅ : ∀ {Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} -> m₁ ≅ m₂ -> m₂ ≅ m₃ -> m₁ ≅ m₃
trans-≅ base base = base
trans-≅ (cons p) (cons q) = cons (trans-≅ p q)
trans-≅ hole hole = hole

--------------------------------------------------------------------------------

-- The proof that a certain term is a value
data IsValue {Δ : Context} : ∀ {τ} -> Term Δ τ -> Set where
  （） : IsValue （）
  True : IsValue True
  False : IsValue False
  Abs : ∀ {α β} (t : Term (α ∷ Δ) β) -> IsValue (Abs t)
  ξ : IsValue ξ
  Mac : ∀ {α} {l : Label} (t : Term Δ α) -> IsValue (Mac t)
  Macₓ : ∀ {α} {l : Label} (e : Term Δ Exception) -> IsValue (Macₓ {α = α} e)
  Res : ∀ {α} {l : Label} (t : Term Δ α) -> IsValue (Res t)
  Resₓ : ∀ {α} {l : Label} (e : Term Δ Exception) -> IsValue (Resₓ {α = α} e)
  Ref : ∀ {l} {α : Ty} -> (n : ℕ) -> IsValue (Ref {{α}} n)

