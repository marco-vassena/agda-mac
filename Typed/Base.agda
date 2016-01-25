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

Contextˡ : Set
Contextˡ = List (Label × Ty)

infixr 3 _∈ˡ_

data _∈ˡ_ : Label × Ty -> Contextˡ -> Set where
  Here : ∀ {l τ Δˡ} -> (l , τ) ∈ˡ (l , τ) ∷ Δˡ
  There : ∀ {l₁ l₂ τ₁ τ₂ Δˡ} -> (l₁ , τ₁) ∈ˡ Δˡ -> ((l₁ , τ₁) ∈ˡ (l₂ , τ₂) ∷ Δˡ)
  
-- I will start first with concrete memory containing closed terms
-- to implement references and then abstract over that with a more
-- generic Store.
-- The question I cannot answer right now is given
-- a store Store (A : Ty -> Set) : (Δ : Context) : Set
-- how can I abstract over generic read/write operations?

data Memory : (Δˡ : Contextˡ) -> Set where
  [] : Memory []
  _∷_ : ∀ {τ l Δ} -> CTerm (Labeled l τ) -> Memory Δ -> Memory ((l , τ) ∷ Δ)
  ∙ : ∀ {{Δ}} -> Memory Δ

--------------------------------------------------------------------------------
-- Typed 0-based indexes

data TypedIx (l  : Label) (τ : Ty) : ℕ -> Contextˡ -> Set where
  Here : ∀ {Δ} -> TypedIx l τ zero ((l , τ) ∷ Δ)
  There : ∀ {Δ n l' τ'} -> TypedIx l τ n Δ -> TypedIx l τ (suc n) ((l' , τ') ∷ Δ)

castIx : ∀ {Δ₁ Δ₂ l τ n} -> TypedIx l τ n Δ₁ -> Δ₁ ⊆ Δ₂ -> TypedIx l τ n Δ₂
castIx Here (cons q) = Here
castIx (There p) (cons q) = There (castIx p q) 

newTypeIx : ∀ {τ l} -> (Δ : Contextˡ) -> TypedIx l τ (length Δ) (Δ L.∷ʳ (l , τ))
newTypeIx [] = Here
newTypeIx (x ∷ Δ) = There (newTypeIx Δ)

uniqueIx : ∀ {l τ n Δ} -> (ix jx : TypedIx l τ n Δ) -> ix ≡ jx
uniqueIx Here Here = refl
uniqueIx (There ix)  (There jx) rewrite uniqueIx ix jx = refl

--------------------------------------------------------------------------------

-- Memory access
_[_] : ∀ {n τ l Δˡ} -> Memory Δˡ -> TypedIx l τ n Δˡ  -> CTerm (Labeled l τ)
(x ∷ m) [ Here ] = x
∙ [ Here ] = ∙
(x ∷ m) [ There p ] = _[_] m p
∙ [ There p ] = ∙

-- [] [ () ]
-- (x ∷ m) [ Here ] = ?
-- (x ∷ m) [ There r ] = _[_] m r
-- ∙ [ r ] = ∙

-- Update
_[_]≔_ : ∀ {l τ n Δˡ} -> Memory Δˡ -> TypedIx l τ n Δˡ -> CTerm (Labeled l τ) -> Memory Δˡ
[] [ () ]≔ c
x ∷ m [ Here ]≔ c = c ∷ m
x ∷ m [ There i ]≔ c = x ∷ (m [ i ]≔ c)
∙ [ i ]≔ c = ∙

infixr 2 _[_]≔_

-- Snoc
_∷ʳ_ : ∀ {τ l Δ} -> Memory Δ -> CTerm (Labeled l τ) ->  Memory (Δ L.∷ʳ (l , τ)) 
[] ∷ʳ c = c ∷ []
(x ∷ Γ) ∷ʳ c = x ∷ (Γ ∷ʳ c)
∙ ∷ʳ c = ∙

-- Move to Types
snoc=∈ : (τ : Ty) (Δ : Context) -> τ ∈ (Δ L.∷ʳ τ)
snoc=∈ τ [] = Here
snoc=∈ τ (x ∷ Δ) = There (snoc=∈ τ Δ)

-- Equality for memory (which only diregards ∙ with different Δ)
data _≅_ : ∀ {Δ₁ Δ₂} -> Memory Δ₁ ->  Memory Δ₂ -> Set where
  base : [] ≅ []
  cons : ∀ {τ l Δ₁ Δ₂} {x : CTerm (Labeled l τ)} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} -> m₁ ≅ m₂ -> (x ∷ m₁) ≅ (x ∷ m₂)
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

