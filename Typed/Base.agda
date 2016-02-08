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

data Memory (l : Label) : Set where
  ∙ : Memory l
  [] : Memory l
  _∷_ : ∀ {τ} -> CTerm (Labeled l τ) -> Memory l -> Memory l

open import Data.List.All

Unique : Label -> List Label -> Set
Unique l₁ ls = All (λ l₂ → ¬ (l₁ ≡ l₂)) ls

data Store : (List Label) -> Set where
  [] : Store []
  _∷_ : ∀ {l ls} {{u : Unique l ls}} -> Memory l -> Store ls -> Store (l ∷ ls)

store-unique : ∀ {l ls} -> Store ls -> (x y : l ∈ ls) -> x ≡ y
store-unique = aux
  where
    unique-lemma : ∀ {l ls} -> l ∈ ls -> Unique l ls -> ⊥
    unique-lemma Here (px ∷ q) = ⊥-elim (px refl)
    unique-lemma (There p) (px ∷ q) = unique-lemma p q

    aux : ∀ {l ls} -> Store ls -> (x y : l ∈ ls) -> x ≡ y
    aux s Here Here = refl
    aux (_∷_ {{u = u}} x s) Here (There y) = ⊥-elim (unique-lemma y u)
    aux (_∷_ {{u = u}} x s) (There x₁) Here = ⊥-elim (unique-lemma x₁ u)
    aux (l ∷ s) (There x) (There y) = cong There (aux s x y)

getMemory : ∀ {l ls} -> l ∈ ls -> Store ls -> Memory l
getMemory Here (x ∷ s) = x
getMemory (There p) (x ∷ s) = getMemory p s

updateMemory : ∀ {l ls} -> Memory l -> l ∈ ls -> Store ls -> Store ls
updateMemory m Here (x ∷ s) = m ∷ s
updateMemory m (There p) (x ∷ s) = x ∷ updateMemory m p s

lengthᵐ : ∀ {l} -> Memory l -> ℕ
lengthᵐ [] = 0
lengthᵐ (x ∷ m) = suc (lengthᵐ m)
lengthᵐ ∙ = 0

--------------------------------------------------------------------------------
-- Typed 0-based indexes

data TypedIx {l : Label} (τ : Ty) : ℕ -> Memory l -> Set where
  Here : ∀ {m} {c : CTerm (Labeled l τ)} -> TypedIx τ zero (c ∷ m)
  There : ∀ {m n τ'} {c : CTerm (Labeled l τ')} ->  TypedIx τ n m -> TypedIx τ (suc n) (c ∷ m)
  Hole : ∀ {n} -> TypedIx τ n ∙
  
-- castIx : ∀ {Δ₁ Δ₂ l τ n} -> TypedIx l τ n Δ₁ -> Δ₁ ⊆ Δ₂ -> TypedIx l τ n Δ₂
-- castIx Here (cons q) = Here
-- castIx (There p) (cons q) = There (castIx p q) 

-- newTypeIx : ∀ {τ l} -> (Δ : Contextˡ) -> TypedIx l τ (length Δ) (Δ L.∷ʳ (l , τ))
-- newTypeIx [] = Here
-- newTypeIx (x ∷ Δ) = There (newTypeIx Δ)

-- uniqueIx : ∀ {l τ n Δ} -> (ix jx : TypedIx l τ n Δ) -> ix ≡ jx
-- uniqueIx Here Here = refl
-- uniqueIx (There ix)  (There jx) rewrite uniqueIx ix jx = refl

-- --------------------------------------------------------------------------------

-- Memory access
_[_] : ∀ {n τ l} -> (m : Memory l) -> TypedIx τ n m  -> CTerm (Labeled l τ)
(c ∷ _) [ Here ] = c
(c ∷ m) [ There i ] = _[_] m i 
∙ [ Hole ] = Res ∙ 

-- Update
_[_]≔_ : ∀ {l τ n} -> (m : Memory l) -> TypedIx τ n m -> CTerm (Labeled l τ) -> Memory l
(_ ∷ m) [ Here ]≔ c = c ∷ m
(c ∷ m) [ There i ]≔ c₁ = c ∷ (m [ i ]≔ c₁)
∙ [ Hole ]≔ c = ∙

infixr 2 _[_]≔_

-- Snoc
_∷ʳ_ : ∀ {τ l} -> Memory l -> CTerm (Labeled l τ) ->  Memory l 
[] ∷ʳ c = c ∷ []
(x ∷ m) ∷ʳ c = x ∷ (m ∷ʳ c)
∙  ∷ʳ c  = ∙

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

