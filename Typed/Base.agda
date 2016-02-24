module Typed.Base where

open import Types public
import Data.List as L
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.All

mutual 

  -- The basic Term Δ τ is a term that has type τ in the context Δ
  -- Δ is extended uniquely by lambda abstractions, which add the type of their argument to it.
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

    Res : ∀ {{l}} {α} -> Term Δ α -> Term Δ (Res l α)
    Resₓ : ∀ {{l}} {α} -> Term Δ Exception -> Term Δ (Res l α)

    -- It is fine to strenghten the level of a labeled resource
    relabel : ∀ {l h α} -> l ⊑ h -> Term Δ (Res l α) -> Term Δ (Res h α)

    -- This is used to avoid a context sensitive erasure in relabel
    relabel∙  : ∀ {l h α} -> l ⊑ h -> Term Δ (Res l α) -> Term Δ (Res h α)

    label : ∀ {l h α} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Res h α))
    unlabel : ∀ {l h α} -> l ⊑ h -> Term Δ (Res l α) -> Term Δ (Mac h α)

    join : ∀ {l h α} -> l ⊑ h -> Term Δ (Mac h α) -> Term Δ (Mac l (Res h α))

    zero : Term Δ Nat

    suc : Term Δ Nat -> Term Δ Nat

    read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)

    write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)

    new : ∀ {α l h} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Ref h α))

    -- Res l α is a functor
    fmap : ∀ {l α β} -> Term Δ (α => β) -> Term Δ (Res l α) -> Term Δ (Res l β)

    -- This is used to avoid a context sensitive erasure in fmap
    fmap∙  : ∀ {l α β} -> Term Δ (α => β) -> Term Δ (Res l α) -> Term Δ (Res l β)
    -- Represent sensitive information that has been erased.
    ∙ : ∀ {{τ}} -> Term Δ τ

  -- A closed term is a term typable in the empty context, i.e. it does not contain free variables.
  CTerm : Ty -> Set
  CTerm τ = Term [] τ

  -- A memory is a list of closed terms.
  -- The label l represents the sensitivity level of the terms contained in the memory.
  data Memory (l : Label) : Set where
    ∙ : Memory l  
    [] : Memory l
    _∷_ : ∀ {τ} -> CTerm τ -> Memory l -> Memory l

  -- A store contains several memories divided by level.
  -- Furthermore it requires each level to be unique.
  data Store : (List Label) -> Set where
    [] : Store []
    _∷_ : ∀ {l ls} {{u : Unique l ls}} -> Memory l -> Store ls -> Store (l ∷ ls)

  -- The proof that a term of a certain type is present in memory.
  data _∈ᵐ_ {l : Label} (τ : Ty) : Memory l -> Set where
    Here : ∀ {m} {c : CTerm τ} -> τ ∈ᵐ (c ∷ m)
    There : ∀ {m τ'} {c : CTerm τ'} -> τ ∈ᵐ m -> τ ∈ᵐ (c ∷ m)
    ∙ : τ ∈ᵐ ∙

  data ⟨_,_⟩∈ˢ_ (τ : Ty) (l : Label) : ∀ {ls} -> Store ls -> Set where
    Here : ∀ {ls} {p : Unique l ls} {m : Memory l} {s : Store ls} -> τ ∈ᵐ m -> ⟨ τ , l ⟩∈ˢ (m ∷ s)
    There : ∀ {l' ls} {p : Unique l' ls} {m : Memory l'} {s : Store ls} -> ⟨ τ , l ⟩∈ˢ s -> ⟨ τ , l ⟩∈ˢ (m ∷ s)

  -- Type synonym that ensures no duplicates in a list.
  Unique : Label -> List Label -> Set
  Unique l₁ ls = All (λ l₂ → ¬ (l₁ ≡ l₂)) ls

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

data TypedIx {l} (τ : Ty) : CTerm Nat -> Memory l -> Set where
  Here : ∀ {m} {c : CTerm τ} -> TypedIx τ zero (c ∷ m)
  There : ∀ {m n τ'} {c : CTerm τ'} -> TypedIx τ n m -> TypedIx τ (suc n) (c ∷ m)
  ∙ : ∀ {n} -> TypedIx τ n ∙

index-unique : ∀ {τ n l} {m : Memory l} -> (i j : TypedIx τ n m) -> i ≡ j
index-unique Here Here = refl
index-unique (There i) (There j) rewrite index-unique i j = refl
index-unique ∙ ∙ = refl


-- Read from memory
_[_] : ∀ {τ l n} -> (m : Memory l) -> TypedIx τ n m -> CTerm (Res l τ)
(c ∷ _) [ Here ] = Res c
(c ∷ m) [ There i ] = _[_] m i 
∙ [ ∙ ] = Res ∙

-- Update something in memory
_[_]≔_ : ∀ {l τ n} -> (m : Memory l) -> TypedIx τ n m -> CTerm τ -> Memory l
(_ ∷ m) [ Here ]≔ c = c ∷ m
(c ∷ m) [ There i ]≔ c₁ = c ∷ (m [ i ]≔ c₁)
∙ [ ∙ ]≔ c = ∙

infixr 2 _[_]≔_

-- Snoc for memory
_∷ʳ_ : ∀ {τ l} -> Memory l -> CTerm τ ->  Memory l 
[] ∷ʳ c = c ∷ []
(x ∷ m) ∷ʳ c = x ∷ (m ∷ʳ c)
∙  ∷ʳ c  = ∙

getMemory : ∀ {l ls} -> l ∈ ls -> Store ls ->  Memory l
getMemory Here (x ∷ s) = x
getMemory (There q) (x ∷ s) = getMemory q s

updateMemory : ∀ {l ls} -> l ∈ ls -> Store ls -> Memory l -> Store ls
updateMemory Here (x ∷ s) m = m ∷ s
updateMemory (There q) (x ∷ s) m = x ∷ updateMemory q s m

count : ∀ {l} -> Memory l -> CTerm Nat
count ∙ = ∙
count [] = zero
count (x ∷ m) = suc (count m)

-- Every piece of information that comes from the memory must be labeled with the same
-- security level.
lengthᵐ : ∀ {l} -> Memory l -> CTerm (Res l Nat)
lengthᵐ m = Res (count m)

-- Read from memory in store
_[_][_] : ∀ {τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ n (getMemory q s) -> CTerm (Res l τ)
(m ∷ s) [ Here ][ r ] = m [ r ]
(x ∷ s) [ There q ][ r ] = s [ q ][ r ]

-- Write to memory in store
_[_][_]≔_ : ∀ {τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ n (getMemory q s) -> CTerm τ -> Store ls
(m ∷ s) [ Here ][ r ]≔ c = (m [ r ]≔ c) ∷ s
(x ∷ s) [ There q ][ r ]≔ c = x ∷ (s [ q ][ r ]≔ c)

newˢ : ∀ {l ls τ} -> l ∈ ls -> Store ls -> CTerm τ -> Store ls
newˢ Here (m ∷ s) c = (m ∷ʳ c) ∷ s
newˢ (There q) (x ∷ s) c = x ∷ newˢ q s c

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
  zero : IsValue zero
  suc : (n : Term Δ Nat) -> IsValue (suc n)

