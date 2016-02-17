module Typed.Base where

open import Types public
import Data.List as L
open import Relation.Binary.PropositionalEquality
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

    Res : ∀ {{l}} {α} -> Term Δ α -> Term Δ (Labeled l α)
    Resₓ : ∀ {{l}} {α} -> Term Δ Exception -> Term Δ (Labeled l α)

    label : ∀ {l h α} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Labeled h α))
    unlabel : ∀ {l h α} -> l ⊑ h -> Term Δ (Labeled l α) -> Term Δ (Mac h α)

    join : ∀ {l h α} -> l ⊑ h -> Term Δ (Mac h α) -> Term Δ (Mac l (Labeled h α))

    -- We don't want to use labels here now, this should is stored in Res
    MRef : ∀ {{α l}} {ls} {s : Store ls} -> ⟨ α , l ⟩∈ˢ s -> Term Δ (MRef α)

    read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)

    write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)

    new : ∀ {α l h ls} {s : Store ls} -> l ⊑ h -> Term Δ α -> ⟨ α , h ⟩∈ˢ s -> Term Δ (Mac l (Ref h α))

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

-- Read from memory
_[_] : ∀ {τ l} -> (m : Memory l) -> τ ∈ᵐ m  -> CTerm (Labeled l τ)
(c ∷ _) [ Here ] = Res c
(c ∷ m) [ There i ] = _[_] m i 
∙ [ ∙ ] = Res ∙

-- Update something in memory
_[_]≔_ : ∀ {l τ} -> (m : Memory l) -> τ ∈ᵐ m -> CTerm τ -> Memory l
(_ ∷ m) [ Here ]≔ c = c ∷ m
(c ∷ m) [ There i ]≔ c₁ = c ∷ (m [ i ]≔ c₁)
∙ [ ∙ ]≔ c = ∙

infixr 2 _[_]≔_

-- Snoc for memory
_∷ʳ_ : ∀ {τ l} -> Memory l -> CTerm τ ->  Memory l 
[] ∷ʳ c = c ∷ []
(x ∷ m) ∷ʳ c = x ∷ (m ∷ʳ c)
∙  ∷ʳ c  = ∙

-- Allocates something in a store.
-- Note that the actual memory location is ignored by this function and in the semantics we assume
-- that it actually points to a valid fresh position in memory.
newˢ : ∀ {l ls τ} -> (s : Store ls) -> ⟨ τ , l ⟩∈ˢ s -> (c : CTerm τ) -> Store ls
newˢ (m ∷ s) (Here x) c = (m ∷ʳ c) ∷ s
newˢ (x ∷ s) (There q) c = x ∷ newˢ s q c

-- Read from the store
readˢ : ∀ {l ls τ} -> (s : Store ls) -> ⟨ τ , l ⟩∈ˢ s -> CTerm (Labeled l τ)
readˢ [] ()
readˢ (m ∷ s) (Here x) = _[_] m x
readˢ (m ∷ s) (There q) = readˢ s q

-- Write (update) to the store
writeˢ : ∀ {l ls τ} -> (c : CTerm τ) (s : Store ls) -> ⟨ τ , l ⟩∈ˢ s -> Store ls
writeˢ c [] ()
writeˢ c (m ∷ q) (Here x) = (m [ x ]≔ c) ∷ q
writeˢ c (m ∷ q) (There s) = m ∷ writeˢ c q s

-- This function generates a proof for a new allocation in memory.
-- We are not actually using this to generate the reference in the semantics
-- because it makes the types too complicated for reasoning.
new-∈ᵐ : ∀ {l τ} -> (m : Memory l) (c : CTerm τ) -> τ ∈ᵐ (m ∷ʳ c)
new-∈ᵐ ∙ c = ∙
new-∈ᵐ [] c = Here
new-∈ᵐ (x ∷ m) c = There (new-∈ᵐ m c)

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
  MRef : ∀ {l ls} {s : Store ls} {α : Ty} -> (p : ⟨ α , l ⟩∈ˢ s) -> IsValue (MRef p)

