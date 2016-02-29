module Typed.Base where

open import Types public
import Data.List as L
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
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

    -- Concurrency
    fork : ∀ {l h} -> l ⊑ h -> Term Δ (Mac h  （）) -> Term Δ (Mac l  （）)

    -- Synchronization primitives
    -- Creates a new empty MVar
    newMVar : ∀ {l h α} -> l ⊑ h -> Term Δ (Mac l (MVar h α))

    -- I will simplify directly the constraints l ⊑ h and h ⊑ l unifying the two labels
    takeMVar : ∀ {l α} -> Term Δ (MVar l α) -> Term Δ (Mac l α)
    putMVar : ∀ {l α} -> Term Δ (MVar l α) -> Term Δ α -> Term Δ (Mac l （）)

    -- Represent sensitive information that has been erased.
    ∙ : ∀ {{τ}} -> Term Δ τ

  -- A closed term is a term typable in the empty context, i.e. it does not contain free variables.
  CTerm : Ty -> Set
  CTerm τ = Term [] τ

  data CellType : Set where
    P : CellType -- Plain memory cell
    M : CellType -- Mutable memory cell (empty / full)

  -- A memory cell of a certain type
  data Cell (τ : Ty) : CellType -> Set where
    ⟪_⟫  : CTerm τ -> Cell τ P
    ⊞ : Cell τ M
    ⟦_⟧ : CTerm τ -> Cell τ M

  -- A memory is a list of closed terms.
  -- The label l represents the sensitivity level of the terms contained in the memory.
  data Memory (l : Label) : Set where
    ∙ : Memory l  
    [] : Memory l
    _∷_ : ∀ {c τ} -> Cell τ c -> Memory l -> Memory l

  -- A store contains several memories divided by level.
  -- Furthermore it requires each level to be unique.
  data Store : (List Label) -> Set where
    [] : Store []
    _∷_ : ∀ {l ls} {{u : Unique l ls}} -> Memory l -> Store ls -> Store (l ∷ ls)

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

data TypedIx {l} (τ : Ty) : CellType -> CTerm Nat -> Memory l -> Set where
  Here : ∀ {m p} {c : Cell τ p} -> TypedIx τ p zero (c ∷ m)
  There : ∀ {m n p p' τ'} {c : Cell τ' p'} -> TypedIx τ p n m -> TypedIx τ p (suc n) (c ∷ m)
  ∙ : ∀ {n p} -> TypedIx τ p n ∙

index-unique : ∀ {τ n p l} {m : Memory l} -> (i j : TypedIx τ p n m) -> i ≡ j
index-unique Here Here = refl
index-unique (There i) (There j) rewrite index-unique i j = refl
index-unique ∙ ∙ = refl

liftRes : ∀ {p τ l} -> Cell τ p -> Cell (Res l τ) p
liftRes ⟪ x ⟫ = ⟪ (Res x) ⟫
liftRes ⊞ = ⊞
liftRes ⟦ x ⟧ = ⟦ (Res x) ⟧

-- TODO : better name / symbol
get : ∀ {τ} -> Cell τ P -> CTerm τ
get ⟪ x ⟫ = x

-- Read from memory
_[_] : ∀ {τ l n p} -> (m : Memory l) -> TypedIx τ p n m -> Cell (Res l τ) p
(c ∷ m) [ Here ] = liftRes c
(c ∷ m) [ There i ] = _[_] m i 
_[_] {p = P} ∙ ∙ = ⟪ (Res ∙) ⟫
_[_] {p = M} ∙ ∙ = ⟦ (Res ∙) ⟧ -- ⊞ is also an option, I think we can choose

-- Update something in memory
_[_]≔_ : ∀ {p l τ n} -> (m : Memory l) -> TypedIx τ p n m -> Cell τ p -> Memory l
(_ ∷ m) [ Here ]≔ c = c ∷ m
(c ∷ m) [ There i ]≔ c₁ = c ∷ (m [ i ]≔ c₁)
∙ [ ∙ ]≔ c = ∙

infixr 2 _[_]≔_

-- Snoc for memory
_∷ʳ_ : ∀ {τ l p} -> Memory l -> Cell p τ ->  Memory l 
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
_[_][_] : ∀ {p τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ p n (getMemory q s) -> Cell (Res l τ) p
(m ∷ s) [ Here ][ r ] = m [ r ]
(x ∷ s) [ There q ][ r ] = s [ q ][ r ]

_[_][_]ᴾ : ∀ {τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ P n (getMemory q s) -> CTerm (Res l τ)
s [ q ][ r ]ᴾ = get (s [ q ][ r ])

-- Write to memory in store
_[_][_]≔_ : ∀ {τ ls l n p} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ p n (getMemory q s) -> Cell τ p -> Store ls
(m ∷ s) [ Here ][ r ]≔ c = (m [ r ]≔ c) ∷ s
(x ∷ s) [ There q ][ r ]≔ c = x ∷ (s [ q ][ r ]≔ c)

newˢ : ∀ {p l ls τ} -> l ∈ ls -> Store ls -> Cell τ p -> Store ls
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


--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ Δ₁ Δ₂} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Var x) p = Var (wken-∈ x p)
wken (Abs t) p = Abs (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return t) p = Return (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken ξ p = ξ
wken (Throw t) p = Throw (wken t p)
wken (Catch t t₁) p = Catch (wken t p) (wken t₁ p)
wken (Mac t) p = Mac (wken t p)
wken (Macₓ t) p = Macₓ (wken t p)
wken (Res t) p = Res (wken t p)
wken (Resₓ t) p = Resₓ (wken t p)
wken (relabel x c) p = relabel x (wken c p)
wken (relabel∙ x c) p = relabel∙ x (wken c p)
wken (label x t) p = label x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
wken (join x t) p = join x (wken t p)
wken zero p = zero
wken (suc n) p = suc (wken n p)
wken (read x t) p = read x (wken t p)
wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
wken (new x t) p = new x (wken t p)
wken (fmap f x) p = fmap (wken f p) (wken x p)
wken (fmap∙ f x) p = fmap∙ (wken f p) (wken x p)
wken (fork x t) p = fork x (wken t p)
wken (newMVar {α = α} x) p = newMVar {α = α} x
wken (takeMVar t) p = takeMVar (wken t p)
wken (putMVar t₁ t₂) p = putMVar (wken t₁ p) (wken t₂ p)
wken ∙ p = ∙

_↑¹ : ∀ {α β Δ} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) β
var-subst [] Δ₂ t Here = t
var-subst [] Δ t (There p) = Var p
var-subst (β ∷ Δ₁) Δ₂ t Here = Var Here
var-subst (x ∷ Δ₁) Δ₂ t (There p) = (var-subst Δ₁ Δ₂ t p) ↑¹

tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Var x) = var-subst Δ₁ Δ₂ v x
tm-subst Δ₁ Δ₂ v (Abs t) = Abs (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return t) = Return (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v ξ = ξ
tm-subst Δ₁ Δ₂ v (Throw t) = Throw (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Catch t t₁) = Catch (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac t) = Mac (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Macₓ t) = Macₓ (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res t) = Res (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Resₓ t) = Resₓ (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (relabel p t) = relabel p (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (relabel∙ p t) = relabel∙ p (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (join x t) = join x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v zero = zero
tm-subst Δ₁ Δ₂ v (suc n) = suc (tm-subst Δ₁ Δ₂ v n)
tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fmap f x) = fmap (tm-subst Δ₁ Δ₂ v f) (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v (fmap∙ f x) = fmap∙ (tm-subst Δ₁ Δ₂ v f) (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (newMVar {α = α} x) = newMVar {α = α} x
tm-subst Δ₁ Δ₂ v (takeMVar t) = takeMVar (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (putMVar t₁ t₂) = putMVar (tm-subst Δ₁ Δ₂ v t₁) (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {Δ α β} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ} v t = tm-subst [] Δ v t

--------------------------------------------------------------------------------

-- A program is made of a labeled store and a closed term
record Program (ls : List Label) (τ : Ty) : Set where
  constructor ⟨_∥_⟩
  field store : Store ls
  field term : CTerm τ

open Program

term-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> term p₁ ≡ term p₂
term-≡ refl = refl

store-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> store p₁ ≡ store p₂
store-≡ refl = refl
