module MAC where

open import Data.List
open import Data.Unit
open import Data.Empty

-- Types τ
data Ty : Set where
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty

infixr 3 _=>_

-- TODO: is it better to have a Value data type or a statement IsValue : Term τ -> Set ?
-- Values v
data Value : Ty -> Set where
  True : Value Bool
  False : Value Bool

-- A context Δ is a list of types contained in an environment 
Context : Set
Context = List Ty

-- Reference to a variable, bound during some abstraction.
data _∈_ : Ty -> Context -> Set where
 Here : ∀ {Δ τ} -> τ ∈ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ Δ -> α ∈ (β ∷ Δ)

-- Untyped terms
data Term : Set where
  True : Term
  False : Term
  
  Var : Term
  Abs : Term -> Term
  App : Term -> Term -> Term

-- Typing judgments 
data _⊢_∷_ (Δ : Context) : Term -> Ty -> Set where 
  ETrue : Δ ⊢ True ∷ Bool
  EFalse : Δ ⊢ False ∷ Bool
  EApp : ∀ {t₁ t₂ α β} ->
           Δ ⊢ t₁ ∷ α => β ->
           Δ ⊢ t₂ ∷ α ->
           Δ ⊢ App t₁ t₂ ∷ β
  EAbs : ∀ {t α β} ->
           α ∷ Δ ⊢ t ∷ β -> 
           Δ ⊢ Abs t ∷ α => β
  EVar : ∀ {τ} -> τ ∈ Δ -> Δ ⊢ Var ∷ τ

infixl 1 _⊢_∷_

mutual 
  -- A closed term is indexed by a type and carries around the context
  -- nedeed for evaluation
  data CTerm : (τ : Ty) -> Set where
    Closure : ∀ {Δ t τ} -> (j : Δ ⊢ t ∷ τ) -> (e : Env Δ) -> CTerm τ 
    -- We need this constructor in order to distribute the same environment in the two terms
    CApp : ∀ {α β} -> CTerm (α => β) -> CTerm α -> CTerm β

  data Env : Context -> Set where
   [] : Env []
   _∷_ : ∀ {Δ τ} -> CTerm τ -> (Γ : Env Δ) -> Env (τ ∷ Δ)


-- Retrieves the term of the type given by the reference from an environment in a safe way
_!!_ : ∀ {Δ τ} -> τ ∈ Δ -> Env Δ -> CTerm τ
Here !! (t ∷ e) = t
There r !! (t ∷ e) = r !! e

-- Determines whether a closed term is a value or not
IsValue : ∀ {τ} -> CTerm τ -> Set
IsValue (Closure ETrue e) = ⊤
IsValue (Closure EFalse e) = ⊤
IsValue (Closure (EApp j₁ j₂) e) = ⊥
IsValue (Closure (EAbs j) e) = ⊤
IsValue (Closure (EVar x) e) = ⊥
IsValue (CApp c₁ c₂) = ⊥

-- Call-by-need small step semantics
-- Note that Env contains closed terms not necessarily values
data _⟼_ : {τ : Ty} -> CTerm τ -> CTerm τ -> Set where

  -- Reduces the function in an application
  AppL : {α β : Ty} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} ->
         c₁ ⟼ c₂ -> (CApp c₁ x) ⟼ (CApp c₂ x)

  -- Pushes a term in the environment
  Beta : ∀ {Δ α β t} {v : CTerm α} {Γ : Env Δ} {j : α ∷ Δ ⊢ t ∷ β} ->
          (CApp (Closure (EAbs j) Γ ) v) ⟼ (Closure j (v ∷ Γ))

  -- Looks up a variable in the environment
  Lookup : ∀ {Δ τ} {i : τ ∈ Δ} {Γ : Env Δ} ->
           (Closure (EVar i) Γ) ⟼ (i !! Γ)

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist : ∀ {Δ α β f x} {Γ : Env Δ} {j₁ : Δ ⊢ f ∷ α => β} {j₂ : Δ ⊢ x ∷ α} ->
         (Closure (EApp j₁ j₂) Γ) ⟼ (CApp (Closure j₁ Γ) (Closure j₂ Γ))
