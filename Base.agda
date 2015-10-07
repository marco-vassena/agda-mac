module Base where

open import Data.List public
open import Data.Unit public
open import Data.Empty public

-- Types τ
data Ty : Set where
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty

infixr 3 _=>_

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
  If_Then_Else_ : Term -> Term -> Term -> Term

-- Typing judgments.
-- They define well-typed terms
-- TODO should I keep the same constructors name as in Term?
data _⊢_∷_ (Δ : Context) : Term -> Ty -> Set where 
  True : Δ ⊢ True ∷ Bool
  False : Δ ⊢ False ∷ Bool
  App : ∀ {t₁ t₂ α β} ->
           Δ ⊢ t₁ ∷ α => β ->
           Δ ⊢ t₂ ∷ α ->
           Δ ⊢ App t₁ t₂ ∷ β
  Abs : ∀ {t α β} ->
           α ∷ Δ ⊢ t ∷ β -> 
           Δ ⊢ Abs t ∷ α => β
  Var : ∀ {τ} -> τ ∈ Δ -> Δ ⊢ Var ∷ τ

  If_Then_Else_ : ∀ {α t₁ t₂ t₃} ->
               Δ ⊢ t₁ ∷ Bool ->
               Δ ⊢ t₂ ∷ α ->
               Δ ⊢ t₃ ∷ α ->
               Δ ⊢ If t₁ Then t₂ Else t₃ ∷ α

infix 3 If_Then_Else_

infixl 1 _⊢_∷_


mutual 
  -- A closed term is indexed by a type and carries around the context
  -- nedeed for evaluation
  -- We need additional constructors _$_ and If_Then_Else_ to explicitly distribute
  -- the same environment in the small step semantics
  data CTerm : (τ : Ty) -> Set where
    
    -- Closure: couples a well-typed term with an environment of the same context Δ
    _,_ : ∀ {Δ t τ} -> (Γ : Env Δ) -> (j : Δ ⊢ t ∷ τ) -> CTerm τ 
    
    -- Closed term application 
    _$_ : ∀ {α β} -> CTerm (α => β) -> CTerm α -> CTerm β

    -- Closed IfThenElse
    If_Then_Else_ : ∀ {α} -> CTerm Bool -> CTerm α -> CTerm α -> CTerm α

  data Env : Context -> Set where
   [] : Env []
   _∷_ : ∀ {Δ τ} -> CTerm τ -> (Γ : Env Δ) -> Env (τ ∷ Δ)

infixr 3 _,_
infixr 0 _$_

-- Retrieves the term of the type given by the reference from an environment in a safe way
_!!_ : ∀ {Δ τ} -> τ ∈ Δ -> Env Δ -> CTerm τ
Here !! (t ∷ e) = t
There r !! (t ∷ e) = r !! e

-- Determines whether a closed term is a value or not
IsValue : ∀ {τ} -> CTerm τ -> Set
IsValue (Γ , True) = ⊤
IsValue (Γ , False) = ⊤
IsValue (Γ , App j j₁) = ⊥
IsValue (Γ , Abs j) = ⊤
IsValue (Γ , Var x) = ⊥
IsValue (Γ , If c Then t Else e) = ⊥
IsValue (c₁ $ c₂) = ⊥
IsValue (If c Then t Else e) = ⊥
