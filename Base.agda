module Base where

open import Relation.Nullary public

-- The security lattice (Label, _⊑_, _⊔_) is kept abstract
-- It will turned in a parameter to the module, but 
-- at the moment Agda crashes with them

postulate Label : Set
postulate _⊑_ : Label -> Label -> Set
postulate _⊑?_ : (l h : Label) -> Dec (l ⊑ h)

open import Data.List public
open import Data.Unit public
open import Data.Empty public

-- Types τ
data Ty : Set where
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : Label -> Ty -> Ty
  Labeled : Label -> Ty -> Ty
  Exception : Ty

infixr 3 _=>_

-- A context Δ is a list of types contained in an environment 
Context : Set
Context = List Ty

-- Reference to a variable, bound during some abstraction.
data _∈_ : Ty -> Context -> Set where
 Here : ∀ {Δ τ} -> τ ∈ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ Δ -> α ∈ (β ∷ Δ)

-- Untyped terms
-- TODO combining terms with types (and therefore contexts)
-- could probably simplify the proofs, because 
-- only terms with the correct type would be reported on case analysis.
data Term : Set where
  True : Term
  False : Term
  
  Var : Term
  Abs : Term -> Term
  App : Term -> Term -> Term
  If_Then_Else_ : Term -> Term -> Term -> Term

  Return : Term -> Term
  _>>=_ : Term -> Term -> Term

  ξ : Term
  Throw : Term -> Term
  Catch : Term -> Term -> Term

  -- Abstract constructors not available to the user
  Mac : Term -> Term

  -- Abstract constructor that denotes failure due to an exception
  Macₓ : Term -> Term

  -- TODO add
  Res : Term -> Term

  label : Term -> Term
  unlabel : Term -> Term

  -- Erased term
  ∙ : Term

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

  Return : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ τ -> Δ ⊢ t ∷ Mac l τ

  _>>=_ : ∀ {α β t k l} ->
            Δ ⊢ t ∷ Mac l α ->
            Δ ⊢ k ∷ (α => Mac l β) ->
            Δ ⊢ t >>= k ∷ Mac l β

  ξ : Δ ⊢ ξ ∷ Exception

  Throw : ∀ {{l}} {τ t} -> Δ ⊢ t ∷ Exception -> Δ ⊢ t ∷ Mac l τ

  Catch : ∀ {t h τ} {{l}} ->
          Δ ⊢ t ∷ Mac l τ -> 
          Δ ⊢ h ∷ Exception => Mac l τ ->
          Δ ⊢ Catch t h ∷ Mac l τ

  -- IO and Mac are fused for simplicity
  Mac : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ τ -> Δ ⊢ t ∷ Mac l τ

  Macₓ : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ Exception -> Δ ⊢ t ∷ Mac l τ

  label : ∀ {t τ l h} -> 
          l ⊑ h -> 
          Δ ⊢ t ∷ τ -> 
          Δ ⊢ label t ∷ Mac l (Labeled h τ)

  unlabel : ∀ {t τ l h} -> 
              l ⊑ h -> 
              Δ ⊢ t ∷ Labeled l τ ->
              Δ ⊢ unlabel t ∷ Mac h τ

  Res : ∀ {t τ} {{l}} ->
        Δ ⊢ t ∷ τ ->
        Δ ⊢ Res t ∷ Labeled l τ

  ∙ : ∀ {τ} -> Δ ⊢ ∙ ∷ τ

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

    _>>=_ : ∀ {α β l} -> CTerm (Mac l α) -> CTerm (α => Mac l β) -> CTerm (Mac l β)

    Catch : ∀ {l τ} -> CTerm (Mac l τ) -> CTerm (Exception => Mac l τ) -> CTerm (Mac l τ)

    unlabel : ∀ {l h τ} -> l ⊑ h -> CTerm (Labeled l τ) -> CTerm (Mac h τ)

  data Env : Context -> Set where
   [] : Env []
   _∷_ : ∀ {Δ τ} -> CTerm τ -> (Γ : Env Δ) -> Env (τ ∷ Δ)
  
infixr 3 _,_
infixr 0 _$_
infixl 5 _>>=_

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
IsValue (Γ , Return j) = ⊥
IsValue (Γ , j >>= j₁) = ⊥
IsValue (Γ , ξ) = ⊤
IsValue (Γ , Throw j) = ⊥
IsValue (Γ , Catch j j₁) = ⊥
IsValue (Γ , Mac m) = ⊤
IsValue (Γ , Macₓ j) = ⊤
IsValue (Γ , label x j) = ⊥
IsValue (Γ , unlabel x j) = ⊥
IsValue (Γ , Res j) = ⊤
IsValue (Γ , ∙) = ⊥
IsValue (c₁ $ c₂) = ⊥
IsValue (If c Then t Else e) = ⊥
IsValue (m >>= k) = ⊥
IsValue (Catch m h) = ⊥
IsValue (unlabel p t) = ⊥
