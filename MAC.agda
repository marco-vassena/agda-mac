module MAC where

open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

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
  
infixl 1 _⊢_∷_

mutual 
  -- A closed term is indexed by a type and carries around the context
  -- nedeed for evaluation
  data CTerm : (τ : Ty) -> Set where
    
    -- Closure: couples a well-typed term with an environment of the same context Δ
    _,_ : ∀ {Δ t τ} -> (Γ : Env Δ) -> (j : Δ ⊢ t ∷ τ) -> CTerm τ 
    
    -- Closed term application 
    -- We need this constructor in order to distribute the same environment in the two terms
    _$_ : ∀ {α β} -> CTerm (α => β) -> CTerm α -> CTerm β

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
IsValue (c₁ $ c₂) = ⊥

-- Call-by-need small step semantics
-- Note that Env contains closed terms not necessarily values
data _⟼_ : {τ : Ty} -> CTerm τ -> CTerm τ -> Set where

  -- Reduces the function in an application
  AppL : {α β : Ty} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} ->
         c₁ ⟼ c₂ -> (c₁ $ x) ⟼ (c₂ $ x)

  -- Pushes a term in the environment
  Beta : ∀ {Δ α β t} {v : CTerm α} {Γ : Env Δ} {j : α ∷ Δ ⊢ t ∷ β} ->
          (Γ , Abs j $ v) ⟼ (v ∷ Γ , j)

  -- Looks up a variable in the environment
  Lookup : ∀ {Δ τ} {i : τ ∈ Δ} {Γ : Env Δ} ->
           (Γ , Var i) ⟼ (i !! Γ)

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist : ∀ {Δ α β f x} {Γ : Env Δ} {j₁ : Δ ⊢ f ∷ α => β} {j₂ : Δ ⊢ x ∷ α} ->
         (Γ , App j₁ j₂) ⟼ ((Γ , j₁) $ (Γ , j₂))

-- A closed term is a redex if it can be reduced further
data Redex {τ : Ty} (c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c

-- Every closed term is either a value or can be reduced further
progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , App f x) = inj₁ (Step Dist)
progress (Γ , Abs t) = inj₂ tt
progress (Γ , Var x) = inj₁ (Step Lookup)
progress (f $ x) with progress f
progress (f $ x₁) | inj₁ (Step s) = inj₁ (Step (AppL s))
progress (Γ , App f x $ y) | inj₂ ()
progress (Γ , Abs t $ x) | inj₂ y = inj₁ (Step Beta)
progress (Γ , Var x $ y) | inj₂ ()
progress ((f $ x) $ y) | inj₂ ()

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

-- TODO move proves to separate module

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex (Γ , True) p (Step ())
valueNotRedex (Γ , False) p (Step ())
valueNotRedex (Γ , App j j₁) p r = p
valueNotRedex (Γ , Abs j) p (Step ())
valueNotRedex (Γ , Var x) p r = p
valueNotRedex (f $ x) p r = p

determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinism (AppL s₁) (AppL s₂) rewrite determinism s₁ s₂ = refl
determinism {c₁ = Γ , Abs j $ x} (AppL s₁) Beta = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₁)) -- AppL does not apply
determinism {c₁ = Γ , Abs j $ x} Beta (AppL s₂) = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₂)) -- Idem
determinism Beta Beta = refl
determinism Lookup Lookup = refl
determinism Dist Dist = refl

-- Type preservation is trivial because it is enforced by the definition of c₁ ⟼ c₂
-- in which two closed terms always have the same type.
preservation : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation _ = refl
