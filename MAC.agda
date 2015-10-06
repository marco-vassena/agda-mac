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
IsValue (Γ , If c Then t Else e) = ⊥
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

  IfCond : ∀ {Δ Δ' α t₁ t₂ t₃} {Γ : Env Δ} {Γ' : Env Δ'}
             {c c' : Δ ⊢ t₁ ∷ Bool} {t : Δ ⊢ t₂ ∷ α} {e : Δ ⊢ t₃ ∷ α} ->
             (Γ , c) ⟼ (Γ , c') ->
             (Γ , (If c Then t Else e)) ⟼ (Γ , (If c' Then t Else e))

  IfTrue : ∀ {Δ α t₂ t₃} {Γ : Env Δ} {t : Δ ⊢ t₂ ∷ α} {e : Δ ⊢ t₃ ∷ α} -> 
             (Γ , (If True Then t Else e)) ⟼ (Γ , t)

  IfFalse : ∀ {Δ α t₂ t₃} {Γ : Env Δ} {t : Δ ⊢ t₂ ∷ α} {e : Δ ⊢ t₃ ∷ α} -> 
             (Γ , (If False Then t Else e)) ⟼ (Γ , e)


-- A closed term is a redex if it can be reduced further
data Redex {τ : Ty} (c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

-- TODO move proves to separate module

-- Every closed term is either a value or can be reduced further

-- The addition of If_Then_Else_ seems to break progress
-- In the typing rules the context Δ is fixed, i.e.
-- it does not change within a rule, except in the lambda abstraction
-- where it is extended with a new variable.

-- In CTerm we have to existentiall quantify over the environment Γ.
-- This is needed because to build a closure (_,_)
-- Given the two constructors _$_ and _,_ when we open
-- a closure we cannot rebuild the term needed for 
-- the small step IfCond, because the Γ may have changed in Γ'

progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , App c c₁) = inj₁ (Step Dist)
progress (Γ , Abs c) = inj₂ tt
progress (Γ , Var x) = inj₁ (Step Lookup)
progress (Γ , (If True Then t Else e)) = inj₁ (Step IfTrue)
progress (Γ , (If False Then t Else e)) = inj₁ (Step IfFalse)
progress (Γ , (If App (App c c₁) c₂ Then t Else e)) = {!!}
progress (Γ , (If App (Abs c) c₁ Then t₁ Else e)) = inj₁ (Step (IfCond {!Beta!}))
progress (Γ , (If App (Var x) c₁ Then t Else e)) = {!!}
progress (Γ , (If App (If c Then c₁ Else c₂) c₃ Then t Else e)) = {!!} -- 
progress (Γ , (If Var x Then t Else e)) = inj₁ (Step (IfCond {!Lookup!})) -- We could store something f $ x in Γ
progress (Γ , (If If c Then c₁ Else c₂ Then t Else e)) = {!!}
progress (f $ x) with progress f
progress (f $ x) | inj₁ (Step s) = inj₁ (Step (AppL s))
progress (Γ , App j j₁ $ x) | inj₂ ()
progress (Γ , Abs j $ x) | inj₂ y = inj₁ (Step Beta)
progress (Γ , Var x $ x₁) | inj₂ ()
progress (Γ , (If j Then j₁ Else j₂) $ x) | inj₂ ()
progress ((f $ f₁) $ x) | inj₂ ()

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex (Γ , True) p (Step ())
valueNotRedex (Γ , False) p (Step ())
valueNotRedex (Γ , App j j₁) p r = p
valueNotRedex (Γ , Abs j) p (Step ())
valueNotRedex (Γ , Var x) p r = p
valueNotRedex (Γ , If c Then t Else e) p r = p
valueNotRedex (f $ x) p r = p

determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinism (AppL s₁) (AppL s₂) rewrite determinism s₁ s₂ = refl
determinism {c₁ = Γ , Abs j $ x} (AppL s₁) Beta = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₁)) -- AppL does not apply
determinism {c₁ = Γ , Abs j $ x} Beta (AppL s₂) = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₂)) -- Idem
determinism Beta Beta = refl
determinism Lookup Lookup = refl
determinism Dist Dist = refl
determinism (IfCond s₁) (IfCond s₂) with determinism s₁ s₂
determinism (IfCond s₁) (IfCond s₂) | refl = refl
determinism (IfCond s₁) IfTrue = ⊥-elim (valueNotRedex (_ , True) tt (Step s₁))
determinism (IfCond s₁) IfFalse = ⊥-elim (valueNotRedex (_ , False) tt (Step s₁))
determinism IfTrue (IfCond s₂) = ⊥-elim (valueNotRedex (_ , True) tt (Step s₂))
determinism IfTrue IfTrue = refl
determinism IfFalse (IfCond s₂) = ⊥-elim (valueNotRedex (_ , False) tt (Step s₂))
determinism IfFalse IfFalse = refl

-- Type preservation is trivial because it is enforced by the definition of c₁ ⟼ c₂
-- in which two closed terms always have the same type.
preservation : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation _ = refl
