module Base where

open import Relation.Nullary public

-- The security lattice (Label, _⊑_, _⊔_) is kept abstract
-- It will turned in a parameter to the module, but
-- at the moment Agda crashes with them

postulate Label : Set
postulate _⊑_ : Label -> Label -> Set
postulate _⊑?_ : (l h : Label) -> Dec (l ⊑ h)

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.List public
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) public
open import Data.Fin using (Fin ; zero ; suc) public
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
data _∈ᵗ_ : Ty -> Context -> Set where
 Here : ∀ {Δ τ} -> τ ∈ᵗ (τ ∷ Δ)
 There : ∀ {Δ α β} -> α ∈ᵗ Δ -> α ∈ᵗ (β ∷ Δ)

-- Transform τ ∈ᵗ Δ in Fin
fin : ∀ {τ Δ} -> τ ∈ᵗ Δ -> Fin (length Δ)
fin Here = zero
fin (There p) = suc (fin p)

-- Untyped terms
-- TODO combining terms with types (and therefore contexts)
-- could probably simplify the proofs, because
-- only terms with the correct type would be reported on case analysis.
data Term : Set where
  True : Term
  False : Term

  Var : ∀ {n} -> Fin n -> Term
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

  Res : Label -> Term -> Term

  label : ∀ {l h} -> l ⊑ h -> Term -> Term
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

  Var : ∀ {τ} -> (p : τ ∈ᵗ Δ) -> Δ ⊢ Var (fin p) ∷ τ

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
          (p : l ⊑ h) ->
          Δ ⊢ t ∷ τ ->
          Δ ⊢ label p t ∷ Mac l (Labeled h τ)

  unlabel : ∀ {t τ l h} ->
              l ⊑ h ->
              Δ ⊢ t ∷ Labeled l τ ->
              Δ ⊢ unlabel t ∷ Mac h τ

  Res : ∀ {t τ} {{l}} ->
        Δ ⊢ t ∷ τ ->
        Δ ⊢ Res l t ∷ Labeled l τ

  ∙ : ∀ {τ} -> Δ ⊢ ∙ ∷ τ

infix 3 If_Then_Else_

infixl 1 _⊢_∷_

mutual
  -- A closed term is a term that carries around the context nedeed for evaluation
  -- We need additional constructors such as _$_ and If_Then_Else_ to explicitly distribute
  -- the same environment in the small step semantics
  data CTerm : Set where

    -- Closure: couples a well-typed term with an environment of the same context Δ
    _,_ : ∀ {n} (Γ : Env n) -> Term -> CTerm 

    -- Closed term application
    _$_ : CTerm -> CTerm -> CTerm

    -- Closed IfThenElse
    If_Then_Else_ : CTerm -> CTerm -> CTerm -> CTerm

    _>>=_ : CTerm -> CTerm -> CTerm

    Catch : CTerm -> CTerm -> CTerm

    unlabel : CTerm -> CTerm

  Env : ℕ -> Set
  Env n = Vec CTerm n

infixr 3 _,_
infixr 0 _$_
infixl 5 _>>=_

-- Determines whether a closed term is a value or not
IsValue : CTerm -> Set
IsValue (Γ , True) = ⊤
IsValue (Γ , False) = ⊤
IsValue (Γ , App f x) = ⊥
IsValue (Γ , Abs x) = ⊤
IsValue (Γ , Var n) = ⊥
IsValue (Γ , If c Then t Else e) = ⊥
IsValue (Γ , Return x) = ⊥
IsValue (Γ , m >>= k) = ⊥
IsValue (Γ , ξ) = ⊤
IsValue (Γ , Throw e) = ⊥
IsValue (Γ , Catch m h) = ⊥
IsValue (Γ , Mac m) = ⊤
IsValue (Γ , Macₓ j) = ⊤
IsValue (Γ , label x t) = ⊥
IsValue (Γ , unlabel t) = ⊥
IsValue (Γ , Res l j) = ⊤
IsValue (Γ , ∙) = ⊤
IsValue (c₁ $ c₂) = ⊥
IsValue (If c Then t Else e) = ⊥
IsValue (m >>= k) = ⊥
IsValue (Catch m h) = ⊥
IsValue (unlabel t) = ⊥

mutual
  -- Well-typed closed term
  data _::_ : CTerm -> Ty -> Set where
    _,_ : ∀ {Δ Γ t τ} -> TEnv  Δ Γ -> Δ ⊢ t ∷ τ -> (Γ , t) :: τ 
    _$_ : ∀ {f x α β} -> f :: (α => β) -> x :: α -> (f $ x) :: β
    If_Then_Else_ : ∀ {c t e α} -> c :: Bool -> t :: α -> e :: α -> (If c Then t Else e) :: α
    _>>=_ : ∀ {m k l α β} -> m :: Mac l α -> k :: (α => Mac l β) -> (m >>= k) :: Mac l β
    Catch : ∀ {m h l α} -> m :: Mac l α -> h :: (Exception => Mac l α) -> Catch m h :: Mac l α
    unlabel : ∀ {t τ l h} {- p : l ⊑ h -} -> t :: Labeled l τ -> unlabel t :: Mac h τ

  -- Typed environment
  data TEnv : (Δ : Context) -> Env (length Δ) -> Set where 
    [] : TEnv [] []
    _∷_ : ∀ {c τ Δ} {Γ : Env (length Δ)} -> c :: τ -> TEnv Δ Γ -> TEnv (τ ∷ Δ) (c ∷ Γ)
