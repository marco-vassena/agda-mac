module Untyped.Base where

open import Types public

-- Untyped bounded terms
-- A term of type Term n is a term that has at least n free variables,
-- i.e. n is a lower bound on the number of free variables.
-- For convenience in compound terms like App the subterms have the same
-- upper bound, see cast.
data Term (n : ℕ) : Set where
  True : Term n 
  False : Term n

  Var : Fin n -> Term n
  Abs : Term (suc n) -> Term n
  App : Term n -> Term n -> Term n

  If_Then_Else_ : Term n -> Term n -> Term n -> Term n

  Return : Term n -> Term n
  _>>=_ : Term n -> Term n -> Term n

  ξ : Term n
  Throw : Term n -> Term n
  Catch : Term n -> Term n -> Term n

  -- Constructor that denotes a successful Mac computation. 
  Mac : Term n -> Term n
  -- Constructor that denotes failure due to an exception
  Macₓ : Term n -> Term n

  Res : {{l : Label}} -> Term n -> Term n
  Resₓ : {{l : Label}} -> Term n -> Term n

  label : ∀ {l h} -> l ⊑ h -> Term n -> Term n
  unlabel : Term n -> Term n

  join : ∀ {l h} -> l ⊑ h -> Term n -> Term n

  --   Erased term
  ∙ : Term n

-- Typing judgments, which define well-typed terms.
data _⊢_∷_ (Δ : Context) : Term (length Δ) -> Ty -> Set where
  True : Δ ⊢ True ∷ Bool
  False : Δ ⊢ False ∷ Bool

  App : ∀ {t₁ t₂ α β} ->
           Δ ⊢ t₁ ∷ α => β ->
           Δ ⊢ t₂ ∷ α ->
           Δ ⊢ App t₁ t₂ ∷ β
  Abs : ∀ {t α β} ->
           α ∷ Δ ⊢ t ∷ β ->
           Δ ⊢ Abs t ∷ α => β

  Var : ∀ {τ} -> (p : τ ∈ Δ) -> Δ ⊢ Var (fin p) ∷ τ

  If_Then_Else_ : ∀ {α t₁ t₂ t₃} ->
               Δ ⊢ t₁ ∷ Bool ->
               Δ ⊢ t₂ ∷ α ->
               Δ ⊢ t₃ ∷ α ->
               Δ ⊢ If t₁ Then t₂ Else t₃ ∷ α

  Return : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ τ -> Δ ⊢ Return t ∷ Mac l τ

  _>>=_ : ∀ {α β t k l} ->
            Δ ⊢ t ∷ Mac l α ->
            Δ ⊢ k ∷ (α => Mac l β) ->
            Δ ⊢ t >>= k ∷ Mac l β

  ξ : Δ ⊢ ξ ∷ Exception

  Throw : ∀ {{l}} {τ t} -> Δ ⊢ t ∷ Exception -> Δ ⊢ Throw t ∷ Mac l τ

  Catch : ∀ {t h τ} {{l}} ->
          Δ ⊢ t ∷ Mac l τ ->
          Δ ⊢ h ∷ Exception => Mac l τ ->
          Δ ⊢ Catch t h ∷ Mac l τ

  -- IO and Mac are fused for simplicity
  Mac : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ τ -> Δ ⊢ Mac t ∷ Mac l τ

  Macₓ : ∀ {τ t} {{l}} -> Δ ⊢ t ∷ Exception -> Δ ⊢ Macₓ t ∷ Mac l τ

  label : ∀ {t τ l h} ->
          (p : l ⊑ h) ->
          Δ ⊢ t ∷ τ ->
          Δ ⊢ label p t ∷ Mac l (Labeled h τ)

  unlabel : ∀ {t τ l h} ->
              l ⊑ h ->
              Δ ⊢ t ∷ Labeled l τ ->
              Δ ⊢ unlabel t ∷ Mac h τ

  join : ∀ {t τ l h} ->
          (p : l ⊑ h) ->
          Δ ⊢ t ∷ Mac h τ ->
          Δ ⊢ join p t ∷ Mac l (Labeled h τ)

  Res : ∀ {t τ} {{l}} ->
        Δ ⊢ t ∷ τ ->
        Δ ⊢ Res t ∷ Labeled l τ

  Resₓ : ∀ {t} {{l τ}}  ->
        Δ ⊢ t ∷ Exception ->
        Δ ⊢ Resₓ t ∷ Labeled l τ

  ∙ : ∀ {τ} -> Δ ⊢ ∙ ∷ τ

infix 3 If_Then_Else_

infixl 1 _⊢_∷_

mutual
  -- A closed term is a term that carries around the context nedeed for evaluation
  -- We need additional constructors such as _$_ and If_Then_Else_ to explicitly distribute
  -- the same environment in the small step semantics
  data CTerm : Set where

    -- Closure: couples a well-typed term with an environment of the same context Δ
    _,_ : ∀ {n} (Γ : Env n) -> Term n -> CTerm 

    -- Closed term application
    _$_ : CTerm -> CTerm -> CTerm

    -- Closed IfThenElse
    If_Then_Else_ : CTerm -> CTerm -> CTerm -> CTerm

    _>>=_ : CTerm -> CTerm -> CTerm

    Catch : CTerm -> CTerm -> CTerm

    unlabel : CTerm -> CTerm

    join : ∀ {l h} -> l ⊑ h -> CTerm -> CTerm

    -- Erased closed term
    ∙ : CTerm

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
IsValue (Γ , join x t) = ⊥
IsValue (Γ , Res j) = ⊤
IsValue (Γ , Resₓ t) = ⊤
IsValue (Γ , ∙) = ⊥
IsValue (c₁ $ c₂) = ⊥
IsValue (If c Then t Else e) = ⊥
IsValue (m >>= k) = ⊥
IsValue (Catch m h) = ⊥
IsValue (unlabel t) = ⊥
IsValue (join x t) = ⊥
IsValue ∙ = ⊥

mutual
  -- Well-typed closed term
  data _::_ : CTerm -> Ty -> Set where
    _,_ : ∀ {Δ Γ' t' τ} -> (Γ : TEnv  Δ Γ') -> (t : Δ ⊢ t' ∷ τ) -> (Γ' , t') :: τ 
    _$_ : ∀ {f x α β} -> f :: (α => β) -> x :: α -> (f $ x) :: β
    If_Then_Else_ : ∀ {c t e α} -> c :: Bool -> t :: α -> e :: α -> (If c Then t Else e) :: α
    _>>=_ : ∀ {m k l α β} -> m :: Mac l α -> k :: (α => Mac l β) -> (m >>= k) :: Mac l β
    Catch : ∀ {m h l α} -> m :: Mac l α -> h :: (Exception => Mac l α) -> Catch m h :: Mac l α
    unlabel : ∀ {t τ l h} -> l ⊑ h -> t :: Labeled l τ -> unlabel t :: Mac h τ
    join : ∀ {t τ l h} -> (x : l ⊑ h) -> t :: Mac h τ -> join x t :: Mac l (Labeled h τ)

    ∙ : ∀ {τ} -> ∙ :: τ

  -- Typed environment
  data TEnv : (Δ : Context) -> Env (length Δ) -> Set where 
    [] : TEnv [] []
    _∷_ : ∀ {c τ Δ} {Γ : Env (length Δ)} -> c :: τ -> TEnv Δ Γ -> TEnv (τ ∷ Δ) (c ∷ Γ)
