module Typed.Base where

open import Types public

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
  
  -- Erased term ∙
  ∙ : ∀ {τ} -> Term Δ τ

infixr 3 _,_
infixr 0 _$_
infixl 5 _>>=_

mutual
  data CTerm : Ty -> Set where
    _,_ : ∀ {Δ τ} -> Env Δ -> Term Δ τ -> CTerm τ
    _$_ : ∀ {α β} -> CTerm (α => β) -> CTerm α -> CTerm β
    If_Then_Else_ : ∀ {τ} -> CTerm Bool -> CTerm τ -> CTerm τ -> CTerm τ
    _>>=_ : ∀ {l α β} -> CTerm (Mac l α) -> CTerm (α => Mac l β) -> CTerm (Mac l β)
    Catch : ∀ {l α} -> CTerm (Mac l α) -> CTerm (Exception => Mac l α) -> CTerm (Mac l α)
    unlabel : ∀ {l τ h} -> l ⊑ h -> CTerm (Labeled l τ) -> CTerm (Mac h τ)
    join : ∀ {l h α} -> l ⊑ h -> CTerm (Mac h α) -> CTerm (Mac l (Labeled h α))

    -- Erased closed term
    ∙ : ∀ {τ} -> CTerm τ

  data Env : (Δ : Context) -> Set where
    [] : Env []
    _∷_ : ∀ {Δ τ} -> CTerm τ -> Env Δ -> Env (τ ∷ Δ)


-- I will start first with concrete memory containing closed terms
-- to implement references and then abstract over that with a more
-- generic Store.
-- The question I cannot answer right now is given
-- a store Store (A : Ty -> Set) : (Δ : Context) : Set
-- how can I abstract over generic read/write operations?

-- data Memory : (Δ : Context) -> Set where
--   [] : Memory []
--   _∷_ : ∀ {τ Δ} -> CTerm τ -> Memory Δ -> Memory (τ ∷ Δ)

-- At the moment momory is completely the same as Env
Memory : Context -> Set
Memory = Env

_!!_ : ∀ {τ Δ} -> τ ∈ Δ -> Env Δ -> CTerm τ
Here !! (x ∷ Γ) = x
There p !! (x ∷ Γ) = p !! Γ

infixr 6 _!!_

-- Determines whether a closed term is a value or not
IsValue : ∀ {τ} -> CTerm τ -> Set
IsValue (Γ , （）) = ⊤
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
IsValue (Γ , unlabel x t) = ⊥
IsValue (Γ , join p t) = ⊥
IsValue (Γ , Res t) = ⊤
IsValue (Γ , Resₓ e) = ⊤
IsValue (Γ , ∙) = ⊥
IsValue (c₁ $ c₂) = ⊥
IsValue (If c Then t Else e) = ⊥
IsValue (m >>= k) = ⊥
IsValue (Catch m h) = ⊥
IsValue (unlabel p t) = ⊥
IsValue (join p m) = ⊥
IsValue ∙ = ⊥
