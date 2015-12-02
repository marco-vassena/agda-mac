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

  Ref : ∀ {{l}} -> (α : Ty) -> Term Δ (Ref l α)

  read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)

  write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)
  
  new : ∀ {α l h} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Ref h α))

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
    write : ∀ {α l h} -> l ⊑ h -> CTerm (Ref h α) -> CTerm α -> CTerm (Mac l （）)
    read : ∀ {α l h} -> l ⊑ h -> CTerm (Ref l α) -> CTerm (Mac h α)
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

-- Lookup
_!!_ : ∀ {τ Δ} -> τ ∈ Δ -> Env Δ -> CTerm τ
Here !! (x ∷ Γ) = x
There p !! (x ∷ Γ) = p !! Γ

infixr 6 _!!_

-- Update
_[_]≔_ : ∀ {τ Δ} -> Env Δ -> τ ∈ Δ -> CTerm τ -> Env Δ
_ ∷ Γ [ Here ]≔ v = v ∷ Γ
x ∷ Γ [ There i ]≔ v = x ∷ (Γ [ i ]≔ v)

infixr 2 _[_]≔_

-- The proof that a certain term is a value
data IsTValue {Δ : Context} : ∀ {τ} -> Term Δ τ -> Set where
  （） : IsTValue （）
  True : IsTValue True
  False : IsTValue False
  Abs : ∀ {α β} (t : Term (α ∷ Δ) β) -> IsTValue (Abs t)
  ξ : IsTValue ξ
  Mac : ∀ {α} {l : Label} (t : Term Δ α) -> IsTValue (Mac t)
  Macₓ : ∀ {α} {l : Label} (e : Term Δ Exception) -> IsTValue (Macₓ {α = α} e)
  Res : ∀ {α} {l : Label} (t : Term Δ α) -> IsTValue (Res t)
  Resₓ : ∀ {α} {l : Label} (e : Term Δ Exception) -> IsTValue (Resₓ {α = α} e)
  Ref : ∀ {l : Label} -> (α : Ty) -> IsTValue (Ref α)

data IsValue {τ : Ty} : CTerm τ -> Set where
  _,_ : ∀ {Δ} {t : Term Δ τ} -> (Γ : Env Δ) -> IsTValue t -> IsValue (Γ , t)

--------------------------------------------------------------------------------

-- Now that we have memory we have to ensure that memory references are all valid.
-- The following data type is such a proof.

data ValidT {Δ} (Δᵐ : Context) : ∀ {τ} -> Term Δ τ -> Set where
  （） : ValidT Δᵐ （）
  True : ValidT Δᵐ True
  False : ValidT Δᵐ False

  Var : ∀ {τ} -> (p : τ ∈ Δ) -> ValidT Δᵐ (Var p)
  App : ∀ {α β}{f : Term Δ (α => β)} {x : Term Δ α} ->
          ValidT Δᵐ f -> ValidT Δᵐ x -> ValidT Δᵐ (App f x)
  Abs : ∀ {α β} {t : Term (α ∷ Δ) β} -> ValidT Δᵐ t -> ValidT Δᵐ (Abs t)

  ξ : ValidT Δᵐ ξ

  Mac : ∀ {α} {l : Label} {t : Term Δ α} ->
          ValidT Δᵐ t -> ValidT Δᵐ (Mac t)
  Macₓ : ∀ {α} {l : Label} {e : Term Δ Exception} ->
           ValidT Δᵐ e -> ValidT Δᵐ (Macₓ {α = α} e)

  Res : ∀ {α}  {l : Label} {t : Term Δ α} ->
           ValidT Δᵐ t -> ValidT Δᵐ (Res t)
  Resₓ : ∀ {α} {l : Label}{e : Term Δ Exception} ->
           ValidT Δᵐ e -> ValidT Δᵐ (Resₓ {α = α} e)

  Ref : ∀ {α} {l : Label} -> (r : α ∈ Δᵐ) -> ValidT Δᵐ (Ref α)

  If_Then_Else_ : ∀ {α} {c : Term Δ Bool} {t e : Term Δ α} ->
                  ValidT Δᵐ c -> ValidT Δᵐ t -> ValidT Δᵐ e -> ValidT Δᵐ (If c Then t Else e)

  Return : ∀ {{l}} {α} {t : Term Δ α} -> ValidT Δᵐ t -> ValidT Δᵐ (Return t)
  
  _>>=_ : ∀ {{l}} {α β} {t₁ : Term Δ (Mac l α)} {t₂ : Term Δ (α => Mac l β)} ->
            ValidT Δᵐ t₁ -> ValidT Δᵐ t₂ -> ValidT Δᵐ (t₁ >>= t₂)

  Throw : ∀ {{l α}} {t : Term Δ Exception} ->
            ValidT Δᵐ t -> ValidT Δᵐ (Throw {{l = l}} t)

  Catch : ∀ {{l}} {α}  -> {t : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
            ValidT Δᵐ t -> ValidT Δᵐ h -> ValidT Δᵐ (Catch t h)

  label : ∀ {l h α} {t : Term Δ α} -> (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (label p t)
  unlabel : ∀ {l h α} {t : Term Δ (Labeled l α)} ->
              (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (unlabel p t)

  join : ∀ {l h α} {t : Term Δ (Mac h α)} ->
           (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (join p t)

  read : ∀ {α l h} {t : Term Δ (Ref l α)} ->
           (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (read p t)

  write : ∀ {α l h} {t₁ : Term Δ (Ref h α)} -> {t₂ : Term Δ α} ->
            (p : l ⊑ h) -> ValidT Δᵐ t₁ -> ValidT Δᵐ t₂ -> ValidT Δᵐ (write p t₁ t₂)
  
  new : ∀ {α l h} {t : Term Δ α} -> (p : l ⊑ h) -> ValidT Δᵐ t ->
          ValidT Δᵐ (new p t)
          
  ∙ : ∀ {τ} -> ValidT Δᵐ (∙ {Δ} {τ})

mutual

 data ValidEnv (Δᵐ : Context) : ∀ {Δ} -> Env Δ -> Set where
   [] : ValidEnv Δᵐ []
   _∷_ : ∀ {τ Δ} {Γ : Env Δ} {c : CTerm τ} -> Valid Δᵐ c -> ValidEnv Δᵐ Γ -> ValidEnv Δᵐ (c ∷ Γ)
   
 data Valid (Δᵐ : Context) : ∀ {τ} -> CTerm τ -> Set where
   _,_ : ∀ {Δ τ} -> {Γ : Env Δ} {t : Term Δ τ} -> ValidEnv Δᵐ Γ -> ValidT Δᵐ t -> Valid Δᵐ (Γ , t)
   _$_ : ∀ {α β} {c₁ : CTerm (α => β)} {c₂ : CTerm α} -> Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (c₁ $ c₂)
   If_Then_Else_ :  ∀ {τ} {c₁ : CTerm Bool} {c₂ c₃ : CTerm τ} ->
                   Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ c₃ -> Valid Δᵐ (If c₁ Then c₂ Else c₃)
   _>>=_ : ∀ {l α β} {c₁ : CTerm (Mac l α)} {c₂ : CTerm (α => Mac l β)} ->
             Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (c₁ >>= c₂)
   Catch : ∀ {l α} -> {c₁ : CTerm (Mac l α)} {c₂ : CTerm (Exception => Mac l α)} ->
             Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (Catch c₁ c₂)
   unlabel : ∀ {l τ h} {c : CTerm (Labeled l τ)} -> (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (unlabel p c)
   join : ∀ {l h α} {c : CTerm (Mac h α)} -> (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (join p c)
   read : ∀ {α l h} {c : CTerm (Ref l α)} (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (read p c)
   write : ∀ {α l h} {c₁ : CTerm (Ref h α)} {c₂ : CTerm α} ->
             (p : l ⊑ h) -> Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (write p c₁ c₂)
   ∙ : ∀ {τ} -> Valid Δᵐ (∙ {τ})

ValidMemory : ∀ {Δᵐ} -> (m : Memory Δᵐ) -> Set
ValidMemory {Δᵐ} m = ValidEnv Δᵐ m
