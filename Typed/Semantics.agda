module Typed.Semantics where

open import Typed.Base public

data _⟼_ : ∀ {τ} -> CTerm τ -> CTerm τ -> Set where
    -- Reduces the function in an application
  AppL : ∀ {α β} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} -> c₁ ⟼ c₂ -> (c₁ $ x) ⟼ (c₂ $ x)

  -- Pushes a term in the environment
  Beta : ∀ {Δ α β} {Γ : Env Δ} {t : Term (α ∷ Δ) β} {x : CTerm α} -> (Γ , Abs t $ x) ⟼ (x ∷ Γ , t)

  -- Looks up a variable in the environment
  Lookup : ∀ {Δ τ} {Γ : Env Δ} {p : τ ∈ Δ} -> (Γ , Var p) ⟼ (p !! Γ)

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist-$ : ∀ {Δ α β} {Γ : Env Δ} {f : Term Δ (α => β)} {x : Term Δ α} -> (Γ , App f x) ⟼ ((Γ , f) $ (Γ , x))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {Δ τ} {Γ : Env Δ} {c : Term Δ Bool} {t e : Term Δ τ} ->
              (Γ , If c Then t Else e) ⟼ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {τ} {c c' : CTerm Bool} {t e : CTerm τ} -> c ⟼ c' ->
             (If c Then t Else e) ⟼ (If c' Then t Else e)

  IfTrue : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , True) Then t Else e) ⟼ t

  IfFalse : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , False) Then t Else e) ⟼ e

  Return : ∀ {l Δ τ} {Γ : Env Δ} {t : Term Δ τ} ->
             (Γ , Return t) ⟼ (Γ , Mac t)

  Dist->>= : ∀ {l Δ α β} {Γ : Env Δ} {c : Term Δ (Mac l α)} {k : Term Δ (α => Mac l β)} ->
              (Γ , c >>= k) ⟼ ((Γ , c) >>= (Γ , k))

  BindCtx : ∀ {l} {α β} {m m' : CTerm (Mac l α)} {k : CTerm (α => Mac l β)} -> 
            m ⟼ m' ->
            (m >>= k) ⟼ (m' >>= k)

  Bind : ∀ {l Δ α β} {Γ : Env Δ} {t : Term Δ α} {k : CTerm (α => Mac l β)} ->
           ((Γ , Mac t) >>= k) ⟼ (k $ Γ , t)

  BindEx : ∀ {l Δ α} {Γ : Env Δ} {e : Term Δ Exception} {k : CTerm (Exception => Mac l α)} ->
           ((Γ , Macₓ e) >>= k) ⟼ (Γ , Throw e)  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)

  Throw : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {e : Term Δ Exception} -> (Γ , Throw e) ⟼ (Γ , Macₓ e)

  Dist-Catch : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {m : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} -> 
                 (Γ , Catch m h) ⟼ Catch (Γ , m) (Γ , h)

  CatchCtx : ∀ {l α} {m m' : CTerm (Mac l α)} {h : CTerm (Exception => Mac l α)} -> 
             m ⟼ m' -> 
             Catch m h ⟼ Catch m' h

  Catch : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {t : Term Δ α} {h : CTerm (Exception => Mac l α)} -> 
            Catch (Γ , Mac t) h ⟼ (Γ , (Return t))

  CatchEx : ∀ {l : Label} {Δ}  {α : Ty} {Γ : Env Δ} {e : Term Δ Exception} {h : CTerm (Exception => Mac l α)} -> 
            Catch (Γ , Macₓ e) h ⟼ (h $ Γ , e)

  label : ∀ {l Δ h α} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) -> 
            (Γ , label p t) ⟼ (Γ , Return (Res t))

  Dist-unlabel : ∀ {l Δ α h} {Γ : Env Δ} {p : l ⊑ h} {t : Term Δ (Labeled l α)} -> 
                 (Γ , unlabel p t) ⟼ unlabel p (Γ , t)

  -- TODO p not implicit
  unlabel : ∀ {l Δ h α} {Γ : Env Δ} {p : l ⊑ h} {t : Term Δ α} ->
            unlabel p (Γ , Res t) ⟼ (Γ , Return t)

  unlabelCtx : ∀ {l h α} {p : l ⊑ h} {c c' : CTerm (Labeled l (Mac h α))} -> c ⟼ c' ->
               unlabel p c ⟼ unlabel p c'

  Hole : ∀ {Δ} {α : Ty} {Γ : Env Δ} -> (Γ , (∙ {_} {α})) ⟼ (Γ , ∙)

  Hole' : {α : Ty} -> (∙ {α}) ⟼ ∙
