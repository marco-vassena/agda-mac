module Untyped.Semantics where

open import Untyped.Base public
open import Relation.Nullary using (¬_)

-- Call-by-need small step semantics
-- Note that Env contains closed terms not necessarily values
data _⟼_ : CTerm -> CTerm -> Set where

  -- Reduces the function in an application
  AppL : ∀ {c₁ c₂ x} -> c₁ ⟼ c₂ -> (c₁ $ x) ⟼ (c₂ $ x)

  -- Pushes a term in the environment
  Beta : ∀ {n t x} {Γ : Env n} -> (Γ , Abs t $ x) ⟼ (x ∷ Γ , t)

  -- Looks up a variable in the environment
  Lookup : ∀ {n} {p : Fin n} {Γ : Env n} -> (Γ , Var p) ⟼ lookup p Γ

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist-$ : ∀ {n} {Γ : Env n} {f x : Term n} -> (Γ , App f x) ⟼ ((Γ , f) $ (Γ , x))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {n} {Γ : Env n} {c t e : Term n} ->
              (Γ , If c Then t Else e) ⟼ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {c c' t e} -> c ⟼ c' ->
             (If c Then t Else e) ⟼ (If c' Then t Else e)

  IfTrue : ∀ {t e n} {Γ : Env n} -> (If (Γ , True) Then t Else e) ⟼ t

  IfFalse : ∀ {t e n} {Γ : Env n} -> (If (Γ , False) Then t Else e) ⟼ e

  Return : ∀ {n} {Γ : Env n} {t : Term n} ->
             (Γ , Return t) ⟼ (Γ , Mac t)

  Dist->>= : ∀ {n c k} {Γ : Env n} ->
              (Γ , c >>= k) ⟼ ((Γ , c) >>= (Γ , k))

  BindCtx : ∀ {m m' k} -> m ⟼ m' ->
            (m >>= k) ⟼ (m' >>= k)

  Bind : ∀ {n k} {Γ : Env n} {t : Term n} ->
           ((Γ , Mac t) >>= k) ⟼ (k $ (Γ , t))

  BindEx : ∀ {k n} {Γ : Env n} {e : Term n} ->
           ((Γ , Macₓ e) >>= k) ⟼ (Γ , Throw e)  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)

  Throw : ∀ {n} {Γ : Env n} {e : Term n} -> (Γ , Throw e) ⟼ (Γ , Macₓ e)

  Dist-Catch : ∀ {n} {Γ : Env n} {m h : Term n} -> (Γ , Catch m h) ⟼ Catch (Γ , m) (Γ , h)

  CatchCtx : ∀ {m m' h} -> m ⟼ m' -> Catch m h ⟼ Catch m' h

  Catch : ∀ {n h} {Γ : Env n} {t : Term n} -> Catch (Γ , Mac t) h ⟼ (Γ , (Return t))

  CatchEx : ∀ {h n} {Γ : Env n} {e : Term n} -> Catch (Γ , Macₓ e) h ⟼ (h $ Γ , e)

  label : ∀ {n l h} {Γ : Env n} {t : Term n} -> (p : l ⊑ h) -> (Γ , label p t) ⟼ (Γ , Return (Res h t))

  Dist-unlabel : ∀ {n} {Γ : Env n} {t : Term n} -> (Γ , unlabel t) ⟼ unlabel (Γ , t)

  unlabel : ∀ {n t l} {Γ : Env n} ->
            unlabel (Γ , Res l t) ⟼ (Γ , Return t)

  unlabelCtx : ∀ {c c'} -> c ⟼ c' ->
               unlabel c ⟼ unlabel c'

  Hole : ∀ {n} {Γ : Env n} -> (Γ , ∙) ⟼ (Γ , ∙)

  Hole' : ∙ ⟼ ∙

-- A closed term is a Redex if it can be reduced further
data Redex (c : CTerm) : Set where
  Step : ∀ {c' : CTerm} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : CTerm -> Set
NormalForm c = ¬ Redex c