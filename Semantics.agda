module Semantics  where

open import Base public
open import Relation.Nullary using (¬_)

-- Retrieves the term of the type given by the reference from an environment in a safe way
-- _!!_ : ∀ {Δ Γ τ} -> τ ∈ Δ -> TEnv Δ Γ -> CTerm τ
-- Here !! (t ∷ _) = t
-- There r !! (_ ∷ e) = r !! e

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
  Dist-$ : ∀ {f x n} {Γ : Env n} -> (Γ , App f x) ⟼ ((Γ , f) $ (Γ , x))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {c t e n} {Γ : Env n} ->
              (Γ , If c Then t Else e) ⟼ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {c c' t e} -> c ⟼ c' ->
             (If c Then t Else e) ⟼ (If c' Then t Else e)

  IfTrue : ∀ {t e n} {Γ : Env n} -> (If (Γ , True) Then t Else e) ⟼ t

  IfFalse : ∀ {t e n} {Γ : Env n} -> (If (Γ , False) Then t Else e) ⟼ e

  Return : ∀ {c n} {Γ : Env n} ->
             (Γ , Return c) ⟼ (Γ , Mac c)

  Dist->>= : ∀ {n c k} {Γ : Env n} ->
              (Γ , c >>= k) ⟼ ((Γ , c) >>= (Γ , k))

  BindCtx : ∀ {m m' k} -> m ⟼ m' ->
            (m >>= k) ⟼ (m' >>= k)

  Bind : ∀ {t k n} {Γ : Env n} ->
           ((Γ , Mac t) >>= k) ⟼ (k $ (Γ , t))

  BindEx : ∀ {e k n} {Γ : Env n} ->
           ((Γ , Macₓ e) >>= k) ⟼ (Γ , Throw e)  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)

  Throw : ∀ {e n} {Γ : Env n} -> (Γ , Throw e) ⟼ (Γ , Macₓ e)

  Dist-Catch : ∀ {m h n} {Γ : Env n} -> (Γ , Catch m h) ⟼ Catch (Γ , m) (Γ , h)

  CatchCtx : ∀ {m m' h} -> m ⟼ m' -> Catch m h ⟼ Catch m' h

  Catch : ∀ {t h n} {Γ : Env n} -> Catch (Γ , Mac t) h ⟼ (Γ , (Return t))

  CatchEx : ∀ {h e n} {Γ : Env n} -> Catch (Γ , Macₓ e) h ⟼ (h $ Γ , e)

  label : ∀ {t n l h} {Γ : Env n} -> (p : l ⊑ h) -> (Γ , label p t) ⟼ (Γ , Return (Res h t))

  Dist-unlabel : ∀ {t n} {Γ : Env n} -> (Γ , unlabel t) ⟼ unlabel (Γ , t)

  unlabel : ∀ {n t l} {Γ : Env n} ->
            unlabel (Γ , Res l t) ⟼ (Γ , Return t)

  unlabelCtx : ∀ {c c'} -> c ⟼ c' ->
               unlabel c ⟼ unlabel c'

  Hole : ∀ {n} {Γ : Env n} -> (Γ , ∙) ⟼ (Γ , ∙)

-- A closed term is a Redex if it can be reduced further
data Redex (c : CTerm) : Set where
  Step : ∀ {c' : CTerm} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : CTerm -> Set
NormalForm c = ¬ Redex c
