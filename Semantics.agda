module Semantics  where

open import Base public
open import Relation.Nullary using (¬_)

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
  Dist-$ : ∀ {Δ α β f x} {Γ : Env Δ} {j₁ : Δ ⊢ f ∷ α => β} {j₂ : Δ ⊢ x ∷ α} ->
         (Γ , App j₁ j₂) ⟼ ((Γ , j₁) $ (Γ , j₂))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {Δ α t₁ t₂ t₃} {Γ : Env Δ} {c : Δ ⊢ t₁ ∷ Bool} {t : Δ ⊢ t₂ ∷ α} {e : Δ ⊢ t₃ ∷ α} ->
              (Γ , If c Then t Else e) ⟼ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {α} {c c' : CTerm Bool} {t e : CTerm α} ->
             c ⟼ c' ->
             (If c Then t Else e) ⟼ (If c' Then t Else e)

  IfTrue : ∀ {Δ α} {Γ : Env Δ} {t e : CTerm α} ->
           (If (Γ , True) Then t Else e) ⟼ t

  IfFalse : ∀ {Δ α} {Γ : Env Δ} {t e : CTerm α} -> 
             (If (Γ , False) Then t Else e) ⟼ e

  Return : ∀ {Δ t τ l}  {Γ : Env Δ} {c : Δ ⊢ t ∷ τ} ->
             (Γ , Return c) ⟼ (Γ , Mac c)

  Dist->>= : ∀ {Δ t₁ t₂ α β l} {Γ : Env Δ} ->
              {c : Δ ⊢ t₁ ∷ Mac l α} {k : Δ ⊢ t₂ ∷ α => (Mac l β)} ->
              (Γ , c >>= k) ⟼ ((Γ , c) >>= (Γ , k))

  BindCtx : ∀ {α β l} {m m' : CTerm (Mac l α)} {k : CTerm (α => (Mac l β))} ->
            m ⟼ m' -> 
            (m >>= k) ⟼ (m' >>= k)

  Bind : ∀ {α β t l Δ} {Γ : Env Δ} {t : Δ ⊢ t ∷ α} {k : CTerm (α => (Mac l β))} ->
           ((Γ , Mac t) >>= k) ⟼ (k $ (Γ , t))

-- A closed term is a Redex if it can be reduced further
data Redex {τ : Ty} (c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c
