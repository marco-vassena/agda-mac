module Semantics  where

open import Base public
open import Relation.Nullary using (¬_)

--Ale: Why is the semantics defined on typed-terms? Semantics is simply
-- semantics, no types.
-- We agree on that!

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

  BindEx : ∀ {α β t l Δ} {Γ : Env Δ} {e : Δ ⊢ t ∷ Exception} {k : CTerm (α => (Mac l β))} ->
           ((Γ , Macₓ e) >>= k) ⟼ (Γ , Throw e)  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)

  Throw : ∀ {Δ t τ l} {Γ : Env Δ} {e : Δ ⊢ t ∷ Exception} ->
            (Γ , Throw {Δ} {τ} e) ⟼ (Γ , Macₓ e)

  Dist-Catch : ∀ {Δ t₁ t₂ τ l} {Γ : Env Δ} {m : Δ ⊢ t₁ ∷ Mac l τ} {h : Δ ⊢ t₂ ∷ Exception => Mac l τ} ->
             (Γ , Catch m h) ⟼ Catch (Γ , m) (Γ , h)

  CatchCtx : ∀ {τ l} {m m' : CTerm (Mac l τ)} {h : CTerm (Exception => Mac l τ)} ->
             m ⟼ m' ->
             Catch m h ⟼ Catch m' h

  Catch : ∀ {Δ m τ l} {Γ : Env Δ} {t : Δ ⊢ m ∷ τ} {h : CTerm (Exception => Mac l τ)} ->
          Catch (Γ , Mac t) h ⟼ (Γ , (Return t))

  CatchEx : ∀ {Δ t τ l} {Γ : Env Δ} {e : Δ ⊢ t ∷ Exception} {h : CTerm (Exception => Mac l τ)} ->
              Catch (Γ , Macₓ e) h ⟼ (h $ Γ , e)

  -- Dist-label :  ∀ {Δ t τ l h} {Γ : Env Δ} {j : Δ ⊢ t ∷ τ} {p : l ⊑ h} ->
  --               (Γ , label p j) ⟼ label (Γ , j)


  -- labelCtx : ∀ {l h : Label} {τ : Ty} {c c' : CTerm τ} ->
  --           c ⟼ c' ->
  --           label {l} {h} c ⟼ label c'

  label : ∀ {Δ l h t τ} {Γ : Env Δ} {t : Δ ⊢ t ∷ τ} -> (p : l ⊑ h) ->
            (Γ , label p t) ⟼ (Γ , Return (Res t))

  Dist-unlabel : ∀ {Δ t τ l h} {Γ : Env Δ} {j : Δ ⊢ t ∷ Labeled l τ} {p : l ⊑ h} ->
                (Γ , unlabel p j) ⟼ unlabel p (Γ , j)

  unlabel : ∀ {Δ l h t τ} {Γ : Env Δ} {t : Δ ⊢ t ∷ τ} -> (p : l ⊑ h) ->
            unlabel p (Γ , Res t) ⟼ (Γ , Return t)

  unlabelCtx : ∀ {l h τ} {c c' : CTerm (Labeled l τ)} {p : l ⊑ h} ->
               c ⟼ c' ->
               unlabel p c ⟼ unlabel p c'

  -- From SequentialLIO. Is there a reason not to consider ∙ a value?
  -- Ale: it could be, but it is not part of the surface syntax.
  -- It looks that it can be a value (Marco, please check that)
  Hole : ∀ {Δ τ} {Γ : Env Δ} -> (Γ , ∙ {τ = τ}) ⟼ (Γ , ∙)

-- A closed term is a Redex if it can be reduced further
data Redex {τ : Ty} (c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c
