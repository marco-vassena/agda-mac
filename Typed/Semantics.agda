module Typed.Semantics where

open import Typed.Base public

-- Id as a CTerm
id : ∀ {α} {Δ} {{Γ : Env Δ}} -> CTerm (α => α)
id {{Γ = Γ}} = Γ , Abs (Var Here)

{-
  TODO I have not introduced the erasure function.
  Should this be moved in the security submodue?

  In the small step semantics there are two steps that reduce bullets.
    Dist-∙ : (Γ , ∙) ⟼ ∙
    Hole   : ∙ ⟼ ∙

  Another rule that has been considered instead of Dist-∙ is:
    THole : (Γ , ∙) ⟼ (Γ , ∙)

  Unforunately rules Hole and THole alone do not preserve distributivity.
  Consider for instance erasing the terms involved in the Dist-$ rule,
  when the whole expression is a sensitive computation of type Mac H α

         (Γ , App f x)   ⟼  (Γ , f)  $  (Γ , x)

               ↧ εᶜ              ↧ εᶜ

         (εᶜ-env Γ, ∙)   ⟼       ∙

  There is not such step because we removed Dist-∙. Note that adding
  also this step would make the small step semantics non deterministic
  because both Dist-∙ and THole would reduce (Γ , ∙).

  Also note that we cannot avoid to have two different bullets (Term and CTerm).
  If we had only the ∙ CTerm this same example would not go through as we would
  need a reduction (Γ , App f x) ⟼ ∙

  A Term bullet alone would also break distributivity.
  Composite CTerms such as f $ x could not properly be erased because they
  do not expose their enviroment. At best we could only apply the erasure
  homomorphically, but this is unsatisfactory.
  Consider the previous example:

    (Γ , App f x)      ⟼           (Γ , f)   $   (Γ , x)

         ↧ εᶜ                                 ↧ εᶜ

    (εᶜ-env Γ, ∙)       ⟼   (εᶜ-env Γ , εᶜ f)  $  (εᶜ-env Γ , εᶜ x)

  Lastly some steps have been slightly modified as follows:
  from c₁ ⟼ c₂ to c₁ ⟼ (id $ c₂).
  Consider the original version of the Return step:

    (Γ , Return x)     ⟼    (Γ , Mac x)

          ↧ εᶜ                    ↧ εᶜ

    (εᶜ-env Γ , ∙)     ⟼    (εᶜ-env Γ , ∙)

  The only step that applies here is Dist-∙ (THole has been ruled out), but the reduced term should be
  ∙ instead of (Γ , ∙). With the proposed adjustment, we obtain a CTerm bullet, because id $ x
  is a composite CTerm and it is collapsed to ∙ at once.
  Furthermore since id x = x, this change does not affect the meaning of any program.

      (Γ , Return x)     ⟼    id $ (Γ , Mac x)

          ↧ εᶜ                    ↧ εᶜ

    (εᶜ-env Γ , ∙)     ⟼    (εᶜ-env Γ , ∙)

-}
data _⟼_ : ∀ {τ} -> CTerm τ -> CTerm τ -> Set where
    -- Reduces the function in an application
  AppL : ∀ {α β} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} -> c₁ ⟼ c₂ -> (c₁ $ x) ⟼ (c₂ $ x)

  -- Pushes a term in the environment
  Beta : ∀ {Δ α β} {Γ : Env Δ} {t : Term (α ∷ Δ) β} {x : CTerm α} -> (Γ , Abs t $ x) ⟼ (id {{Γ}} $ (x ∷ Γ , t))

  -- Looks up a variable in the environment
  Lookup : ∀ {Δ τ} {Γ : Env Δ} {p : τ ∈ Δ} -> (Γ , Var p) ⟼ (id {{Γ}} $ (p !! Γ))

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist-$ : ∀ {Δ α β} {Γ : Env Δ} {f : Term Δ (α => β)} {x : Term Δ α} -> (Γ , App f x) ⟼ ((Γ , f) $ (Γ , x))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {Δ τ} {Γ : Env Δ} {c : Term Δ Bool} {t e : Term Δ τ} ->
              (Γ , If c Then t Else e) ⟼ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {τ} {c c' : CTerm Bool} {t e : CTerm τ} -> c ⟼ c' ->
             (If c Then t Else e) ⟼ (If c' Then t Else e)

  IfTrue : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , True) Then t Else e) ⟼ (id {{Γ}} $ t)

  IfFalse : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , False) Then t Else e) ⟼ (id {{Γ}} $ e)

  Return : ∀ {l Δ τ} {Γ : Env Δ} {t : Term Δ τ} ->
             (Γ , Return t) ⟼ (id {{Γ}} $ (Γ , Mac t))

  Dist->>= : ∀ {l Δ α β} {Γ : Env Δ} {c : Term Δ (Mac l α)} {k : Term Δ (α => Mac l β)} ->
              (Γ , c >>= k) ⟼ ((Γ , c) >>= (Γ , k))

  BindCtx : ∀ {l} {α β} {m m' : CTerm (Mac l α)} {k : CTerm (α => Mac l β)} ->
            m ⟼ m' ->
            (m >>= k) ⟼ (m' >>= k)

  Bind : ∀ {l Δ α β} {Γ : Env Δ} {t : Term Δ α} {k : CTerm (α => Mac l β)} ->
           ((Γ , Mac t) >>= k) ⟼ (k $ Γ , t)

  BindEx : ∀ {l Δ α β} {Γ : Env Δ} {e : Term Δ Exception} {k : CTerm (α => Mac l β)} ->
           ((Γ , Macₓ e) >>= k) ⟼ (id {{Γ}} $ (Γ , Throw e))  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)

  Throw : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {e : Term Δ Exception} -> (Γ , Throw {{l}} {{α}} e) ⟼ (id {{Γ}} $ (Γ , Macₓ e))

  Dist-Catch : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {m : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
                 (Γ , Catch m h) ⟼ Catch (Γ , m) (Γ , h)

  CatchCtx : ∀ {l α} {m m' : CTerm (Mac l α)} {h : CTerm (Exception => Mac l α)} ->
             m ⟼ m' ->
             Catch m h ⟼ Catch m' h

  Catch : ∀ {l : Label} {Δ} {α : Ty} {Γ : Env Δ} {t : Term Δ α} {h : CTerm (Exception => Mac l α)} ->
            -- (λ x . x) $ (Γ , Return e)
            Catch (Γ , Mac t) h ⟼ (id {{Γ}} $ (Γ , (Return t)))

  CatchEx : ∀ {l : Label} {Δ} {Γ : Env Δ} {α : Ty} {e : Term Δ Exception} {h : CTerm (Exception => Mac l α)} ->
            Catch (Γ , Macₓ e) h ⟼ (h $ (Γ , e))

  label : ∀ {l Δ h α} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
            (Γ , label p t) ⟼ (id {{Γ}} $ (Γ , Return (Res t)))

  Dist-unlabel : ∀ {l Δ α h} {Γ : Env Δ} {t : Term Δ (Labeled l α)} -> (p : l ⊑ h) ->
                 (Γ , unlabel p t) ⟼ unlabel p (Γ , t)

  unlabel : ∀ {l Δ h α} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
            unlabel p (Γ , Res t) ⟼ (id {{Γ}} $ (Γ , Return t))

  unlabelEx : ∀ {l Δ h α} {Γ : Env Δ} {e : Term Δ Exception} -> (p : l ⊑ h) ->
            unlabel {l} {α} {h}  p (Γ , Resₓ e) ⟼ (id {{Γ}} $ (Γ , Throw e))

  unlabelCtx : ∀ {l h α} {c c' : CTerm (Labeled l α)} -> (p : l ⊑ h) -> c ⟼ c' ->
               unlabel p c ⟼ unlabel p c'

  Dist-join : ∀ {l h α Δ} {Γ : Env Δ} {t : Term Δ (Mac h α)} -> (p : l ⊑ h) ->
                (Γ , join p t) ⟼ join p (Γ , t)

  joinCtx : ∀ {l h α} {c c' : CTerm (Mac h α)} -> (p : l ⊑ h) ->
               c ⟼ c' -> join p c ⟼ join p c'

  join : ∀ {l h α Δ} {Γ : Env Δ} {t : Term Δ α} (p : l ⊑ h) ->
              join p (Γ , Mac t) ⟼ (id {{Γ = Γ}} $ (Γ , (Return (Res t))))

  joinEx : ∀ {l h α Δ} {Γ : Env Δ} {e : Term Δ Exception} (p : l ⊑ h) ->
              join {α = α} p (Γ , Macₓ e) ⟼ (id {{Γ = Γ}} $ (Γ , Return (Resₓ e)))

  Dist-∙ : ∀ {Δ} {α : Ty} {Γ : Env Δ} -> (Γ , (∙ {_} {α})) ⟼ ∙

  Hole : ∀ {τ} -> (∙ {τ}) ⟼ ∙

-- A closed term is a Redex if it can be reduced further
data Redex {τ : Ty}(c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c
