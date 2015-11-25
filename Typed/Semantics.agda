module Typed.Semantics where

open import Typed.Base public

-- Id as a CTerm
id : ∀ {α} {Δ} {{Γ : Env Δ}} -> CTerm (α => α)
id {{Γ = Γ}} = Γ , Abs (Var Here)

-- c₁ ⇝ c₂ is the pure reduction of the pure term c₁ into c₂ 
data _⇝_ : ∀ {τ} -> CTerm τ -> CTerm τ -> Set where
  -- Reduces the function in an application
  AppL : ∀ {α β} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} -> c₁ ⇝ c₂ -> (c₁ $ x) ⇝ (c₂ $ x)

  -- Pushes a term in the environment
  Beta : ∀ {Δ α β} {Γ : Env Δ} {t : Term (α ∷ Δ) β} {x : CTerm α} -> (Γ , Abs t $ x) ⇝ (id {{Γ}} $ (x ∷ Γ , t))

  -- Looks up a variable in the environment
  Lookup : ∀ {Δ τ} {Γ : Env Δ} {p : τ ∈ Δ} -> (Γ , Var p) ⇝ (id {{Γ}} $ (p !! Γ))

  -- Distributes the environment forming two closures wrapped in a CLapp
  Dist-$ : ∀ {Δ α β} {Γ : Env Δ} {f : Term Δ (α => β)} {x : Term Δ α} -> (Γ , App f x) ⇝ ((Γ , f) $ (Γ , x))

  -- Distributes the environment to its subterms
  Dist-If : ∀ {Δ τ} {Γ : Env Δ} {c : Term Δ Bool} {t e : Term Δ τ} ->
              (Γ , If c Then t Else e) ⇝ (If (Γ , c) Then (Γ , t) Else (Γ , e))

  -- Evaluates the condition term
  IfCond : ∀ {τ} {c c' : CTerm Bool} {t e : CTerm τ} -> c ⇝ c' ->
             (If c Then t Else e) ⇝ (If c' Then t Else e)

  -- Reduces to the Then branch if the condition is True
  IfTrue : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , True) Then t Else e) ⇝ (id {{Γ}} $ t)

  -- Reduces to the Else branch if the condition is False
  IfFalse : ∀ {Δ τ} {t e : CTerm τ} {Γ : Env Δ} -> (If (Γ , False) Then t Else e) ⇝ (id {{Γ}} $ e)

  -- Transforms a Term bullet (Γ , ∙) in a closed term bullet ∙
  Dist-∙ : ∀ {Δ} {α : Ty} {Γ : Env Δ} -> (Γ , (∙ {_} {α})) ⇝ ∙

  -- Bullet reduces to itself
  Hole : ∀ {τ} -> (∙ {τ}) ⇝ ∙

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

    There isn't any step (εᶜ-env Γ, ∙) ⟼ ∙ because we removed Dist-∙.
    Note that adding also this step would make the small step semantics non deterministic
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

data Program (Δ : Context) (τ : Ty) : Set where
  ⟨_∥_⟩ : Memory Δ -> CTerm τ -> Program Δ τ

data _⟼_ {Δ₁ : Context} : ∀ {Δ₂ τ} -> Program Δ₁ τ -> Program Δ₂ τ -> Set where
  Pure : ∀ {τ} {m : Memory Δ₁} {c₁ c₂ : CTerm τ} -> c₁ ⇝ c₂ -> ⟨ m ∥ c₁ ⟩ ⟼ ⟨ m ∥ c₂ ⟩

  Return : ∀ {l Δ τ} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ τ} ->
             ⟨ m ∥ (Γ , Return t) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Mac t)) ⟩

  Dist->>= : ∀ {l Δ α β} {m : Memory Δ₁} {Γ : Env Δ} {c : Term Δ (Mac l α)} {k : Term Δ (α => Mac l β)} ->
              ⟨ m ∥ (Γ , c >>= k) ⟩ ⟼ ⟨ m ∥  ((Γ , c) >>= (Γ , k)) ⟩

  BindCtx : ∀ {l α β Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Mac l α)} {k : CTerm (α => Mac l β)} ->
            ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
            ⟨ m₁ ∥ (c₁ >>= k) ⟩ ⟼ ⟨ m₂ ∥ (c₂ >>= k) ⟩

  Bind : ∀ {l Δ α β} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} {k : CTerm (α => Mac l β)} ->
           ⟨ m ∥ ((Γ , Mac t) >>= k) ⟩ ⟼ ⟨ m ∥ (k $ Γ , t) ⟩

  -- Rethrown as in LIO. It could be also (Γ , Macₓ e)
  BindEx : ∀ {l Δ α β} {m : Memory Δ₁} {Γ : Env Δ} {e : Term Δ Exception} {k : CTerm (α => Mac l β)} ->
           ⟨ m ∥ ((Γ , Macₓ e) >>= k) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Throw e)) ⟩
           
  Throw : ∀ {l : Label} {Δ} {α : Ty} {m : Memory Δ₁} {Γ : Env Δ} {e : Term Δ Exception} ->
            ⟨ m ∥ (Γ , Throw {{l}} {{α}} e) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Macₓ e)) ⟩

  Dist-Catch : ∀ {l : Label} {Δ} {α : Ty} {m : Memory Δ₁} {Γ : Env Δ}
                 {c : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
                 ⟨ m ∥ (Γ , Catch c h) ⟩ ⟼ ⟨ m ∥ Catch (Γ , c) (Γ , h) ⟩

  CatchCtx : ∀ {l α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂}
               {c₁ c₂ : CTerm (Mac l α)} {h : CTerm (Exception => Mac l α)} ->
               ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
               ⟨ m₁ ∥ Catch c₁ h ⟩ ⟼ ⟨ m₂ ∥ Catch c₂ h ⟩

  Catch : ∀ {l : Label} {Δ} {α : Ty} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} {h : CTerm (Exception => Mac l α)} ->
            -- (λ x . x) $ (Γ , Return e)
            ⟨ m ∥ Catch (Γ , Mac t) h ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , (Return t))) ⟩

  CatchEx : ∀ {l : Label} {Δ} {m : Memory Δ₁} {Γ : Env Δ} {α : Ty}
              {e : Term Δ Exception} {h : CTerm (Exception => Mac l α)} ->
              ⟨ m ∥ Catch (Γ , Macₓ e) h ⟩ ⟼ ⟨ m ∥ (h $ (Γ , e)) ⟩

  label : ∀ {l Δ h α} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
            ⟨ m ∥ (Γ , label p t) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Return (Res t))) ⟩

  Dist-unlabel : ∀ {l Δ α h} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ (Labeled l α)} -> (p : l ⊑ h) ->
                 ⟨ m ∥ (Γ , unlabel p t) ⟩ ⟼ ⟨ m ∥ unlabel p (Γ , t) ⟩

  unlabel : ∀ {l Δ h α} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
            ⟨ m ∥ unlabel p (Γ , Res t) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Return t)) ⟩

  unlabelEx : ∀ {l Δ h α} {m : Memory Δ₁} {Γ : Env Δ} {e : Term Δ Exception} -> (p : l ⊑ h) ->
            ⟨ m ∥ unlabel {l} {α} {h}  p (Γ , Resₓ e) ⟩ ⟼ ⟨ m ∥ (id {{Γ}} $ (Γ , Throw e)) ⟩

  unlabelCtx : ∀ {l h α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Labeled l α)} -> (p : l ⊑ h) ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                 ⟨ m₁ ∥ unlabel p c₁ ⟩ ⟼ ⟨ m₂ ∥ unlabel p c₂ ⟩

  Dist-join : ∀ {l h α Δ} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ (Mac h α)} -> (p : l ⊑ h) ->
                ⟨ m ∥ (Γ , join p t) ⟩ ⟼ ⟨ m ∥ join p (Γ , t) ⟩

  joinCtx : ∀ {l h α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Mac h α)} -> (p : l ⊑ h) ->
               ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ join p c₁ ⟩ ⟼ ⟨ m₂ ∥ join p c₂ ⟩

  join : ∀ {l h α Δ} {m : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} (p : l ⊑ h) ->
            ⟨ m ∥ join p (Γ , Mac t) ⟩ ⟼ ⟨ m ∥ (id {{Γ = Γ}} $ (Γ , (Return (Res t)))) ⟩

  joinEx : ∀ {l h α Δ} {m : Memory Δ₁} {Γ : Env Δ} {e : Term Δ Exception} (p : l ⊑ h) ->
              ⟨ m ∥ join {α = α} p (Γ , Macₓ e) ⟩ ⟼ ⟨ m ∥ (id {{Γ = Γ}} $ (Γ , Return (Resₓ e))) ⟩

  

  Dist-new : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
           ⟨ m₁ ∥ Γ , new p t ⟩ ⟼ ⟨ m₁ ∥ new p (Γ , t) ⟩

  Dist-write : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} {r : Term Δ (Ref h α)} -> (p : l ⊑ h) ->
          ⟨ m₁ ∥ Γ , write p r t ⟩ ⟼ ⟨ m₁ ∥ write p (Γ , r) (Γ , t) ⟩

  Dist-read : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {t : Term Δ (Ref l α)} -> (p : l ⊑ h) ->
           ⟨ m₁ ∥ Γ , read p t ⟩ ⟼ ⟨ m₁ ∥ read p (Γ , t) ⟩

  newCtx : ∀ {l h α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm α} -> (p : l ⊑ h) ->
          ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ new p c₁ ⟩ ⟼ ⟨ m₂ ∥ (new p c₂) ⟩

  new : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {t : Term Δ α} -> (p : l ⊑ h) ->
          ⟨ m₁ ∥ new p (Γ , t) ⟩ ⟼ ⟨ (Γ , t) ∷ m₁ ∥ id {{Γ = Γ}} $ (Γ , Return (Ref (Here {α ∷ Δ₁} ))) ⟩

  writeCtx :  ∀ {l h α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Ref h α)} {c₃ : CTerm α} ->
                (p : l ⊑ h) -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                ⟨ m₁ ∥ write p c₁ c₃ ⟩ ⟼ ⟨ m₂ ∥ write p c₂ c₃ ⟩

  write : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {c : CTerm α} ->
            (p : l ⊑ h) (r : α ∈ Δ₁) ->
          ⟨ m₁ ∥ (write p (Γ , (Ref r)) c) ⟩ ⟼ ⟨ m₁ [ r ]≔ c ∥ id {{Γ = Γ}} $ (Γ , Return （）) ⟩

  readCtx : ∀ {l h α Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Ref l α)} -> (p : l ⊑ h) ->
            ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
            ⟨ m₁ ∥ (read p c₁) ⟩ ⟼ ⟨ m₂ ∥ (read p c₂) ⟩

  -- ⟨ m₁ ∥ read p r ⟩ ⟼ ⟨ m₁ ∥ return (r !! m₁) ⟩
  read : ∀ {l h α Δ} {m₁ : Memory Δ₁} {Γ : Env Δ} {r : α ∈ Δ₁} -> (p : l ⊑ h) ->
            ⟨ m₁ ∥ (read p (Γ , (Ref r))) ⟩ ⟼ ⟨ m₁ ∥ (Γ , Abs (Return (Var Here))) $ (r !! m₁) ⟩

-- TODO maybe define Redex for Program instead of single term  

-- A closed term is a Redex if it can be reduced further in a certain memory configuration
data Redex {Δ₁ : Context} {τ : Ty} (m₁ : Memory Δ₁) (c₁ : CTerm τ) : Set where
  Step : ∀ {Δ₂} {m₂ : Memory Δ₂} {c₂ : CTerm τ} -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Redex m₁ c₁

-- Normal forms
-- A closed term is in normal form for a given memory configuration
-- if it cannot be reduced further
NormalForm : ∀ {Δ₁ τ} -> Memory Δ₁ -> CTerm τ -> Set
NormalForm m c = ¬ Redex m c
