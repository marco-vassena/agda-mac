module Untyped.Proofs where

open import Untyped.Semantics
open import Data.Sum
open import Relation.Binary.PropositionalEquality

getFunPureStep : ∀ {c₁ c₂ α β} -> c₁ :: (α => β) -> c₁ ⟼ c₂ -> c₁ ⇝ c₂
getFunPureStep (Γ , App t t₃) (Pure x) = x
getFunPureStep (Γ , Abs t₁) (Pure x) = x
getFunPureStep (Γ , Var p) (Pure x) = x
getFunPureStep (Γ , (If t Then t₄ Else t₅)) (Pure x) = x
getFunPureStep (Γ , ∙) (Pure x) = x
getFunPureStep (f $ x) (Pure s) = s
getFunPureStep (If c Then t Else e) (Pure s) = s
getFunPureStep ∙ (Pure s) = s

getBoolPureStep : ∀ {c₁ c₂} -> c₁ :: Bool -> c₁ ⟼ c₂ -> c₁ ⇝ c₂
getBoolPureStep (Γ , True) (Pure ())
getBoolPureStep (Γ , False) (Pure ())
getBoolPureStep (Γ , App f x) (Pure s) = s
getBoolPureStep (Γ , Var p) (Pure s) = s
getBoolPureStep (Γ , (If c Then t Else e)) (Pure s) = s
getBoolPureStep (Γ , ∙) (Pure s) = s
getBoolPureStep (f $ x) (Pure s) = s
getBoolPureStep (If c Then t Else e) (Pure s) = s
getBoolPureStep ∙ (Pure s) = s

-- Every well-typed closed term is either a value or can be reduced further
progress : ∀ {c τ} -> c :: τ -> (Redex c) ⊎ (IsValue c)
progress (Γ , （）) = inj₂ (_ , （）)
progress (Γ , True) = inj₂ (_ , True)
progress (Γ , False) = inj₂ (_ , False)
progress (Γ , App t t₃) = inj₁ (Step (Pure Dist-$))
progress (Γ , Abs t₁) = inj₂ (_ , Abs _)
progress (Γ , Var p) = inj₁ (Step (Pure Lookup))
progress (Γ , (If t Then t₄ Else t₅)) = inj₁ (Step (Pure Dist-If))
progress (Γ , Return t₁) = inj₁ (Step Return)
progress (Γ , m >>= k) =  inj₁ (Step Dist->>=)
progress (Γ , ξ) = inj₂ (_ , ξ)
progress (Γ , Throw t₁) = inj₁ (Step Throw)
progress (Γ , Catch t₁ t₂) = inj₁ (Step Dist-Catch)
progress {c = Γ , Mac t} (_ , Mac {{l}} _) = inj₂ (_ , Mac t)
progress (Γ , Macₓ t₁) = inj₂ (_ , Macₓ _)
progress (Γ , label p t₁) = inj₁ (Step (label p))
progress (Γ , unlabel x t₁) = inj₁ (Step Dist-unlabel)
progress (Γ , join p t₁) = inj₁ (Step (Dist-join p))
progress (Γ , Res t₁) = inj₂ (_ , Res _)
progress (Γ , Resₓ t₁) = inj₂ (_ , Resₓ _)
progress (Γ , ∙) = inj₁ (Step (Pure Dist-∙))
progress (f $ x) with progress f
progress (f $ x) | inj₁ (Step s) = inj₁ (Step (Pure (AppL (getFunPureStep f s))))
progress (Γ , App t₃ t₄ $ x₂) | inj₂ (Γ' , ())
progress (Γ , Abs t₁ $ x₂) | inj₂ (Γ' , Abs t) = inj₁ (Step (Pure Beta))
progress (Γ , Var p $ x₂) | inj₂ (Γ' , ())
progress (Γ , (If t₄ Then t₅ Else t₆) $ x₂) | inj₂ (Γ' , ())
progress (Γ , ∙ $ x₂) | inj₂ (Γ' , ()) 
progress (If c Then t Else e) with progress c
progress (If c Then t Else e) | inj₁ (Step x) = inj₁ (Step (Pure (IfCond (getBoolPureStep c x))))
progress (If Γ , True Then t₃ Else e₁) | inj₂ (Γ' , True) = inj₁ (Step (Pure IfTrue))
progress (If Γ , False Then t₃ Else e₁) | inj₂ (Γ' , False) = inj₁ (Step (Pure IfFalse))
progress (If Γ , App t₃ t₄ Then t₅ Else e₁) | inj₂ (Γ' , ())
progress (If Γ , Var p Then t₃ Else e₁) | inj₂ (Γ' , ())
progress (If Γ , (If t₄ Then t₅ Else t₆) Then t₇ Else e₁) | inj₂ (Γ' , ())
progress (If Γ , ∙ Then t₃ Else e₁) | inj₂ (Γ' , ())
progress (m >>= k) with progress m
progress (m₁ >>= k₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , （）)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , True)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , False)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , Abs t)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , ξ)
progress ((Γ , Mac t₁) >>= k₁) | inj₂ (Γ' , Mac t) = inj₁ (Step Bind)
progress ((Γ , Macₓ t₁) >>= k₁) | inj₂ (Γ' , Macₓ t) = inj₁ (Step BindEx)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , Res t)
progress ((Γ , ()) >>= k₁) | inj₂ (Γ' , Resₓ e)
progress (Catch m h) with progress m
progress (Catch m₁ h₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , （）)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , True)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , False)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , Abs t)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , ξ)
progress (Catch (Γ , Mac t₁) h₁) | inj₂ (Γ' , Mac t) = inj₁ (Step Catch)
progress (Catch (Γ , Macₓ t₁) h₁) | inj₂ (Γ' , Macₓ t) = inj₁ (Step CatchEx)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , Res t)
progress (Catch (Γ , ()) h₁) | inj₂ (Γ' , Resₓ e)
progress (unlabel x c) with progress c
progress (unlabel x₁ c) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x))
progress (unlabel x (Γ , ())) | inj₂ (Γ' , （）)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , True)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , False)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , Abs t)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , ξ)
progress (unlabel x (Γ , (Res t)))| inj₂ (Γ' , Res _) = inj₁ (Step unlabel)
progress (unlabel x (Γ , (Resₓ t))) | inj₂ (Γ' , Resₓ _) = inj₁ (Step unlabelEx)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , Mac _)
progress (unlabel x (Γ , ())) | inj₂ (Γ' , Macₓ _)
progress (join x c) with progress c
progress (join x₁ c) | inj₁ (Step x) = inj₁ (Step (joinCtx x₁ x))
progress (join x₁ (Γ , ())) | inj₂ (Γ' , （）)
progress (join x₁ (Γ , ())) | inj₂ (Γ' , True)
progress (join x₁ (Γ , ())) | inj₂ (Γ' , False)
progress (join x₁ (Γ , ())) | inj₂ (Γ' , Abs t)
progress (join x₁ (Γ , ())) | inj₂ (Γ' , ξ)
progress (join x₁ (Γ , Mac t₁)) | inj₂ (Γ' , Mac t) = inj₁ (Step (join x₁))
progress (join x₁ (Γ , Macₓ t₁)) | inj₂ (Γ' , Macₓ t) = inj₁ (Step (joinEx x₁))
progress (join x₁ (Γ , ())) | inj₂ (Γ' , Res t)
progress (join x₁ (Γ , ())) | inj₂ (Γ' , Resₓ e)
progress ∙ = inj₁ (Step (Pure Hole))

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ (c : CTerm) -> IsValue c -> NormalForm c
valueNotRedex .(Γ , （）) (Γ , （）) (Step (Pure ()))
valueNotRedex .(Γ , True) (Γ , True) (Step (Pure ()))
valueNotRedex .(Γ , False) (Γ , False) (Step (Pure ()))
valueNotRedex .(Γ , Abs t) (Γ , Abs t) (Step (Pure ()))
valueNotRedex .(Γ , ξ) (Γ , ξ) (Step (Pure ()))
valueNotRedex .(Γ , Mac t) (Γ , Mac t) (Step (Pure ()))
valueNotRedex .(Γ , Macₓ e) (Γ , Macₓ e) (Step (Pure ()))
valueNotRedex .(Γ , Res t) (Γ , Res t) (Step (Pure ()))
valueNotRedex .(Γ , Resₓ e) (Γ , Resₓ e) (Step (Pure ()))

determinism⇝ : ∀ {c₁ c₂ c₃} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃

determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (AppL ()) Beta
determinism⇝ Beta (AppL ())
determinism⇝ Beta Beta = refl
determinism⇝ Lookup Lookup = refl
determinism⇝ Dist-$ Dist-$ = refl
determinism⇝ Dist-If Dist-If = refl
determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (IfCond ()) IfTrue
determinism⇝ (IfCond ()) IfFalse
determinism⇝ IfTrue (IfCond ())
determinism⇝ IfTrue IfTrue = refl
determinism⇝ IfFalse (IfCond ())
determinism⇝ IfFalse IfFalse = refl
determinism⇝ Dist-∙ Dist-∙ = refl
determinism⇝ Hole Hole = refl

-- | The small step semantics is deterministic.
-- -- At most one rule apply per term.
determinism : ∀ {c₁ c₂ c₃} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinismMixed  : ∀ {c₁ c₂ c₃} -> c₁ ⇝ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃

determinism (Pure s₁) s₂ = determinismMixed s₁ s₂
determinism s₁ (Pure s₂) = sym (determinismMixed s₂ s₁)
determinism Return Return = refl
determinism Dist->>= Dist->>= = refl
determinism (BindCtx s₁) (BindCtx s₂) with determinism s₁ s₂
determinism (BindCtx s₁) (BindCtx s₂) | refl = refl
determinism (BindCtx (Pure ())) Bind
determinism (BindCtx (Pure ())) BindEx
determinism Bind (BindCtx (Pure ()))
determinism Bind Bind = refl
determinism BindEx (BindCtx (Pure ()))
determinism BindEx BindEx = refl
determinism Throw Throw = refl
determinism Dist-Catch Dist-Catch = refl
determinism (CatchCtx s₁) (CatchCtx s₂) rewrite determinism s₁ s₂ = refl
determinism (CatchCtx (Pure ())) Catch
determinism (CatchCtx (Pure ())) CatchEx
determinism Catch (CatchCtx (Pure ()))
determinism Catch Catch = refl
determinism CatchEx (CatchCtx (Pure ()))
determinism CatchEx CatchEx = refl
determinism (label p) (label .p) = refl
determinism Dist-unlabel Dist-unlabel = refl
determinism unlabel unlabel = refl
determinism unlabel (unlabelCtx (Pure ()))
determinism unlabelEx unlabelEx = refl
determinism unlabelEx (unlabelCtx (Pure ()))
determinism (unlabelCtx (Pure ())) unlabel
determinism (unlabelCtx (Pure ())) unlabelEx
determinism (unlabelCtx s₁) (unlabelCtx s₂) rewrite determinism s₁ s₂ = refl
determinism (Dist-join x) (Dist-join .x) = refl
determinism (joinCtx x s₁) (joinCtx .x s₂) rewrite determinism s₁ s₂ = refl
determinism (joinCtx x (Pure ())) (join .x)
determinism (joinCtx x (Pure ())) (joinEx .x)
determinism (join x) (joinCtx .x (Pure ()))
determinism (join x) (join .x) = refl
determinism (joinEx x) (joinCtx .x (Pure ()))
determinism (joinEx x) (joinEx .x) = refl

determinismMixed s₁ (Pure s₂) = determinism⇝ s₁ s₂
determinismMixed () Return
determinismMixed () Dist->>=
determinismMixed () (BindCtx s₂)
determinismMixed () Bind
determinismMixed () BindEx
determinismMixed () Throw
determinismMixed () Dist-Catch
determinismMixed () (CatchCtx s₂)
determinismMixed () Catch
determinismMixed () CatchEx
determinismMixed () (label p)
determinismMixed () Dist-unlabel
determinismMixed () unlabel
determinismMixed () unlabelEx
determinismMixed () (unlabelCtx s₂)
determinismMixed () (Dist-join p)
determinismMixed () (joinCtx p s₂)
determinismMixed () (join p)
determinismMixed () (joinEx p)

-- Typed id cterm
idᵗ : ∀ {Δ τ} {Γ : Env (length Δ)} {{Γᵗ : TEnv Δ Γ}} -> id {n = length Δ} :: (τ => τ)
idᵗ {{Γᵗ = Γᵗ}} = Γᵗ , Abs (Var Here)

lookup-fin : ∀ {τ Δ} {Γ : Env (length Δ)} (p : τ ∈ Δ) (Γᵗ : TEnv Δ Γ) -> lookup (fin p) Γ :: τ
lookup-fin Here (x ∷ Γ) = x
lookup-fin (There p) (x ∷ Γ) = lookup-fin p Γ


-- A well-typed closed term when reduced preserves its type.
preservation : ∀ {τ} {c₁ c₂ : CTerm} -> c₁ :: τ -> c₁ ⟼ c₂ -> c₂ :: τ

preservation⇝ : ∀ {τ} {c₁ c₂ : CTerm} -> c₁ :: τ -> c₁ ⇝ c₂ -> c₂ :: τ

preservation⇝ (f $ x) (AppL s) = preservation⇝ f s $ x
preservation⇝ (Γ , Abs t $ x) Beta = idᵗ $ x ∷ Γ , t
preservation⇝ (Γ , Var p) (Lookup {Γ = Γ'}) = idᵗ $ lookup-fin p Γ
preservation⇝ (Γ , App f x) Dist-$ = Γ , f $ Γ , x
preservation⇝ (Γ , (If c Then t Else e)) Dist-If = If Γ , c Then Γ , t Else (Γ , e)
preservation⇝ (If c Then t Else e) (IfCond s) = If preservation⇝ c s Then t Else e
preservation⇝ (If Γ , True Then t₂ Else t₃) IfTrue = idᵗ $ t₂
preservation⇝ (If Γ , False Then t₂ Else t₃) IfFalse = idᵗ $ t₃
preservation⇝ (Γ , ∙) Dist-∙ = ∙
preservation⇝ ∙ Hole = ∙

preservation p (Pure s) = preservation⇝ p s
preservation (Γ , Return t) Return = idᵗ $ Γ , (Mac t)
preservation (Γ , m >>= k) Dist->>= = (Γ , m) >>= (Γ , k)
preservation (m >>= k) (BindCtx s) = preservation m s >>= k
preservation ((Γ , Mac m) >>= k) Bind = k $ Γ , m
preservation ((Γ , Macₓ e) >>= k) BindEx = idᵗ $  Γ , (Throw e)
preservation (Γ , Throw t) Throw = idᵗ $ Γ , (Macₓ t)
preservation (Γ , Catch m h) Dist-Catch = Catch (Γ , m) (Γ , h)
preservation (Catch m h) (CatchCtx s) = Catch (preservation m s) h
preservation (Catch (Γ , Mac t) h) Catch = idᵗ $  Γ , (Return t)
preservation (Catch (Γ , Macₓ t) h) CatchEx = h $ (Γ , t)
preservation (Γ , label p t) (label .p) = idᵗ $  Γ , (Return (Res t))
preservation (Γ , unlabel x t) Dist-unlabel = unlabel x (Γ , t)
preservation (unlabel x t) (unlabelCtx s) = unlabel x (preservation t s)
preservation (unlabel x (Γ , Res t)) unlabel = idᵗ $ Γ , (Return t)
preservation (unlabel x (Γ , Resₓ e)) unlabelEx = idᵗ $ (Γ , (Throw e)) 
preservation (join x t) (joinCtx .x s) = join x (preservation t s)
preservation (join x (Γ , Mac t)) (join .x) = idᵗ $ Γ , (Return (Res t))
preservation (join x (Γ , Macₓ e)) (joinEx .x) = idᵗ $ Γ , (Return (Resₓ e))
preservation (Γ , join x t) (Dist-join .x) = join x (Γ , t)
