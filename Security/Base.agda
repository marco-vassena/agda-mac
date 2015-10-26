-- Defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Relation.Binary.PropositionalEquality

ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ
ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)
ε-Mac lₐ p (Var x) = Var x
ε-Mac lₐ p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Mac lₐ p (If c Then t Else e) = If (ε lₐ c) Then (ε-Mac lₐ p t) Else ε-Mac lₐ p e
ε-Mac lₐ p (Return t) = Return (ε lₐ t)
ε-Mac lₐ p (m >>= k) = (ε-Mac lₐ p m) >>= ε lₐ k
ε-Mac lₐ p (Throw t) = Throw (ε lₐ t)
ε-Mac lₐ p (Catch m k) = Catch (ε-Mac lₐ p m) (ε lₐ k)
ε-Mac lₐ p (Mac t) = Mac (ε lₐ t)
ε-Mac lₐ p (Macₓ t) = Macₓ (ε lₐ t)
ε-Mac lₐ p (label x t) = label x (ε lₐ t) -- Should I compare with the second label here  ?s
ε-Mac lₐ p (unlabel x t) = unlabel x (ε lₐ t)
ε-Mac lₐ p ∙ = ∙

ε {Mac lᵈ τ} lₐ t with lᵈ ⊑? lₐ
ε {Mac lᵈ τ} lₐ t | yes p = ε-Mac lₐ p t
ε {Mac lᵈ τ} lₐ t | no ¬p = ∙
ε {Labeled lᵈ τ} lₐ t = {!!}
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If t Then t₁ Else t₂) = If (ε lₐ t) Then (ε lₐ t₁) Else (ε lₐ t₂)
ε lₐ ξ = ξ
ε lₐ ∙ = ∙

-- Erasure function.
-- ε l t transform a term t in ∙ if it is above the security level l.
εᶜ : ∀ {τ} -> Label -> CTerm τ -> CTerm τ
εᶜ-env : ∀ {Δ} -> Label -> Env Δ -> Env Δ
-- εᶜ-Labeled : ∀ {τ l₁} -> (l₂ : Label) -> l₁ ⊑ l₂ -> CTerm (Labeled l₁ τ) -> CTerm (Labeled l₁ τ)
εᶜ-Mac : ∀ {τ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)
εᶜ-Mac lₐ p (Γ , t) = (εᶜ-env lₐ Γ) , (ε-Mac lₐ p t)
εᶜ-Mac lₐ p (f $ x) = (εᶜ lₐ f) $ (εᶜ lₐ x)
εᶜ-Mac lₐ p (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Mac lₐ p t) Else εᶜ-Mac lₐ p e
εᶜ-Mac lₐ p (m >>= k) = (εᶜ-Mac lₐ p m) >>= (εᶜ lₐ k)
εᶜ-Mac lₐ p (Catch m h) = Catch (εᶜ-Mac lₐ p m) (εᶜ lₐ h)
εᶜ-Mac lₐ p (unlabel x c) = unlabel x (εᶜ lₐ c) 
εᶜ-Mac lₐ p ∙ = ∙

εᶜ-Mac-∙ : ∀ {lᵈ τ} -> (lₐ : Label) -> ¬ (lᵈ ⊑ lₐ) -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)
εᶜ-Mac-∙ lₐ ¬p (Γ , t) = εᶜ-env lₐ Γ , ∙
εᶜ-Mac-∙ lₐ ¬p c = ∙

εᶜ {Mac lᵈ τ} lₐ c with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ τ} lₐ c | yes p = εᶜ-Mac lₐ p c
εᶜ {Mac lᵈ τ} lₐ c | no ¬p = εᶜ-Mac-∙ lₐ ¬p c
εᶜ {Labeled x τ} lₐ c = {!!}
εᶜ lₐ (Γ , t) = (εᶜ-env lₐ Γ) , (ε lₐ t)
εᶜ lₐ (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ lₐ (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ lₐ t) Else (εᶜ lₐ e)
εᶜ lₐ ∙ = ∙

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

open import Typed.Semantics

εᶜ-lookup : ∀ {Δ τ} {{lₐ}} -> (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ lₐ (p !! Γ) ≡ p !! εᶜ-env lₐ Γ
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

εᶜ-distributes : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⟼ c₂ -> εᶜ lₐ c₁ ⟼ εᶜ lₐ c₂
εᶜ-Mac-∙-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) -> (p : ¬ (lᵈ ⊑ lₐ)) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac-∙ lₐ p c₁) ⟼ (εᶜ-Mac-∙ lₐ p c₂)
εᶜ-Mac-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac lₐ p c₁) ⟼ (εᶜ-Mac lₐ p c₂)


εᶜ-Mac-∙-distributes lₐ ¬p (AppL s) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Beta = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Lookup = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p Dist-$ = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p Dist-If = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p (IfCond s) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p IfTrue = Hole
εᶜ-Mac-∙-distributes lₐ ¬p IfFalse = Hole 
εᶜ-Mac-∙-distributes lₐ ¬p Return = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p Dist->>= = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p (BindCtx s) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Bind = Hole
εᶜ-Mac-∙-distributes lₐ ¬p BindEx = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Throw = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p Dist-Catch = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p (CatchCtx s) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Catch = Hole
εᶜ-Mac-∙-distributes lₐ ¬p CatchEx = Hole
εᶜ-Mac-∙-distributes lₐ ¬p (label p) = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p (Dist-unlabel p) = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p (unlabel p) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p (unlabelCtx p s) = Hole
εᶜ-Mac-∙-distributes lₐ ¬p Dist-∙ = Dist-∙
εᶜ-Mac-∙-distributes lₐ ¬p Hole = Hole

εᶜ-Mac-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : lᵈ ⊑ lₐ) (Γ : Env Δ) (x : Mac lᵈ τ ∈ Δ) -> εᶜ-Mac lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Mac-lookup {lᵈ} {lₐ = lₐ} p (x ∷ Γ) Here with lᵈ ⊑? lₐ
εᶜ-Mac-lookup p (x ∷ Γ) Here | yes q rewrite extensional-⊑ p q = refl 
εᶜ-Mac-lookup p (x ∷ Γ) Here | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Mac-lookup p Γ x = refl

-- Yeah!
εᶜ-Closure : ∀ {τ Δ} {{Γ : Env Δ}} {t : Term Δ τ} (lₐ : Label) -> εᶜ lₐ (Γ , t) ≡ (εᶜ-env lₐ Γ , ε lₐ t)
εᶜ-Closure {Bool} lₐ = refl
εᶜ-Closure {τ => τ₁} lₐ = refl
εᶜ-Closure {Mac lᵈ τ} lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Mac lᵈ τ} lₐ | yes p = refl
εᶜ-Closure {Mac lᵈ τ} lₐ | no ¬p = refl
εᶜ-Closure {Labeled x τ} lₐ = {!!}
εᶜ-Closure {Exception} lₐ = refl

εᶜ-Mac-distributes lₐ p (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-Mac-distributes {lᵈ} lₐ p Beta with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ Beta | yes p = Beta
εᶜ-Mac-distributes lₐ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes {lᵈ} {c₁ = Γ , Var x} lₐ p Lookup with lᵈ ⊑? lₐ
εᶜ-Mac-distributes {lᵈ} {τ} {Γ , Var x} lₐ p₁ Lookup | yes p rewrite εᶜ-Mac-lookup p Γ x = Lookup
εᶜ-Mac-distributes {lᵈ} {τ} {Γ , Var x} lₐ p Lookup | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes lₐ p (Dist-$ {α = Bool}) = Dist-$
εᶜ-Mac-distributes lₐ p (Dist-$ {α = α => α₁}) = Dist-$
εᶜ-Mac-distributes {c₁ = Γ , App f x} lₐ p  Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$ 
εᶜ-Mac-distributes lₐ p Dist-If = Dist-If
εᶜ-Mac-distributes lₐ p (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-Mac-distributes {lᵈ} lₐ p IfTrue with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ IfTrue | yes p = IfTrue
εᶜ-Mac-distributes lₐ p IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes {lᵈ} lₐ p IfFalse with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ IfFalse | yes p = IfFalse
εᶜ-Mac-distributes lₐ p IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes {lᵈ} lₐ p Return with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ Return | yes p = Return
εᶜ-Mac-distributes lₐ p Return | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes lₐ p Dist->>= = Dist->>=
εᶜ-Mac-distributes lₐ p (BindCtx s) = BindCtx (εᶜ-Mac-distributes lₐ p s)
εᶜ-Mac-distributes {lᵈ} {τ} {c₁ = (Γ , Mac t) >>= k} lₐ p Bind rewrite εᶜ-Closure {t = t} lₐ = Bind
εᶜ-Mac-distributes {lᵈ} lₐ p BindEx with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ BindEx | yes p = BindEx
εᶜ-Mac-distributes lₐ p BindEx | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes {lᵈ} lₐ p Throw with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ Throw | yes p = Throw
εᶜ-Mac-distributes lₐ p Throw | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes lₐ p Dist-Catch = Dist-Catch
εᶜ-Mac-distributes lₐ p (CatchCtx s) = CatchCtx (εᶜ-Mac-distributes lₐ p s)
εᶜ-Mac-distributes {lᵈ} lₐ p Catch with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ p₁ Catch | yes p = Catch
εᶜ-Mac-distributes lₐ p Catch | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes lₐ p CatchEx = CatchEx
εᶜ-Mac-distributes lₐ p (label p₁) = {!!}
εᶜ-Mac-distributes lₐ p (Dist-unlabel p₁) = {!!}
εᶜ-Mac-distributes lₐ p (unlabel p₁) = {!!}
εᶜ-Mac-distributes lₐ p (unlabelCtx p₁ s) = {!!}
εᶜ-Mac-distributes lₐ p Dist-∙ = Dist-∙
εᶜ-Mac-distributes lₐ p Hole = Hole



εᶜ-distributes {Mac lᵈ τ} lₐ s with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ τ} lₐ s | yes p = εᶜ-Mac-distributes lₐ p s
εᶜ-distributes {Mac lᵈ τ} lₐ s | no ¬p = εᶜ-Mac-∙-distributes lₐ ¬p s
εᶜ-distributes {Bool} lₐ (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-distributes {Bool} lₐ Beta = Beta
εᶜ-distributes {Bool} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-distributes {Bool} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$
εᶜ-distributes {Bool} lₐ Dist-If = Dist-If
εᶜ-distributes {Bool} lₐ (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-distributes {Bool} lₐ IfTrue = IfTrue
εᶜ-distributes {Bool} lₐ IfFalse = IfFalse
εᶜ-distributes {Bool} lₐ Dist-∙ = Dist-∙
εᶜ-distributes {Bool} lₐ Hole = Hole
εᶜ-distributes {τ => τ₁} lₐ (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-distributes {τ => τ₁} lₐ Beta = Beta
εᶜ-distributes {τ => τ₁} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-distributes {τ => τ₁} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$
εᶜ-distributes {τ => τ₁} lₐ Dist-If = Dist-If
εᶜ-distributes {τ => τ₁} lₐ (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-distributes {τ => τ₁} lₐ IfTrue = IfTrue
εᶜ-distributes {τ => τ₁} lₐ IfFalse = IfFalse
εᶜ-distributes {τ => τ₁} lₐ Dist-∙ = Dist-∙
εᶜ-distributes {τ => τ₁} lₐ Hole = Hole
εᶜ-distributes {Labeled x τ} lₐ s = {!!}
εᶜ-distributes {Exception} lₐ (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-distributes {Exception} lₐ Beta = Beta
εᶜ-distributes {Exception} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-distributes {Exception} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$
εᶜ-distributes {Exception} lₐ Dist-If = Dist-If
εᶜ-distributes {Exception} lₐ (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-distributes {Exception} lₐ IfTrue = IfTrue
εᶜ-distributes {Exception} lₐ IfFalse = IfFalse
εᶜ-distributes {Exception} lₐ Dist-∙ = Dist-∙
εᶜ-distributes {Exception} lₐ Hole = Hole

--------------------------------------------------------------------------------

-- Graph of the function ε
-- Erasure l t tₑ corresponds to ε l t ≡ t'
-- data Erasure (l : Label) {n : ℕ} : Term n -> Term n -> Set where
--   True : Erasure l True True
--   False : Erasure l False False
--   Var : (x : Fin n) -> Erasure l (Var x) (Var x)
--   Abs : {t tₑ : Term (suc n)} -> Erasure l t tₑ -> Erasure l (Abs t) (Abs tₑ)
--   App : {f fₑ x xₑ : Term n} -> Erasure l f fₑ -> Erasure l x xₑ -> Erasure l (App f x) (App fₑ xₑ)
--   If_Then_Else_ : {c cₑ t tₑ e eₑ : Term n} -> 
--                   Erasure l c cₑ -> Erasure l t tₑ -> Erasure l e eₑ ->
--                   Erasure l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)
--   Return : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Return t) (Return tₑ)
--   _>>=_ : ∀ {m mₑ k kₑ : Term n} -> Erasure l m mₑ -> Erasure l k kₑ ->
--             Erasure l (m >>= k) (mₑ >>= kₑ)
--   ξ : Erasure l ξ ξ
--   Throw : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Throw t) (Throw tₑ)
--   Catch : {m mₑ h hₑ : Term n} -> Erasure l m mₑ -> Erasure l h hₑ -> Erasure l (Catch m h) (Catch mₑ hₑ) 
--   Mac : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Mac t) (Mac tₑ)
--   Macₓ : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Macₓ t) (Macₓ tₑ)
--   Res : {t tₑ : Term n} -> (l' : Label) -> l ⊑ l' -> 
--         Erasure l t tₑ -> Erasure l (Res l' t) (Res l' tₑ)
--   Res∙ : ∀ {t : Term n} -> (l' : Label) -> ¬ (l ⊑ l') -> Erasure l (Res l' t) (Res l' ∙)
--   label : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t tₑ : Term n} -> l ⊑ l₂ -> 
--             Erasure l t tₑ -> Erasure l (label x t) (label x tₑ)
--   label∙ : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t : Term n} -> ¬ (l ⊑ l₂) -> Erasure l (label x t) (label x ∙) 
--   unlabel : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (unlabel t) (unlabel tₑ)
--   ∙ : Erasure l ∙ ∙

-- -- Sound
-- -- For any term t I can construct Erasure l t (ε l t), 
-- -- i.e. Erasure approximates correctly the erasure function. 
-- ε-Erasure : ∀ {l n} -> (t : Term n) -> Erasure l t (ε l t)
-- ε-Erasure True = True
-- ε-Erasure False = False
-- ε-Erasure (Var x) = Var x
-- ε-Erasure (Abs t) = Abs (ε-Erasure t)
-- ε-Erasure (App f x) = App (ε-Erasure f) (ε-Erasure x)
-- ε-Erasure (If c Then t Else e) = If ε-Erasure c Then ε-Erasure t Else ε-Erasure e
-- ε-Erasure (Return t) = Return (ε-Erasure t)
-- ε-Erasure (m >>= k) = ε-Erasure m >>= ε-Erasure k
-- ε-Erasure ξ = ξ
-- ε-Erasure (Throw e) = Throw (ε-Erasure e)
-- ε-Erasure (Catch m h) = Catch (ε-Erasure m) (ε-Erasure h)
-- ε-Erasure (Mac t) = Mac (ε-Erasure t)
-- ε-Erasure (Macₓ t) = Macₓ (ε-Erasure t)
-- ε-Erasure {l₁} (Res l₂ t) with l₁ ⊑? l₂
-- ε-Erasure (Res l₂ t) | yes p = Res l₂ p (ε-Erasure t)
-- ε-Erasure (Res l₂ t) | no ¬p = Res∙ l₂ ¬p
-- ε-Erasure {l₁} (label {h = l₂} x t) with l₁ ⊑? l₂
-- ε-Erasure (label x t) | yes p = label p (ε-Erasure t)
-- ε-Erasure (label x t) | no ¬p = label∙ ¬p
-- ε-Erasure (unlabel t) = unlabel (ε-Erasure t)
-- ε-Erasure ∙ = ∙

-- -- Complete
-- -- For any term t and tₑ such that Erasure l t tₑ, the ε l t ≡ tₑ
-- -- i.e. Erasure represents only the erasure function.
-- Erasure-ε : ∀ {l n} {t tₑ : Term n} -> Erasure l t tₑ -> ε l t ≡ tₑ
-- Erasure-ε True = refl
-- Erasure-ε False = refl
-- Erasure-ε (Var x) = refl
-- Erasure-ε (Abs t) rewrite Erasure-ε t = refl
-- Erasure-ε (App f x) rewrite Erasure-ε f | Erasure-ε x = refl
-- Erasure-ε (If c Then t Else e) rewrite
--   Erasure-ε c | Erasure-ε t | Erasure-ε e = refl
-- Erasure-ε (Return t) rewrite Erasure-ε t = refl
-- Erasure-ε (m >>= k) rewrite Erasure-ε m | Erasure-ε k = refl
-- Erasure-ε ξ = refl
-- Erasure-ε (Throw e) rewrite Erasure-ε e = refl
-- Erasure-ε (Catch m h) rewrite Erasure-ε m | Erasure-ε h = refl
-- Erasure-ε (Mac t) rewrite Erasure-ε t = refl
-- Erasure-ε (Macₓ t) rewrite Erasure-ε t = refl
-- Erasure-ε {l₁} (Res l₂ l₁⊑l₂ t) with l₁ ⊑? l₂
-- Erasure-ε (Res l₂ l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
-- Erasure-ε (Res l₂ l₁⊑l₂ t) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε {l₁} (Res∙ l₂ l₁⋢l₂) with l₁ ⊑? l₂
-- Erasure-ε (Res∙ l₂ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε (Res∙ l₂ l₁⋢l₂) | no _ = refl
-- Erasure-ε {l₁} (label {l₂ = l₂} l₁⊑l₂ t) with l₁ ⊑? l₂
-- Erasure-ε (label l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
-- Erasure-ε (label l₁⊑l₂ t₁) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε {l₁} (label∙ {l₂ = l₂} l₁⋢l₂) with l₁ ⊑? l₂
-- Erasure-ε (label∙ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε (label∙ l₁⋢l₂) | no _ = refl
-- Erasure-ε (unlabel t) rewrite Erasure-ε t = refl
-- Erasure-ε ∙ = refl

-- -- Corresponds to ε l t ≡ ε l (ε l t).
-- -- I am using the graph of ε because of unification issues. 
-- Erasure-idem : ∀ {n} {{l}} {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l tₑ tₑ 
-- Erasure-idem True = True
-- Erasure-idem False = False
-- Erasure-idem (Var x) = Var x
-- Erasure-idem (Abs t) = Abs (Erasure-idem t)
-- Erasure-idem (App f x) = App (Erasure-idem f) (Erasure-idem x)
-- Erasure-idem (If c Then t Else e) = If (Erasure-idem c) Then (Erasure-idem t) Else (Erasure-idem e)
-- Erasure-idem (Return t) = Return (Erasure-idem t)
-- Erasure-idem (m >>= k) = (Erasure-idem m) >>= (Erasure-idem k)
-- Erasure-idem ξ = ξ
-- Erasure-idem (Throw e) = Throw (Erasure-idem e)
-- Erasure-idem (Catch m h) = Catch (Erasure-idem m) (Erasure-idem h)
-- Erasure-idem (Mac t) = Mac (Erasure-idem t)
-- Erasure-idem (Macₓ t) = Macₓ (Erasure-idem t)
-- Erasure-idem (Res l x t) = Res l x (Erasure-idem t)
-- Erasure-idem (Res∙ l x) = Res∙ l x
-- Erasure-idem (label x t) = label x (Erasure-idem t)
-- Erasure-idem (label∙ x) = label∙ x
-- Erasure-idem (unlabel t) = unlabel (Erasure-idem t)
-- Erasure-idem ∙ = ∙

-- -- Now we need a similar construction for εᶜ and εᶜ-env

-- mutual
--   data Erasureᶜ (l : Label) : CTerm -> CTerm -> Set where
--     _,_ : ∀ {n} {t tₑ : Term n} {Γ Γₑ : Env n} -> 
--             ErasureEnvᶜ l Γ Γₑ -> Erasure l t tₑ -> Erasureᶜ l (Γ , t) (Γₑ , tₑ)
--     _$_ : ∀ {f fₑ x xₑ} -> Erasureᶜ l f fₑ -> Erasureᶜ l x xₑ -> Erasureᶜ l (f $ x) (fₑ $ xₑ)
    
--     If_Then_Else_ : ∀ {c cₑ t tₑ e eₑ} -> Erasureᶜ l c cₑ -> Erasureᶜ l t tₑ -> Erasureᶜ l e eₑ ->
--                     Erasureᶜ l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)

--     _>>=_ : ∀ {m mₑ k kₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l k kₑ -> Erasureᶜ l (m >>= k) (mₑ >>= kₑ)

--     Catch : ∀ {m mₑ h hₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l h hₑ -> Erasureᶜ l (Catch m h) (Catch mₑ hₑ)

--     unlabel : ∀ {t tₑ} -> Erasureᶜ l t tₑ -> Erasureᶜ l (unlabel t) (unlabel tₑ)


--   data ErasureEnvᶜ (l : Label) : ∀ {n} -> Env n -> Env n -> Set where
--     [] : ErasureEnvᶜ l [] []
--     _∷_ : ∀ {n c cₑ} {Γ Γₑ : Env n} -> Erasureᶜ l c cₑ -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l (c ∷ Γ) (cₑ ∷ Γₑ)

-- -- Sound
-- εᶜ-Erasureᶜ : ∀ {{l}} -> (c : CTerm) -> Erasureᶜ l c (εᶜ l c)
-- εᶜ-env-ErasureEnvᶜ : ∀ {l n} -> (Γ : Env n) -> ErasureEnvᶜ l Γ (εᶜ-env l Γ)

-- εᶜ-Erasureᶜ (Γ , x) = (εᶜ-env-ErasureEnvᶜ Γ) , (ε-Erasure x)
-- εᶜ-Erasureᶜ (f $ x) = εᶜ-Erasureᶜ f $ εᶜ-Erasureᶜ x
-- εᶜ-Erasureᶜ (If c Then c₁ Else c₂) = If εᶜ-Erasureᶜ c Then εᶜ-Erasureᶜ c₁ Else εᶜ-Erasureᶜ c₂
-- εᶜ-Erasureᶜ (c >>= c₁) = εᶜ-Erasureᶜ c >>= εᶜ-Erasureᶜ c₁
-- εᶜ-Erasureᶜ (Catch c c₁) = Catch (εᶜ-Erasureᶜ c) (εᶜ-Erasureᶜ c₁)
-- εᶜ-Erasureᶜ (unlabel c) = unlabel (εᶜ-Erasureᶜ c)

-- εᶜ-env-ErasureEnvᶜ [] = []
-- εᶜ-env-ErasureEnvᶜ (x ∷ Γ) = (εᶜ-Erasureᶜ x) ∷ εᶜ-env-ErasureEnvᶜ Γ

-- -- Complete
-- Erasureᶜ-εᶜ : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> εᶜ l c ≡ cₑ
-- ErasureEnvᶜ-εᶜ-env : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> εᶜ-env l Γ ≡ Γₑ

-- Erasureᶜ-εᶜ (Γ , e) rewrite
--   ErasureEnvᶜ-εᶜ-env Γ | Erasure-ε e = refl
-- Erasureᶜ-εᶜ (f $ x) rewrite
--   Erasureᶜ-εᶜ f | Erasureᶜ-εᶜ x = refl
-- Erasureᶜ-εᶜ (If c Then t Else e) rewrite
--   Erasureᶜ-εᶜ c | Erasureᶜ-εᶜ t | Erasureᶜ-εᶜ e = refl
-- Erasureᶜ-εᶜ (m >>= k) rewrite
--   Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ k = refl
-- Erasureᶜ-εᶜ (Catch m h) rewrite
--   Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ h = refl
-- Erasureᶜ-εᶜ (unlabel e) rewrite
--   Erasureᶜ-εᶜ e = refl

-- ErasureEnvᶜ-εᶜ-env [] = refl
-- ErasureEnvᶜ-εᶜ-env (e ∷ Γ) rewrite
--   Erasureᶜ-εᶜ e | ErasureEnvᶜ-εᶜ-env Γ = refl

-- Erasureᶜ-idem : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> Erasureᶜ l cₑ cₑ 
-- ErasureEnvᶜ-idem : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l Γₑ Γₑ 

-- Erasureᶜ-idem (Γ , c) = (ErasureEnvᶜ-idem Γ) , (Erasure-idem c)
-- Erasureᶜ-idem (f $ x) = Erasureᶜ-idem f $ Erasureᶜ-idem x
-- Erasureᶜ-idem (If c Then t Else e) = If Erasureᶜ-idem c Then Erasureᶜ-idem t Else Erasureᶜ-idem e
-- Erasureᶜ-idem (c >>= c₁) = Erasureᶜ-idem c >>= Erasureᶜ-idem c₁
-- Erasureᶜ-idem (Catch c c₁) = Catch (Erasureᶜ-idem c) (Erasureᶜ-idem c₁)
-- Erasureᶜ-idem (unlabel c) = unlabel (Erasureᶜ-idem c)

-- ErasureEnvᶜ-idem [] = []
-- ErasureEnvᶜ-idem (x ∷ Γ) = (Erasureᶜ-idem x) ∷ (ErasureEnvᶜ-idem Γ)

-- --------------------------------------------------------------------------------
-- -- Going through the graph of the erasure function we can prove the original
-- -- idempotence lemma.

-- -- ε is idempotent
-- ε-idem : ∀ {l n} -> (t : Term n) -> ε l t ≡ ε l (ε l t)
-- ε-idem t with Erasure-idem (ε-Erasure t)
-- ... | r = sym (Erasure-ε r)

-- -- εᶜ is idempotent
-- εᶜ-idem : ∀ {l} -> (c : CTerm) -> εᶜ l c ≡ εᶜ l (εᶜ l c)
-- εᶜ-idem c with Erasureᶜ-idem (εᶜ-Erasureᶜ c) 
-- ... | r = sym (Erasureᶜ-εᶜ r)

-- -- εᶜ-env is idempotent
-- εᶜ-env-idem : ∀ {l n} -> (Γ : Env n) -> εᶜ-env l Γ ≡ εᶜ-env l (εᶜ-env l Γ)
-- εᶜ-env-idem Γ with ErasureEnvᶜ-idem (εᶜ-env-ErasureEnvᶜ Γ)
-- ... | r = sym (ErasureEnvᶜ-εᶜ-env r)

-- --------------------------------------------------------------------------------
