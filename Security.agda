module Security where

open import Semantics

-- An ETerm Δ τ denotes the result of the erasure function.
-- It is a term that may be erased, i.e. transformed to ∙, depending
-- on the attacker's label level.
-- Note that the erased term is nevertheless well-typed.
-- data ETerm (Δ : Context) (τ : Ty) : Set where
--   ⌜_⌝ : ∀ {t} -> Δ ⊢ t ∷ τ -> ETerm Δ τ

-- Erasure function.
-- ε l t transform a term t in ∙ if it is above the security level l.
ε : ∀ {n} -> Label -> Term n -> Term n
ε l True = True
ε l False = False
ε l (Var x) = Var x
ε l (Abs t) = Abs (ε l t)
ε l (App f x) = App (ε l f) (ε l x)
ε l (If c Then t Else e) = If (ε l c) Then (ε l t) Else (ε l e)
ε l (Return t) = Return (ε l t)
ε l (m >>= k) = (ε l m) >>= (ε l k)
ε l ξ = ξ
ε l (Throw t) = Throw (ε l t)
ε l (Catch m h) = Catch (ε l m) (ε l h)
ε l (Mac t) = Mac (ε l t)
ε l (Macₓ t) = Macₓ (ε l t)
ε l₁ (Res l₂ t) with l₁ ⊑? l₂
ε l₁ (Res l₂ t) | yes l₁⊑l₂ = Res l₂ (ε l₁ t)
ε l₁ (Res l₂ t) | no l₁⋢l₂ = Res l₂ ∙
ε l₁ (label {l = l₂} x t) with l₁ ⊑? l₂
ε l₁ (label x t) | yes l₁⊑l₂ = label x (ε l₁ t)
ε l₁ (label x t) | no l₁⋢l₂ = label x ∙
ε l (unlabel t) = unlabel (ε l t)
ε l ∙ = ∙

εᶜ-env : ∀ {n} -> Label -> Env n -> Env n
εᶜ : Label -> CTerm -> CTerm

εᶜ l (Γ , t) = (εᶜ-env l Γ) , ε l t
εᶜ l (f $ x) = (εᶜ l f) $ (εᶜ l x)
εᶜ l (If c Then t Else e) = If (εᶜ l c) Then (εᶜ l t) Else (εᶜ l e)
εᶜ l (m >>= k) = (εᶜ l m) >>= (εᶜ l k)
εᶜ l (Catch m h) = Catch (εᶜ l m) (εᶜ l h)
εᶜ l (unlabel c) = unlabel (εᶜ l c)

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ
