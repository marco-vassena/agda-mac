module Security where

open import Semantics

-- An ETerm Δ τ denotes the result of the erasure function.
-- It is a term that may be erased, i.e. transformed to ∙, depending
-- on the attacker's label level.
-- Note that the erased term is nevertheless well-typed.
data ETerm (Δ : Context) (τ : Ty) : Set where
  ⌜_⌝ : ∀ {t} -> Δ ⊢ t ∷ τ -> ETerm Δ τ

-- Erasure function.
-- ε l t transform a term t in ∙ if it is above the security level l.

ε : ∀ {Δ τ t} -> Label -> Δ ⊢ t ∷ τ -> ETerm Δ τ
ε l True = ⌜ True ⌝
ε l False = ⌜ False ⌝
ε l (App f x) with ε l f | ε l x
ε l (App f x) | ⌜ g ⌝ | ⌜ y ⌝ = ⌜ App g y ⌝
ε l (Abs t) with ε l t
ε l (Abs t) | ⌜ t' ⌝ = ⌜ Abs t' ⌝
ε l (Var x) = ⌜ Var x ⌝  -- The context will be erased in this case
ε l (If c Then t Else e) with ε l c | ε l t | ε l e
ε l (If c Then t Else e) | ⌜ c' ⌝ | ⌜ t' ⌝ | ⌜ e' ⌝ = ⌜ If c' Then t' Else e' ⌝
ε l (Return x) with ε l x
ε l (Return x) | ⌜ x' ⌝ = ⌜ Return x' ⌝
ε l (m >>= k) with ε l m | ε l k
ε l (m >>= k) | ⌜ m' ⌝ | ⌜ k' ⌝ = ⌜ (m' >>= k') ⌝
ε l ξ = ⌜ ξ ⌝
ε l (Throw e) with ε l e
ε l (Throw e) | ⌜ e' ⌝ = ⌜ Throw e' ⌝
ε l (Catch m h) with ε l m | ε l h
ε l (Catch m h₁) | ⌜ m' ⌝ | ⌜ h' ⌝ = ⌜ (Catch m' h') ⌝
ε l (Mac t) with ε l t
ε l (Mac t) | ⌜ t' ⌝ = ⌜ (Mac t') ⌝ -- Check! I don't believe we should not hide anything directly because Mac is private
ε l (Macₓ t) with ε l t
ε l (Macₓ t) | ⌜ t' ⌝ = ⌜ Macₓ t' ⌝  -- Idem
-- CHECK!
ε l (label {l = l₁} {h = l₂} x t) with l ⊑? l₂
ε l (label x t) | yes p = ⌜ label x ∙ ⌝
ε l (label x t) | no ¬p with ε l t
ε l (label x t) | no ¬p | ⌜ t' ⌝ = ⌜ label x t' ⌝  -- l₂ ⊑ l

-- CHECK! In SequentialLIO ε is applied homomorphically, but it does not feel right to me!
-- To erase, we only focus on the parts of the program which are sensitive, the rest is applied
-- homomorphically. How do we know where the sensitive data is? Well, it is the labeled values
-- (sensitive data already created) or sensitive data being created (primitive label).
ε l (unlabel {l = l₁} {h = l₂} x t) with l₁ ⊑? l
ε l (unlabel x t) | yes p with ε l t
ε l (unlabel x t) | yes p | ⌜ t' ⌝ = ⌜ (unlabel x t') ⌝ -- l₁ ⊑ l
ε l (unlabel x t) | no ¬p = ⌜ (unlabel x ∙) ⌝
ε l (Res {{l = l₁}} t) with l₁ ⊑? l
ε l (Res t) | yes p with ε l t
ε l (Res t) | yes p | ⌜ t' ⌝ = ⌜ (Res t') ⌝
ε l (Res t) | no ¬p = ⌜ (Res ∙) ⌝
ε l ∙ = ⌜ ∙ ⌝

-- Erasure function for closed terms.
-- It erases simple terms and the corresponding environment.
εᶜ : ∀ {τ} -> Label -> CTerm τ -> CTerm τ

-- ε-env l Γ ≡ map ε Γ
εᶜ-env : ∀ {Δ} -> Label -> Env Δ -> Env Δ

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

εᶜ l (Γ , True) = {!!}
εᶜ l (Γ , False) = {!!}
εᶜ l (Γ , App f x) = {!!}
εᶜ l (Γ , Abs t₁) = {!!}
εᶜ l (Γ , Var x) = {!!}
εᶜ l (Γ , (If t Then t₄ Else t₅)) = {!!}
εᶜ l (Γ , Return t₁) = {!!}
εᶜ l (Γ , t₁ >>= t₂) = {!!}
εᶜ l (Γ , ξ) = {!!}
εᶜ l (Γ , Throw t₁) = {!!}
εᶜ l (Γ , Catch t₁ t₂) = {!!}
εᶜ l (Γ , Mac t₁) = {!!}
εᶜ l (Γ , Macₓ t₁) = {!!}
εᶜ l (Γ , label x t₁) = {!!}
εᶜ l (Γ , unlabel x t₁) = {!!}
εᶜ l (Γ , Res t₁) = {!!}
εᶜ l (Γ , ∙) = {!!}
εᶜ l (f $ x) = (εᶜ l f) $ εᶜ l x
εᶜ l (If c Then t Else e) = If (εᶜ l c) Then (εᶜ l t) Else (εᶜ l e)
εᶜ l (m >>= k) = (εᶜ l m) >>= (εᶜ l k)
εᶜ l (Catch m h) = Catch (εᶜ l m) (εᶜ l h)
εᶜ l (unlabel x c) = unlabel x (εᶜ l c)
