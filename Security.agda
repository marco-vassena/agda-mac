module Security where

open import Semantics
open import Relation.Binary.PropositionalEquality

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

-- Erasure function for enviroments and closed terms,
-- defined mutually recursively.
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

ε-idem : ∀ {n} {{l}} -> (t : Term n) -> ε l t ≡ ε l (ε l t)
ε-idem True = refl
ε-idem False = refl
ε-idem (Var x) = refl
-- Marco: Agda does not solve to complex unification problems like this,
-- trying to pattern match on the equality proof r leads to the following error 
-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   ε l t ≟ ε l (ε l t)
-- when checking that the expression ? has type
-- Abs (ε .l t) ≡ Abs (ε .l (ε .l t))
ε-idem (Abs t) with ε-idem t
... | r = {!!}
ε-idem (App t t₁) = {!!}
ε-idem (If t Then t₁ Else t₂) = {!!}
ε-idem (Return t) = {!!}
ε-idem (t >>= t₁) = {!!}
ε-idem ξ = {!!}
ε-idem (Throw t) = {!!}
ε-idem (Catch t t₁) = {!!}
ε-idem (Mac t) = {!!}
ε-idem (Macₓ t) = {!!}
ε-idem (Res x t) = {!!}
ε-idem (label x t) = {!!}
ε-idem (unlabel t) = {!!}
ε-idem ∙ = {!!}
