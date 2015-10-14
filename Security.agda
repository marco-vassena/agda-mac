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
ε l₁ (label {h = l₂} x t) with l₁ ⊑? l₂
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

--------------------------------------------------------------------------------

-- Graph of the function ε
-- Erasure l t tₑ corresponds to ε l t ≡ t'
data Erasure (l : Label) {n : ℕ} : Term n -> Term n -> Set where
  True : Erasure l True True
  False : Erasure l False False
  Var : (x : Fin n) -> Erasure l (Var x) (Var x)
  Abs : {t tₑ : Term (suc n)} -> Erasure l t tₑ -> Erasure l (Abs t) (Abs tₑ)
  App : {f fₑ x xₑ : Term n} -> Erasure l f fₑ -> Erasure l x xₑ -> Erasure l (App f x) (App fₑ xₑ)
  If_Then_Else_ : {c cₑ t tₑ e eₑ : Term n} -> 
                  Erasure l c cₑ -> Erasure l t tₑ -> Erasure l e eₑ ->
                  Erasure l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)
  Return : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Return t) (Return tₑ)
  _>>=_ : ∀ {m mₑ k kₑ : Term n} -> Erasure l m mₑ -> Erasure l k kₑ ->
            Erasure l (m >>= k) (mₑ >>= kₑ)
  ξ : Erasure l ξ ξ
  Throw : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Throw t) (Throw tₑ)
  Catch : {m mₑ h hₑ : Term n} -> Erasure l m mₑ -> Erasure l h hₑ -> Erasure l (Catch m h) (Catch mₑ hₑ) 
  Mac : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Mac t) (Mac tₑ)
  Macₓ : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Macₓ t) (Macₓ tₑ)
  Res : {t tₑ : Term n} -> (l' : Label) -> l ⊑ l' -> 
        Erasure l t tₑ -> Erasure l (Res l' t) (Res l' tₑ)
  Res∙ : ∀ {t : Term n} -> (l' : Label) -> ¬ (l ⊑ l') -> Erasure l (Res l' t) (Res l' ∙)
  label : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t tₑ : Term n} -> l ⊑ l₂ -> 
            Erasure l t tₑ -> Erasure l (label x t) (label x tₑ)
  label∙ : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t : Term n} -> ¬ (l ⊑ l₂) -> Erasure l (label x t) (label x ∙) 
  unlabel : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (unlabel t) (unlabel tₑ)
  ∙ : Erasure l ∙ ∙

-- Safety.
-- For any term t I can construct Erasure l t (ε l t), 
-- i.e. Erasure approximates correctly the erasure function. 
ε-Erasure : ∀ {l n} -> (t : Term n) -> Erasure l t (ε l t)
ε-Erasure True = True
ε-Erasure False = False
ε-Erasure (Var x) = Var x
ε-Erasure (Abs t) = Abs (ε-Erasure t)
ε-Erasure (App f x) = App (ε-Erasure f) (ε-Erasure x)
ε-Erasure (If c Then t Else e) = If ε-Erasure c Then ε-Erasure t Else ε-Erasure e
ε-Erasure (Return t) = Return (ε-Erasure t)
ε-Erasure (m >>= k) = ε-Erasure m >>= ε-Erasure k
ε-Erasure ξ = ξ
ε-Erasure (Throw e) = Throw (ε-Erasure e)
ε-Erasure (Catch m h) = Catch (ε-Erasure m) (ε-Erasure h)
ε-Erasure (Mac t) = Mac (ε-Erasure t)
ε-Erasure (Macₓ t) = Macₓ (ε-Erasure t)
ε-Erasure {l₁} (Res l₂ t) with l₁ ⊑? l₂
ε-Erasure (Res l₂ t) | yes p = Res l₂ p (ε-Erasure t)
ε-Erasure (Res l₂ t) | no ¬p = Res∙ l₂ ¬p
ε-Erasure {l₁} (label {h = l₂} x t) with l₁ ⊑? l₂
ε-Erasure (label x t) | yes p = label p (ε-Erasure t)
ε-Erasure (label x t) | no ¬p = label∙ ¬p
ε-Erasure (unlabel t) = unlabel (ε-Erasure t)
ε-Erasure ∙ = ∙

-- Completness
-- For any term t and tₑ such that Erasure l t tₑ, the ε l t ≡ tₑ
-- i.e. Erasure represents only the erasure function.
Erasure-ε : ∀ {l n} {t tₑ : Term n} -> Erasure l t tₑ -> ε l t ≡ tₑ
Erasure-ε True = refl
Erasure-ε False = refl
Erasure-ε (Var x) = refl
Erasure-ε (Abs t) rewrite Erasure-ε t = refl
Erasure-ε (App f x) rewrite Erasure-ε f | Erasure-ε x = refl
Erasure-ε (If c Then t Else e) rewrite
  Erasure-ε c | Erasure-ε t | Erasure-ε e = refl
Erasure-ε (Return t) rewrite Erasure-ε t = refl
Erasure-ε (m >>= k) rewrite Erasure-ε m | Erasure-ε k = refl
Erasure-ε ξ = refl
Erasure-ε (Throw e) rewrite Erasure-ε e = refl
Erasure-ε (Catch m h) rewrite Erasure-ε m | Erasure-ε h = refl
Erasure-ε (Mac t) rewrite Erasure-ε t = refl
Erasure-ε (Macₓ t) rewrite Erasure-ε t = refl
Erasure-ε {l₁} (Res l₂ l₁⊑l₂ t) with l₁ ⊑? l₂
Erasure-ε (Res l₂ l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
Erasure-ε (Res l₂ l₁⊑l₂ t) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε {l₁} (Res∙ l₂ l₁⋢l₂) with l₁ ⊑? l₂
Erasure-ε (Res∙ l₂ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε (Res∙ l₂ l₁⋢l₂) | no _ = refl
Erasure-ε {l₁} (label {l₂ = l₂} l₁⊑l₂ t) with l₁ ⊑? l₂
Erasure-ε (label l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
Erasure-ε (label l₁⊑l₂ t₁) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε {l₁} (label∙ {l₂ = l₂} l₁⋢l₂) with l₁ ⊑? l₂
Erasure-ε (label∙ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε (label∙ l₁⋢l₂) | no _ = refl
Erasure-ε (unlabel t) rewrite Erasure-ε t = refl
Erasure-ε ∙ = refl

ε-idem : ∀ {n} {{l}} {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l tₑ tₑ --  ε l t ≡ ε l (ε l t)
ε-idem True = True
ε-idem False = False
ε-idem (Var x) = Var x
ε-idem (Abs t) = Abs (ε-idem t)
ε-idem (App f x) = App (ε-idem f) (ε-idem x)
ε-idem (If c Then t Else e) = If (ε-idem c) Then (ε-idem t) Else (ε-idem e)
ε-idem (Return t) = Return (ε-idem t)
ε-idem (m >>= k) = (ε-idem m) >>= (ε-idem k)
ε-idem ξ = ξ
ε-idem (Throw e) = Throw (ε-idem e)
ε-idem (Catch m h) = Catch (ε-idem m) (ε-idem h)
ε-idem (Mac t) = Mac (ε-idem t)
ε-idem (Macₓ t) = Macₓ (ε-idem t)
ε-idem (Res l x t) = Res l x (ε-idem t)
ε-idem (Res∙ l x) = Res∙ l x
ε-idem (label x t) = label x (ε-idem t)
ε-idem (label∙ x) = label∙ x
ε-idem (unlabel t) = unlabel (ε-idem t)
ε-idem ∙ = ∙

--------------------------------------------------------------------------------
