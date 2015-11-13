-- Defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Relation.Binary.PropositionalEquality

ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ

ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)

-- When we don't have a specific value to erase we erase the whole computation
-- afterall it is not visible to the attacker: lʰ ⊑ lₐ
ε-Mac-Labeled-∙ : ∀ {lᵈ lʰ Δ τ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> ¬ (lʰ ⊑ lₐ) -> 
                  Term Δ (Mac lʰ τ) -> Term Δ (Mac lʰ τ)
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Var x) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (App f x) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (If c Then t Else e) 
  = ∙ -- If (ε lₐ c) Then (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a t) Else (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a e)
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Return t) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (m >>= k) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Throw t) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Catch m h) = ∙ -- Catch (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a m) (ε lₐ h)
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Mac t) = Mac ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Macₓ t) = Macₓ ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (label x t) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (unlabel x t) = ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (join {h = lʰ} d⊑h t) = ∙
--  with lʰ ⊑? lₐ
-- ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (join d⊑h t) | yes h⊑a = join d⊑h (ε-Mac lₐ h⊑a t)
-- ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (join d⊑h t) | no ¬h⊑a' = join d⊑h (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a' t) 
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a ∙ = ∙

ε-Mac lₐ p (Var x) = Var x
ε-Mac lₐ p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Mac lₐ p (If c Then t Else e) = If (ε lₐ c) Then (ε-Mac lₐ p t) Else ε-Mac lₐ p e
ε-Mac lₐ p (Return t) = Return (ε lₐ t)
ε-Mac lₐ p (m >>= k) = (ε-Mac lₐ p m) >>= ε lₐ k
ε-Mac lₐ p (Throw t) = Throw (ε lₐ t)
ε-Mac lₐ p (Catch m k) = Catch (ε-Mac lₐ p m) (ε lₐ k)
ε-Mac lₐ p (Mac t) = Mac (ε lₐ t)
ε-Mac lₐ p (Macₓ t) = Macₓ (ε lₐ t)
ε-Mac lₐ p (label {l = lᵈ} {h = lʰ} d⊑h t) with lʰ ⊑? lₐ
ε-Mac lₐ p₁ (label d⊑h t) | yes p = label d⊑h (ε lₐ t)
ε-Mac lₐ p (label d⊑h t) | no ¬p = label d⊑h ∙ 
ε-Mac lₐ p (unlabel x t) = unlabel x (ε lₐ t)
ε-Mac lₐ p (join {l = lᵈ} {h = lʰ} d⊑h t) with lʰ ⊑? lₐ
ε-Mac lₐ p (join d⊑h t) | yes h⊑a = join d⊑h (ε-Mac lₐ h⊑a t)
ε-Mac lₐ d⊑a (join d⊑h t) | no ¬h⊑a = join d⊑h (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a t)
ε-Mac lₐ p ∙ = ∙

ε-Labeled : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> Term Δ (Labeled lᵈ τ) -> Term Δ (Labeled lᵈ τ)
ε-Labeled lₐ p (Var x) = Var x
ε-Labeled lₐ p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Labeled lₐ p (If c Then t Else e) = If (ε lₐ c) Then (ε-Labeled lₐ p t) Else (ε-Labeled lₐ p e)
ε-Labeled lₐ p (Res t) = Res (ε lₐ t)
ε-Labeled lₐ p (Resₓ t) = Resₓ (ε lₐ t)
ε-Labeled lₐ p ∙ = ∙

ε-Labeled-∙ : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> ¬ (lᵈ ⊑ lₐ) -> Term Δ (Labeled lᵈ τ) -> Term Δ (Labeled lᵈ τ)
ε-Labeled-∙ lₐ ¬p (Var x) = Var x
ε-Labeled-∙ lₐ ¬p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Labeled-∙ lₐ ¬p (If t Then t₁ Else t₂) = If ε lₐ t Then ε-Labeled-∙ lₐ ¬p t₁ Else ε-Labeled-∙ lₐ ¬p t₂
ε-Labeled-∙ lₐ ¬p (Res t) = Res ∙
ε-Labeled-∙ lₐ ¬p (Resₓ t) = Resₓ ∙ -- It is not possible to distinguish between Res and Resₓ so its fine to erase the exception only
ε-Labeled-∙ lₐ ¬p ∙ = ∙

ε {Mac lᵈ τ} lₐ t with lᵈ ⊑? lₐ
ε {Mac lᵈ τ} lₐ t | yes p = ε-Mac lₐ p t
ε {Mac lᵈ τ} lₐ t | no ¬p = ∙
ε {Labeled lᵈ τ} lₐ t with lᵈ ⊑? lₐ
ε {Labeled lᵈ τ} lₐ t | yes p = ε-Labeled lₐ p t
ε {Labeled lᵈ τ} lₐ t | no ¬p = ε-Labeled-∙ lₐ ¬p t
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If t Then t₁ Else t₂) = If (ε lₐ t) Then (ε lₐ t₁) Else (ε lₐ t₂)
ε lₐ ξ = ξ
ε lₐ ∙ = ∙

{- 
  Typed-driven erasure function for closed terms.
  
  εᶜ l c transform a term t in ∙ if it is above the security level l.
  
  Note that the erasure function collapse to ∙ composed CTerm (e.g. f $ x, m >>= k),
  but not simple closure (Γ , t), in which the enviroment Γ is erased and only
  the term t is converted into ∙.
  This distinction is essential, because distributivity would be broken otherwise.
  Consider for instance applying the erasure function to the terms in the step Dist-$,
  when the argument is a sensitive computation of type Mac H α:

         (Γ , App f x)   ⟼            (Γ , f)  $  (Γ , x)
    
            ↧ εᶜ                                ↧ εᶜ 
    
    (εᶜ-env Γ, App f ∙)   ⟼   (εᶜ-env Γ, εᶜ f)   $   ∙
         
  The step in the erased term does not hold, because Dist-$ would require
  (εᶜ-env Γ , ∙) ≠ ∙

-}

εᶜ : ∀ {τ} -> Label -> CTerm τ -> CTerm τ
εᶜ-env : ∀ {Δ} -> Label -> Env Δ -> Env Δ

εᶜ-Mac : ∀ {τ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)
εᶜ-Mac-Labeled-∙ : ∀ {lᵈ lʰ τ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> ¬ (lʰ ⊑ lₐ) -> 
                  CTerm (Mac lʰ τ) -> CTerm (Mac lʰ τ)
εᶜ-Mac-∙ : ∀ {lᵈ τ} -> (lₐ : Label) -> ¬ (lᵈ ⊑ lₐ) -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)

εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Γ , t) = (εᶜ-env lₐ Γ) , (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a t)
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (f $ x) = ∙
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (If c Then t Else e) 
  = ∙ -- If (εᶜ lₐ c) Then (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a t) Else (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a e)
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (m >>= k) = ∙
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Catch m h) = ∙ -- Catch (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a m) (εᶜ lₐ h)
εᶜ-Mac-Labeled-∙ lₐ d⊑a _ (unlabel {h = lʰ} h⊑a c) = ∙ -- unlabel h⊑a (εᶜ lₐ c)
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (join {h = lʰ} d⊑h c) = ∙ 
--  with lʰ ⊑? lₐ
-- εᶜ-Mac-Labeled-∙ lₐ d⊑a _ (join d⊑h c) | yes h⊑a = join d⊑h (εᶜ-Mac lₐ h⊑a c)
-- εᶜ-Mac-Labeled-∙ lₐ d⊑a _ (join d⊑h c) | no ¬h⊑a = ∙ -- {!!} -- ljoin d⊑h (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a c)
-- join x {!!}
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a ∙ = ∙

εᶜ-Mac lₐ p (Γ , t) = (εᶜ-env lₐ Γ) , (ε-Mac lₐ p t)
εᶜ-Mac lₐ p (f $ x) = (εᶜ lₐ f) $ (εᶜ lₐ x)
εᶜ-Mac lₐ p (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Mac lₐ p t) Else εᶜ-Mac lₐ p e
εᶜ-Mac lₐ p (m >>= k) = (εᶜ-Mac lₐ p m) >>= (εᶜ lₐ k)
εᶜ-Mac lₐ p (Catch m h) = Catch (εᶜ-Mac lₐ p m) (εᶜ lₐ h)
εᶜ-Mac lₐ p (unlabel x c) = unlabel x (εᶜ lₐ c) 
εᶜ-Mac lₐ p (join {l = lᵈ} {h = lʰ} d⊑h c) with lʰ ⊑? lₐ
εᶜ-Mac lₐ p₁ (join {l = lᵈ} {h = lʰ} d⊑h c) | yes h⊑a = join d⊑h (εᶜ-Mac lₐ h⊑a c)
εᶜ-Mac lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h c) | no ¬h⊑a = join d⊑h (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a c) 
-- Can we try to fix the definition here?
-- Sketch pattern match on type and 
-- in case of Labeled H α call εᶜ-Mac-Labeled-∙ : lᵈ ⊑ lₐ -> ¬ lʰ ⊑ lₐ -> Mac L (Labeled H a) -> Mac L (Labeled H a)
-- which erases only the Labeled part
εᶜ-Mac lₐ p ∙ = ∙

εᶜ-Labeled : ∀ {τ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> CTerm (Labeled lᵈ τ) -> CTerm (Labeled lᵈ τ)
εᶜ-Labeled lₐ p (Γ , t) = εᶜ-env lₐ Γ , ε-Labeled lₐ p t
εᶜ-Labeled lₐ p (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ-Labeled lₐ p (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Labeled lₐ p t) Else (εᶜ-Labeled lₐ p e)
εᶜ-Labeled lₐ p ∙ = ∙

εᶜ-Mac-∙ lₐ ¬p (Γ , t) = εᶜ-env lₐ Γ , ∙
εᶜ-Mac-∙ lₐ ¬p c = ∙

εᶜ-Labeled-∙ : ∀ {lᵈ τ} -> (lₐ : Label) -> ¬ (lᵈ ⊑ lₐ) -> CTerm (Labeled lᵈ τ) -> CTerm (Labeled lᵈ τ)
εᶜ-Labeled-∙ lₐ ¬p (Γ , t) = εᶜ-env lₐ Γ , ε-Labeled-∙ lₐ ¬p t
εᶜ-Labeled-∙ lₐ ¬p (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ-Labeled-∙ lₐ ¬p (If c Then c₁ Else c₂) = If (εᶜ lₐ c) Then (εᶜ-Labeled-∙ lₐ ¬p c₁) Else (εᶜ-Labeled-∙ lₐ ¬p c₂)
εᶜ-Labeled-∙ lₐ ¬p ∙ = ∙ 

εᶜ {Mac lᵈ τ} lₐ c with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ τ} lₐ c | yes p = εᶜ-Mac lₐ p c
εᶜ {Mac lᵈ τ} lₐ c | no ¬p = εᶜ-Mac-∙ lₐ ¬p c
εᶜ {Labeled lᵈ τ} lₐ c with lᵈ ⊑? lₐ
εᶜ {Labeled lᵈ τ} lₐ c | yes p = εᶜ-Labeled lₐ p c
εᶜ {Labeled lᵈ τ} lₐ c | no ¬p = εᶜ-Labeled-∙ lₐ ¬p c
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

εᶜ-Closure : ∀ {τ Δ} {{Γ : Env Δ}} {t : Term Δ τ} (lₐ : Label) -> εᶜ lₐ (Γ , t) ≡ (εᶜ-env lₐ Γ , ε lₐ t)
εᶜ-Closure {Bool} lₐ = refl
εᶜ-Closure {τ => τ₁} lₐ = refl
εᶜ-Closure {Mac lᵈ τ} lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Mac lᵈ τ} lₐ | yes p = refl
εᶜ-Closure {Mac lᵈ τ} lₐ | no ¬p = refl
εᶜ-Closure {Labeled lᵈ τ} lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Labeled lᵈ τ} lₐ | yes p = refl
εᶜ-Closure {Labeled lᵈ τ} lₐ | no ¬p = refl
εᶜ-Closure {Exception} lₐ = refl


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
