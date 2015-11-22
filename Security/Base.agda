-- This module defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Relation.Binary.PropositionalEquality

-- Erasure function for open terms
ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ

-- Erasure function for open Mac terms that are visible to the attacker.
-- It applies ε homomorphically.
ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)

-- This erasure function is used to erase values produced by sensitive
-- computation. In particular this function does not always completely
-- collapse the computation to ∙, but for Mac and Macₓ it preserves
-- the constructors. This function is used to erase appropriately
-- a sensitive compution wrapped in a join.
ε-Mac-Labeled-∙ : ∀ {lᵈ lʰ Δ τ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> ¬ (lʰ ⊑ lₐ) -> 
                  Term Δ (Mac lʰ τ) -> Term Δ (Mac lʰ τ)
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Mac t) = Mac ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Macₓ t) = Macₓ ∙
ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a _ = ∙

ε-Mac lₐ p (Var x) = Var x
ε-Mac lₐ p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Mac lₐ p (If c Then t Else e) = If (ε lₐ c) Then (ε-Mac lₐ p t) Else (ε-Mac lₐ p e)
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

-- Erasure function for open Labeled terms that are visible to the attacker.
ε-Labeled : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Term Δ (Labeled lᵈ τ) -> Term Δ (Labeled lᵈ τ)
ε-Labeled lₐ p (Var x) = Var x
ε-Labeled lₐ p (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Labeled lₐ p (If c Then t Else e) = If (ε lₐ c) Then (ε-Labeled lₐ p t) Else (ε-Labeled lₐ p e)
ε-Labeled lₐ (yes p) (Res t) = Res (ε lₐ t)
ε-Labeled lₐ (no ¬p) (Res t) = Res ∙
ε-Labeled lₐ (yes p) (Resₓ t) = Resₓ (ε lₐ t)
ε-Labeled lₐ (no ¬p) (Resₓ t) = Resₓ ∙
ε-Labeled lₐ p ∙ = ∙

ε {Mac lᵈ τ} lₐ t with lᵈ ⊑? lₐ
ε {Mac lᵈ τ} lₐ t | yes p = ε-Mac lₐ p t
ε {Mac lᵈ τ} lₐ t | no ¬p = ∙
ε {Labeled lᵈ τ} lₐ t = ε-Labeled lₐ (lᵈ ⊑? lₐ) t
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
  the open term t is converted into ∙.
  This distinction is essential, because distributivity would be broken otherwise.
  Consider for instance applying the erasure function to the terms in the step Dist-$,
  when the argument is a sensitive computation of type Mac H α:

         (Γ , App f x)   ⟼            (Γ , f)  $  (Γ , x)
    
            ↧ εᶜ                                ↧ εᶜ 
    
    (εᶜ-env Γ, App f ∙)   ⟼   (εᶜ-env Γ, εᶜ f)   $   ∙
         
  The step between the erased terms does not hold, because Dist-$ would require
  (εᶜ-env Γ , ∙) ≠ ∙

-}

εᶜ : ∀ {τ} -> Label -> CTerm τ -> CTerm τ
εᶜ-env : ∀ {Δ} -> Label -> Env Δ -> Env Δ

εᶜ-Mac : ∀ {τ lᵈ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)
εᶜ-Mac-Labeled-∙ : ∀ {lᵈ lʰ τ} -> (lₐ : Label) -> lᵈ ⊑ lₐ -> ¬ (lʰ ⊑ lₐ) -> 
                  CTerm (Mac lʰ τ) -> CTerm (Mac lʰ τ)
εᶜ-Mac-∙ : ∀ {lᵈ τ} -> (lₐ : Label) -> ¬ (lᵈ ⊑ lₐ) -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)

-- Erasure function for closed term of type Mac L (Labeled H α), whose computation is visible
-- to the attacker, but not the labeled resource.
-- It maps closures calling ε-Mac-Labeled-∙, otherwise it completely
-- collapse to ∙ the computation.
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a (Γ , t) = (εᶜ-env lₐ Γ) , (ε-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a t)
εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a _ = ∙

εᶜ-Mac lₐ p (Γ , t) = (εᶜ-env lₐ Γ) , (ε-Mac lₐ p t)
εᶜ-Mac lₐ p (f $ x) = (εᶜ lₐ f) $ (εᶜ lₐ x)
εᶜ-Mac lₐ p (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Mac lₐ p t) Else εᶜ-Mac lₐ p e
εᶜ-Mac lₐ p (m >>= k) = (εᶜ-Mac lₐ p m) >>= (εᶜ lₐ k)
εᶜ-Mac lₐ p (Catch m h) = Catch (εᶜ-Mac lₐ p m) (εᶜ lₐ h)
εᶜ-Mac lₐ p (unlabel x c) = unlabel x (εᶜ lₐ c) 
εᶜ-Mac lₐ p (join {l = lᵈ} {h = lʰ} d⊑h c) with lʰ ⊑? lₐ
εᶜ-Mac lₐ p₁ (join {l = lᵈ} {h = lʰ} d⊑h c) | yes h⊑a = join d⊑h (εᶜ-Mac lₐ h⊑a c)
εᶜ-Mac lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h c) | no ¬h⊑a = join d⊑h (εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a c) 
εᶜ-Mac lₐ p ∙ = ∙

-- Erasure function for closed labeled terms that are visible to the attacker
εᶜ-Labeled : ∀ {τ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> CTerm (Labeled lᵈ τ) -> CTerm (Labeled lᵈ τ)
εᶜ-Labeled lₐ p (Γ , t) = εᶜ-env lₐ Γ , ε-Labeled lₐ p t
εᶜ-Labeled lₐ p (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ-Labeled lₐ p (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Labeled lₐ p t) Else (εᶜ-Labeled lₐ p e)
εᶜ-Labeled lₐ p ∙ = ∙

εᶜ-Mac-∙ lₐ ¬p (Γ , t) = εᶜ-env lₐ Γ , ∙
εᶜ-Mac-∙ lₐ ¬p c = ∙

εᶜ {Mac lᵈ τ} lₐ c with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ τ} lₐ c | yes p = εᶜ-Mac lₐ p c
εᶜ {Mac lᵈ τ} lₐ c | no ¬p = εᶜ-Mac-∙ lₐ ¬p c
εᶜ {Labeled lᵈ τ} lₐ c = εᶜ-Labeled lₐ (lᵈ ⊑? lₐ) c
εᶜ lₐ (Γ , t) = (εᶜ-env lₐ Γ) , (ε lₐ t)
εᶜ lₐ (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ lₐ (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ lₐ t) Else (εᶜ lₐ e)
εᶜ lₐ ∙ = ∙

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

open import Typed.Semantics

-- Applying the erausre function to an environment and looking up the value is the same
-- as first looking up a variable and then erasing the result.
εᶜ-lookup : ∀ {Δ τ} {{lₐ}} -> (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ lₐ (p !! Γ) ≡ p !! εᶜ-env lₐ Γ
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

-- Auxiliary lemma.
-- It is convenient especially when function application is analyzed.
-- The argument has some arbitrary type α and without pattern matching on it
-- Agda will not realize this fact.
εᶜ-Closure : ∀ {τ Δ} {{Γ : Env Δ}} (t : Term Δ τ) (lₐ : Label) -> εᶜ lₐ (Γ , t) ≡ (εᶜ-env lₐ Γ , ε lₐ t)
εᶜ-Closure {Bool} t lₐ = refl
εᶜ-Closure {τ => τ₁} t lₐ = refl
εᶜ-Closure {Mac lᵈ τ} t lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Mac lᵈ τ} t lₐ | yes p = refl
εᶜ-Closure {Mac lᵈ τ} t lₐ | no ¬p = refl
εᶜ-Closure {Labeled lᵈ τ} t lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Labeled lᵈ τ} t lₐ | yes p = refl
εᶜ-Closure {Labeled lᵈ τ} t lₐ | no ¬p = refl
εᶜ-Closure {Exception} t lₐ = refl

ε-Labeled-extensional : ∀ {τ Δ lᵈ lₐ} -> (x y : Dec (lᵈ ⊑ lₐ)) (t : Term Δ (Labeled lᵈ τ)) ->
                           ε-Labeled lₐ x t ≡ ε-Labeled lₐ y t
ε-Labeled-extensional _ _ (Var x) = refl
ε-Labeled-extensional _ _ (App f x) = refl
ε-Labeled-extensional x y (If c Then t Else e)
  rewrite ε-Labeled-extensional x y t | ε-Labeled-extensional x y e = refl
ε-Labeled-extensional (yes p) (yes p₁) (Res t) = refl
ε-Labeled-extensional (yes p) (no ¬p) (Res t) = ⊥-elim (¬p p)
ε-Labeled-extensional (no ¬p) (yes p) (Res t) = ⊥-elim (¬p p)
ε-Labeled-extensional (no ¬p) (no ¬p₁) (Res t) = refl
ε-Labeled-extensional (yes p) (yes p₁) (Resₓ t) = refl
ε-Labeled-extensional (yes p) (no ¬p) (Resₓ t) = ⊥-elim (¬p p)
ε-Labeled-extensional (no ¬p) (yes p) (Resₓ t) = ⊥-elim (¬p p)
ε-Labeled-extensional (no ¬p) (no ¬p₁) (Resₓ t) = refl
ε-Labeled-extensional _ _ ∙ = refl

εᶜ-Labeled-extensional : ∀ {τ lᵈ lₐ} -> (x y : Dec (lᵈ ⊑ lₐ)) (c : CTerm (Labeled lᵈ τ)) ->
                           εᶜ-Labeled lₐ x c ≡ εᶜ-Labeled lₐ y c
εᶜ-Labeled-extensional x y (Γ , t) rewrite ε-Labeled-extensional x y t = refl
εᶜ-Labeled-extensional _ _ (f $ x) = refl
εᶜ-Labeled-extensional x y (If c Then t Else e)
  rewrite εᶜ-Labeled-extensional x y t | εᶜ-Labeled-extensional x y e = refl
εᶜ-Labeled-extensional _ _ ∙ = refl
