-- This module defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Relation.Binary.PropositionalEquality

-- Erasure function for open terms
ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ

-- Erasure function for open Mac terms that are visible to the attacker.
-- It applies ε homomorphically.
ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)

ε-Mac-Labeled : ∀ {lʰ lₐ Δ τ} -> Dec (lʰ ⊑ lₐ) -> Term Δ (Mac lʰ τ) -> Term Δ (Mac lʰ τ)
ε-Mac-Labeled (yes p) t = ε-Mac _ (yes p) t
ε-Mac-Labeled (no ¬p) (Mac t) = Mac ∙
ε-Mac-Labeled (no ¬p) (Macₓ t) = Macₓ ∙
ε-Mac-Labeled (no ¬p) t = ∙

ε-Mac-Labeled∙ : ∀ {τ lʰ Δ} -> Term Δ (Mac lʰ τ) -> Term Δ (Mac lʰ τ)
ε-Mac-Labeled∙ (Mac t) =  Mac ∙
ε-Mac-Labeled∙ (Macₓ t) = Macₓ ∙
ε-Mac-Labeled∙ t = ∙

ε-Mac lₐ (yes p) (Var x) = Var x
ε-Mac lₐ (yes p) (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Mac lₐ (yes p) (If c Then t Else e) = If (ε lₐ c) Then (ε-Mac lₐ (yes p) t) Else (ε-Mac lₐ (yes p) e)
ε-Mac lₐ (yes p) (Return t) = Return (ε lₐ t)
ε-Mac lₐ (yes p) (m >>= k) = (ε-Mac lₐ (yes p) m) >>= (ε lₐ k)
ε-Mac lₐ (yes p) (Throw t) = Throw (ε lₐ t)
ε-Mac lₐ (yes p) (Catch m h) = Catch (ε-Mac lₐ (yes p) m) (ε lₐ h)
ε-Mac lₐ (yes p) (Mac t) = Mac (ε lₐ t)
ε-Mac lₐ (yes p) (Macₓ t) = Macₓ (ε lₐ t)
ε-Mac lₐ (yes p) (label {l = lᵈ} {h = lʰ} x t) with lʰ ⊑? lₐ
ε-Mac lₐ (yes p₁) (label x t) | yes p = label x (ε lₐ t)
ε-Mac lₐ (yes p) (label x t) | no ¬p = label x ∙
ε-Mac lₐ (yes p) (unlabel x t) = unlabel x (ε lₐ t)
ε-Mac lₐ (yes p) (join {l = lᵈ} {h = lʰ} x t) with lʰ ⊑? lₐ
ε-Mac lₐ (yes p₁) (join x t) | yes p = join x (ε-Mac lₐ (yes p) t)
ε-Mac lₐ (yes p) (join x t) | no ¬p = join x (ε-Mac-Labeled∙ t)
ε-Mac lₐ (yes _) (read p r) = read p (ε lₐ r)
ε-Mac lₐ (yes _) (write p r t) = write p (ε lₐ r) (ε lₐ t)
ε-Mac lₐ (yes _) (new p t) = new p (ε lₐ t)
ε-Mac lₐ (yes p) ∙ = ∙
ε-Mac lₐ (no ¬p) t = ∙

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

ε {Mac lᵈ τ} lₐ t = ε-Mac lₐ (lᵈ ⊑? lₐ) t
ε {Labeled lᵈ τ} lₐ t = ε-Labeled lₐ (lᵈ ⊑? lₐ) t
ε lₐ （） = （）
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If t Then t₁ Else t₂) = If (ε lₐ t) Then (ε lₐ t₁) Else (ε lₐ t₂)
ε lₐ ξ = ξ
ε lₐ (Ref n) = Ref n
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

εᶜ-Mac : ∀ {τ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> CTerm (Mac lᵈ τ) -> CTerm (Mac lᵈ τ)

εᶜ-Mac-Labeled : ∀ {lₐ lʰ τ} -> Dec (lʰ ⊑ lₐ) -> CTerm (Mac lʰ τ) -> CTerm (Mac lʰ τ)
εᶜ-Mac-Labeled {lₐ} d (Γ , t) = εᶜ-env lₐ Γ , ε-Mac-Labeled d t
εᶜ-Mac-Labeled {lₐ} (yes p) c = εᶜ-Mac lₐ (yes p) c 
εᶜ-Mac-Labeled (no ¬p) c = ∙

εᶜ-Mac-Labeled∙ : ∀ {τ lʰ} -> (lₐ : Label) -> CTerm (Mac lʰ τ) -> CTerm (Mac lʰ τ)
εᶜ-Mac-Labeled∙ lₐ (Γ , t) = εᶜ-env lₐ Γ , ε-Mac-Labeled∙ t
εᶜ-Mac-Labeled∙ lₐ t = ∙

-- εᵖ-Mac-Labeled∙ : ∀ {τ}
-- lₐ

εᶜ-Mac lₐ p (Γ , t) = εᶜ-env lₐ Γ , ε-Mac lₐ p t
εᶜ-Mac lₐ (yes p) (f $ x) = (εᶜ lₐ f) $ (εᶜ lₐ x)
εᶜ-Mac lₐ (yes p) (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ-Mac lₐ (yes p) t) Else εᶜ-Mac lₐ (yes p) e
εᶜ-Mac lₐ (yes p) (m >>= k) = (εᶜ-Mac lₐ (yes p) m) >>= (εᶜ lₐ k)
εᶜ-Mac lₐ (yes p) (Catch m h) = Catch (εᶜ-Mac lₐ (yes p) m) (εᶜ lₐ h)
εᶜ-Mac lₐ (yes p) (unlabel x c) = unlabel x (εᶜ lₐ c)
εᶜ-Mac lₐ (yes p) (join {l = lᵈ} {h = lʰ} x c) with lʰ ⊑? lₐ
εᶜ-Mac lₐ (yes p₁) (join x c) | yes p = join x (εᶜ-Mac lₐ (yes p) c)
εᶜ-Mac lₐ (yes p) (join x c) | no ¬p = join x (εᶜ-Mac-Labeled∙ lₐ c)
εᶜ-Mac lₐ (yes _) (write {l = lᵈ} {h = lʰ} p r c) = write p (εᶜ lₐ r) (εᶜ lₐ c)
εᶜ-Mac lₐ (yes p) (read {l = l} {h = h} l⊑h r) = read l⊑h (εᶜ lₐ r)
εᶜ-Mac lₐ (yes p) ∙ = ∙
εᶜ-Mac lₐ (no ¬p) c = ∙

εᶜ {Mac lᵈ τ} lₐ c = εᶜ-Mac lₐ (lᵈ ⊑? lₐ) c
εᶜ lₐ (Γ , t) = (εᶜ-env lₐ Γ) , (ε lₐ t)
εᶜ lₐ (f $ x) = εᶜ lₐ f $ εᶜ lₐ x
εᶜ lₐ (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ lₐ t) Else (εᶜ lₐ e)
εᶜ lₐ ∙ = ∙

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

open import Typed.Semantics

εᵐ : ∀ {Δᵐ} -> Label -> Memory Δᵐ -> Memory Δᵐ
εᵐ lₐ [] = []
εᵐ lₐ (c ∷ m) = εᶜ lₐ c ∷ εᵐ lₐ m
εᵐ lₐ ∙ = ∙

εᵖ-Mac : ∀ {Δᵐ τ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Program Δᵐ (Mac lᵈ τ) -> Program Δᵐ (Mac lᵈ τ)
εᵖ-Mac lₐ (yes p) ⟨ m ∥ c ⟩ = ⟨ (εᵐ lₐ m) ∥ (εᶜ-Mac lₐ (yes p) c) ⟩
εᵖ-Mac lₐ (no ¬p) ⟨ m ∥ c ⟩ = ⟨ ∙ ∥ (εᶜ-Mac lₐ (no ¬p) c) ⟩

-- Erasure for programs, i.e. closed term with memory
εᵖ : ∀ {Δᵐ τ} -> Label -> Program Δᵐ τ -> Program Δᵐ τ
εᵖ {τ = Mac lᵈ τ} lₐ p = εᵖ-Mac lₐ (lᵈ ⊑? lₐ) p
εᵖ lₐ ⟨ m ∥ c ⟩ = ⟨ (εᵐ lₐ m) ∥ (εᶜ lₐ c) ⟩

-- Applying the erausre function to an environment and looking up the value is the same
-- as first looking up a variable and then erasing the result.
εᶜ-lookup : ∀ {Δ τ} (lₐ : Label) -> (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ lₐ (p !! Γ) ≡ p !! εᶜ-env lₐ Γ
εᶜ-lookup lₐ Here (x ∷ Γ) = refl
εᶜ-lookup lₐ (There p) (x ∷ Γ) = εᶜ-lookup lₐ p Γ

-- Auxiliary lemma.
-- It is convenient especially when function application is analyzed.
-- The argument has some arbitrary type α and without pattern matching on it
-- Agda will not realize this fact.
εᶜ-Closure : ∀ {τ Δ} {{Γ : Env Δ}} (t : Term Δ τ) (lₐ : Label) -> εᶜ lₐ (Γ , t) ≡ (εᶜ-env lₐ Γ , ε lₐ t)
εᶜ-Closure {（）} _ lₐ = refl
εᶜ-Closure {Bool} t lₐ = refl
εᶜ-Closure {τ => τ₁} t lₐ = refl
εᶜ-Closure {Mac lᵈ τ} t lₐ with lᵈ ⊑? lₐ
εᶜ-Closure {Mac lᵈ τ} t lₐ | yes p = refl
εᶜ-Closure {Mac lᵈ τ} t lₐ | no ¬p = refl
εᶜ-Closure {Labeled lᵈ τ} t lₐ = refl
εᶜ-Closure {Ref lᵈ τ} t lₐ = refl
εᶜ-Closure {Exception} t lₐ = refl

ε-Mac-extensional : ∀ {τ Δ lᵈ lₐ} -> (x y : Dec (lᵈ ⊑ lₐ)) (t : Term Δ (Mac lᵈ τ)) -> ε-Mac lₐ x t ≡ ε-Mac lₐ y t
ε-Mac-extensional (yes p) (yes p₁) (Var x₁) = refl
ε-Mac-extensional (yes p) (no ¬p) (Var x₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Var x₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Var x₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (App t t₁) = refl
ε-Mac-extensional (yes p) (no ¬p) (App t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (App t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (App t t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (If t Then t₁ Else t₂)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t₁ | ε-Mac-extensional (yes p) (yes p₁) t₂ = refl
ε-Mac-extensional (yes p) (no ¬p) (If t Then t₁ Else t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (If t Then t₁ Else t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (If t Then t₁ Else t₂) = refl
ε-Mac-extensional (yes p) (yes p₁) (Return t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Return t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Return t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Return t) = refl
ε-Mac-extensional (yes p) (yes p₁) (t >>= t₁)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t = refl
ε-Mac-extensional (yes p) (no ¬p) (t >>= t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (t >>= t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (t >>= t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (Throw t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Throw t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Throw t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Throw t) = refl
ε-Mac-extensional (yes p) (yes p₁) (Catch t t₁)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t = refl
ε-Mac-extensional (yes p) (no ¬p) (Catch t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Catch t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Catch t t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (Mac t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Mac t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Mac t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Mac t) = refl
ε-Mac-extensional (yes p) (yes p₁) (Macₓ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Macₓ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Macₓ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Macₓ t) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (label {h = lʰ} x₁ t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (label x₁ t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (label x₁ t) | no ¬p = refl
ε-Mac-extensional (yes p) (no ¬p) (label x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (label x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (label x₁ t) = refl
ε-Mac-extensional (yes p) (yes p₁) (unlabel x₁ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (unlabel x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (unlabel x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (unlabel x₁ t) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (join {h = lʰ} x₁ t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (join x₁ t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (join x₁ t) | no ¬p = refl
ε-Mac-extensional (yes p) (no ¬p) (join x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (join x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (join x₁ t) = refl
ε-Mac-extensional (yes p) (yes p₁) (read p₂ r) = refl
ε-Mac-extensional (yes p) (no ¬p) (read p₁ r) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (read p₁ r) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (read p r) = refl
ε-Mac-extensional (yes p) (yes p₁) (write p₂ r t) = refl
ε-Mac-extensional (yes p) (no ¬p) (write p₁ r t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (write p₁ r t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (write p r t) = refl
ε-Mac-extensional (yes p) (yes p₁) (new p₂ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (new p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (new p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (new p t) = refl
ε-Mac-extensional (yes p) (yes p₁) ∙ = refl
ε-Mac-extensional (yes p) (no ¬p) ∙ = refl
ε-Mac-extensional (no ¬p) (yes p) ∙ = refl
ε-Mac-extensional (no ¬p) (no ¬p₁) ∙ = refl

εᶜ-Mac-extensional : ∀ {τ lᵈ lₐ} -> (x y : Dec (lᵈ ⊑ lₐ)) (c : CTerm (Mac lᵈ τ)) -> εᶜ-Mac lₐ x c ≡ εᶜ-Mac lₐ y c
εᶜ-Mac-extensional x y (Γ , t)
  rewrite ε-Mac-extensional x y t = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (c $ c₁) = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (c $ c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (c $ c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (c $ c₁) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (If c Then c₁ Else c₂)
  rewrite εᶜ-Mac-extensional (yes p) (yes p₁) c₁ | εᶜ-Mac-extensional (yes p) (yes p₁) c₂ = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (If c Then c₁ Else c₂) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (If c Then c₁ Else c₂) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (If c Then c₁ Else c₂) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (c >>= c₁)
  rewrite εᶜ-Mac-extensional (yes p) (yes p₁) c = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (c >>= c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (c >>= c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (c >>= c₁) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (Catch c c₁)
  rewrite εᶜ-Mac-extensional (yes p) (yes p₁) c = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (Catch c c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (Catch c c₁) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (Catch c c₁) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (unlabel x₁ c) = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (unlabel x₁ c) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (unlabel x₁ c) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (unlabel x₁ c) = refl
εᶜ-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (join {h = lʰ} x₁ c) with lʰ ⊑? lₐ
εᶜ-Mac-extensional (yes p₁) (yes p₂) (join x₁ c) | yes p = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (join x₁ c) | no ¬p = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (join x₁ c) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (join x₁ c) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (join x₁ c) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (read p₂ r) = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (read p₁ r) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (read p₁ r) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (read p r) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) (write p₂ r t) = refl
εᶜ-Mac-extensional (yes p) (no ¬p) (write p₁ r t) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (yes p) (write p₁ r t) = ⊥-elim (¬p p)
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) (write p r t) = refl
εᶜ-Mac-extensional (yes p) (yes p₁) ∙ = refl
εᶜ-Mac-extensional (yes p) (no ¬p) ∙ = refl
εᶜ-Mac-extensional (no ¬p) (yes p) ∙ = refl
εᶜ-Mac-extensional (no ¬p) (no ¬p₁) ∙ = refl

