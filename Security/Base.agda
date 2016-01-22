-- This module defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality

-- Erasure function for open terms
ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ

-- Erasure function for open Mac terms that are visible to the attacker.
-- It applies ε homomorphically.
ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)

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
ε-Mac lₐ (yes p) (join x t) | no ¬p = join x (Mac ∙)
ε-Mac lₐ (yes _) (read p r) = read p (ε lₐ r)
ε-Mac lₐ (yes _) (write p r t) = write p (ε lₐ r) (ε lₐ t)
ε-Mac lₐ (yes _) (new p t) = new p (ε lₐ t)
ε-Mac lₐ (yes p) ∙ = ∙
ε-Mac lₐ (no ¬p) (Var x) = Var x
ε-Mac lₐ (no ¬p) t = ∙

ε {Mac lᵈ τ} lₐ t = ε-Mac lₐ (lᵈ ⊑? lₐ) t
ε lₐ （） = （）
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If t Then t₁ Else t₂) = If (ε lₐ t) Then (ε lₐ t₁) Else (ε lₐ t₂)
ε {Labeled lᵈ τ} lₐ (Res t) with lᵈ ⊑? lₐ
ε {Labeled lᵈ τ} lₐ (Res t) | yes p = Res (ε lₐ t)
ε {Labeled lᵈ τ} lₐ (Res t) | no ¬p = Res ∙
ε {Labeled lᵈ τ} lₐ (Resₓ t) with lᵈ ⊑? lₐ
ε {Labeled lᵈ τ} lₐ (Resₓ t) | yes p = Resₓ (ε lₐ t)
-- It is not possible to distinguish between Res and Resₓ when they are sensitive,
-- because you would need to be in a high computation to unlabel them,
-- which would get collapsed.
ε {Labeled lᵈ τ} lₐ (Resₓ t) | no ¬p = Res ∙
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



εᵐ : ∀ {Δᵐ} -> Label -> Memory Δᵐ -> Memory Δᵐ
εᵐ lₐ [] = []
εᵐ lₐ (x ∷ m) = (ε lₐ x) ∷ (εᵐ lₐ m)
εᵐ lₐ ∙ = ∙

εᵖ-Mac : ∀ {τ lᵈ Δᵐ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Program Δᵐ (Mac lᵈ τ) -> Program Δᵐ (Mac lᵈ τ)
εᵖ-Mac {τ} lₐ (yes p) ⟨ m ∥ c ⟩ = ⟨ (εᵐ lₐ  m) ∥ (ε-Mac lₐ (yes p) c) ⟩
εᵖ-Mac lₐ (no ¬p) ⟨ m ∥ c ⟩ = ⟨ ∙ ∥ (ε-Mac lₐ (no ¬p) c) ⟩

-- Erasure for programs, i.e. closed term with memory
εᵖ : ∀ {Δᵐ τ} -> Label -> Program Δᵐ τ -> Program Δᵐ τ
εᵖ {τ = Mac lᵈ τ} lₐ p = εᵖ-Mac lₐ (lᵈ ⊑? lₐ) p
εᵖ lₐ ⟨ m ∥ c ⟩ = ⟨ εᵐ lₐ m ∥ ε lₐ c ⟩

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

ε∙≡∙ : ∀ {τ : Ty} {Δ : Context} -> (lₐ : Label) -> ε {τ} {Δ} lₐ ∙ ≡ ∙
ε∙≡∙ {（）} lₐ = refl
ε∙≡∙ {Bool} lₐ = refl
ε∙≡∙ {τ => τ₁} lₐ = refl
ε∙≡∙ {Mac lᵈ τ} lₐ with lᵈ ⊑? lₐ
ε∙≡∙ {Mac lᵈ τ} lₐ | yes p = refl
ε∙≡∙ {Mac lᵈ τ} lₐ | no ¬p = refl
ε∙≡∙ {Labeled x τ} lₐ = refl
ε∙≡∙ {Exception} lₐ = refl
ε∙≡∙ {Ref x τ} lₐ = refl

εVar≡Var : ∀ {α Δ} -> (lₐ : Label) (p : α ∈ Δ) -> ε lₐ (Var p) ≡ Var p
εVar≡Var {（）} lₐ p = refl
εVar≡Var {Bool} lₐ p = refl
εVar≡Var {α => α₁} lₐ p = refl
εVar≡Var {Mac lᵈ α} lₐ p with lᵈ ⊑? lₐ
εVar≡Var {Mac lᵈ α} lₐ p₁ | yes p = refl
εVar≡Var {Mac lᵈ α} lₐ p | no ¬p = refl
εVar≡Var {Labeled x α} lₐ p = refl
εVar≡Var {Exception} lₐ p = refl
εVar≡Var {Ref x α} lₐ p = refl

εVar≡Var' : ∀ {α Δ} -> (lₐ : Label) (p : α ∈ Δ) ->  Var p ≡ ε lₐ (Var p)
εVar≡Var' lₐ p = sym (εVar≡Var lₐ p)
