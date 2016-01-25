-- This module defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.List as L hiding (drop)

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

open import Data.Product

εᵖ-is-program : ∀ {τ Δᵐ} -> (lₐ : Label) -> (p : Program Δᵐ τ) -> ∃ λ mᵉ → ∃ λ cᵉ → εᵖ lₐ p ≡ ⟨ mᵉ ∥ cᵉ ⟩
εᵖ-is-program {（）} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl
εᵖ-is-program {Bool} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl
εᵖ-is-program {τ => τ₁} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl
εᵖ-is-program {Mac lᵈ τ} lₐ ⟨ m ∥ c ⟩ with lᵈ ⊑? lₐ
εᵖ-is-program {Mac lᵈ τ} lₐ ⟨ m ∥ c ⟩ | yes p = εᵐ lₐ m , ε-Mac lₐ (yes p) c , refl
εᵖ-is-program {Mac lᵈ τ} lₐ ⟨ m ∥ c ⟩ | no ¬p = ∙ , ((ε-Mac lₐ (no ¬p) c) , refl)
εᵖ-is-program {Labeled x τ} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl
εᵖ-is-program {Exception} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl
εᵖ-is-program {Ref x τ} lₐ ⟨ m ∥ c ⟩ = εᵐ lₐ m , ε lₐ c , refl

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

--------------------------------------------------------------------------------

ε-wken : ∀ {α Δ₁ Δ₂} -> (lₐ : Label) -> (t : Term Δ₁ α) (p : Δ₁ ⊆ˡ Δ₂) -> ε lₐ (wken t p) ≡ wken (ε lₐ t) p

ε-Mac-wken : ∀ {lᵈ α Δ₁ Δ₂} -> (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) (t : Term Δ₁ (Mac lᵈ α)) (p : Δ₁ ⊆ˡ Δ₂) -> ε-Mac lₐ x (wken t p) ≡ wken (ε-Mac lₐ x t) p
ε-Mac-wken lₐ (yes p) (Var x₁) p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Var x₁) p = refl
ε-Mac-wken lₐ (yes x) (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-Mac-wken lₐ (no x) (App t t₁) p = refl
ε-Mac-wken lₐ (yes p) (If t Then t₁ Else t₂) p₁
  rewrite ε-wken lₐ t p₁ | ε-Mac-wken lₐ (yes p) t₁ p₁ | ε-Mac-wken lₐ (yes p) t₂ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (If t Then t₁ Else t₂) p = refl
ε-Mac-wken lₐ (yes p) (Return t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Return t) p = refl
ε-Mac-wken lₐ (yes p) (t >>= t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (t >>= t₁) p = refl
ε-Mac-wken lₐ (yes p) (Throw t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Throw t) p = refl
ε-Mac-wken lₐ (yes p) (Catch t t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Catch t t₁) p = refl
ε-Mac-wken lₐ (yes p) (Mac t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Mac t) p = refl
ε-Mac-wken lₐ (yes p) (Macₓ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Macₓ t) p = refl
ε-Mac-wken lₐ (yes p) (label {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (label x₁ t) p₂ | yes p rewrite ε-wken lₐ t p₂ = refl
ε-Mac-wken lₐ (yes p) (label x₁ t) p₁ | no ¬p = refl 
ε-Mac-wken lₐ (no ¬p) (label x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (unlabel x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (unlabel x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (join {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (join x₁ t) p₂ | yes p rewrite ε-Mac-wken lₐ (yes p) t p₂ = refl
ε-Mac-wken lₐ (yes p) (join x₁ t) p₁ | no ¬p = refl
ε-Mac-wken lₐ (no ¬p) (join x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (read x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (read x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (write x₁ t t₁) p₁ rewrite ε-wken lₐ t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (write x₁ t t₁) p = refl
ε-Mac-wken lₐ (yes p) (new x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (new x₁ t) p = refl
ε-Mac-wken lₐ (yes p) ∙ p₁ = refl
ε-Mac-wken lₐ (no ¬p) ∙ p = refl

ε-wken {（）} lₐ （） p = refl
ε-wken {（）} lₐ (Var x) p = refl
ε-wken {（）} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {（）} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {（）} lₐ ∙ p = refl
ε-wken {Bool} lₐ True p = refl
ε-wken {Bool} lₐ False p = refl
ε-wken {Bool} lₐ (Var x) p = refl
ε-wken {Bool} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Bool} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Bool} lₐ ∙ p = refl
ε-wken {α => α₁} lₐ (Var x) p = refl
ε-wken {α => α₁} lₐ (Abs t) p
  rewrite ε-wken lₐ t (cons p) = refl
ε-wken {α => α₁} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {α => α₁} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {α => α₁} lₐ ∙ p = refl
ε-wken {Mac lᵈ α} lₐ t p rewrite ε-Mac-wken lₐ (lᵈ ⊑? lₐ) t p = refl
ε-wken {Labeled x α} lₐ (Var x₁) p = refl
ε-wken {Labeled x α} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Labeled x α} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Labeled lᵈ α} lₐ (Res t) p with lᵈ ⊑? lₐ
ε-wken {Labeled lᵈ α} lₐ (Res t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Labeled lᵈ α} lₐ (Res t) p | no ¬p = refl
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p with lᵈ ⊑? lₐ
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p | no ¬p = refl
ε-wken {Labeled x α} lₐ ∙ p = refl
ε-wken {Exception} lₐ (Var x) p = refl
ε-wken {Exception} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Exception} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Exception} lₐ ξ p = refl
ε-wken {Exception} lₐ ∙ p = refl
ε-wken {Ref x α} lₐ (Var x₁) p = refl
ε-wken {Ref x α} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Ref x α} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Ref x α} lₐ (Ref x₁) p = refl
ε-wken {Ref x α} lₐ ∙ p = refl

ε-subst : ∀ {Δ α β} (lₐ : Label) (x : Term Δ α) (t : Term (α ∷ Δ) β) -> subst (ε lₐ x) (ε lₐ t) ≡ ε lₐ (subst x t)
ε-subst lₐ x t = ε-tm-subst [] _ x t
  where
        ε-tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ) ->
               tm-subst Δ₁ Δ₂ (ε lₐ x) (ε lₐ t) ≡ ε lₐ (tm-subst Δ₁ Δ₂ x t)

        ε-Mac-tm-subst : ∀ {lᵈ α  τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) (Mac lᵈ τ)) (p : Dec (lᵈ ⊑ lₐ)) ->
                         tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ p t) ≡ ε-Mac lₐ p (tm-subst Δ₁ Δ₂ x t)

        ε-var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) -> (p : β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                      var-subst Δ₁ Δ₂ (ε lₐ x) p ≡ ε lₐ (var-subst Δ₁ Δ₂ x p)
        ε-var-subst [] Δ₂ t₁ Here = refl
        ε-var-subst [] Δ t₁ (There p) rewrite εVar≡Var lₐ p = refl
        ε-var-subst (（） ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Bool ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst ((β => β₁) ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here with lᵈ ⊑? lₐ
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | yes p = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | no ¬p = refl
        ε-var-subst (Labeled x₁ β ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Exception ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Ref x₁ β ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (x₁ ∷ Δ₁) Δ₂ t₁ (There p)
          rewrite ε-var-subst Δ₁ Δ₂ t₁ p | ε-wken lₐ (var-subst Δ₁ Δ₂ t₁ p) (drop {x₁} refl-⊆ˡ) = refl

        ε-Mac-var-subst : ∀ {lᵈ α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (y : Dec (lᵈ ⊑ lₐ)) -> (p : (Mac lᵈ β) ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                          tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ y (Var p)) ≡ ε-Mac lₐ y (var-subst Δ₁ Δ₂ x p)

        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (yes p) Here rewrite ε-Mac-extensional (yes p) (lᵈ ⊑? lₐ) x₁ = refl
        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (no ¬p) Here rewrite ε-Mac-extensional (no ¬p) (lᵈ ⊑? lₐ) x₁ =  refl
        ε-Mac-var-subst [] Δ x₁ (yes p) (There p₁) = refl
        ε-Mac-var-subst [] Δ x₁ (no ¬p) (There p) = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (yes p) Here = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (no ¬p) Here = refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (yes p) (There p₁)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (yes p) p₁ | ε-Mac-wken lₐ (yes p) (var-subst Δ₁ Δ₂ x₂ p₁) (drop {x₁} refl-⊆ˡ) =  refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (no ¬p) (There p)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (no ¬p) p | ε-Mac-wken lₐ (no ¬p) (var-subst Δ₁ Δ₂ x₂ p) (drop {x₁} refl-⊆ˡ) =  refl

        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ （） = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ True = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ False = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Abs t₁)
          rewrite ε-tm-subst (_ ∷ Δ₁) Δ₂ x₁ t₁ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Mac lᵈ τ} Δ₁ Δ₂ x₂ t₁ = ε-Mac-tm-subst Δ₁ Δ₂ x₂ t₁ (lᵈ ⊑? lₐ)
        ε-tm-subst {τ = Labeled x₁ τ} Δ₁ Δ₂ x₂ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₂ x₃ = refl
        ε-tm-subst {τ = Labeled l τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Labeled l τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | no ¬p = refl
        ε-tm-subst {τ = Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | no ¬p = refl
        ε-tm-subst {τ = Labeled x₁ τ} Δ₁ Δ₂ x₂ ∙ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ξ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₃ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (Ref x₃) = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₂ ∙ = refl

        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Var p) x rewrite ε-Mac-var-subst Δ₁ Δ₂ x₁ x p = refl         
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₂ (yes p) | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₃ (yes p) = refl                        
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p₁) | yes p 
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p) | no ¬p = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p₁) | yes p
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p) | no ¬p = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl 
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (no ¬p) = refl

ε-Mac-subst : ∀ {lᵈ Δ α β} (lₐ : Label) (y : Dec (lᵈ ⊑ lₐ)) (x : Term Δ α) (t : Term (α ∷ Δ) (Mac lᵈ β))
              -> subst (ε lₐ x) (ε-Mac lₐ (lᵈ ⊑? lₐ) t) ≡ (ε-Mac lₐ y (subst x t))
ε-Mac-subst {lᵈ} lₐ y x t rewrite ε-Mac-extensional y (lᵈ ⊑? lₐ) (subst x t) = ε-subst lₐ x t

ε-Mac-CTerm≡∙ : ∀ {lᵈ τ} (lₐ : Label) (c : CTerm (Mac lᵈ τ)) (x : ¬ (lᵈ ⊑ lₐ)) -> ε-Mac lₐ (no x) c ≡ ∙
ε-Mac-CTerm≡∙ lₐ (Var ()) x₁
ε-Mac-CTerm≡∙ lₐ (App c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (If c Then c₁ Else c₂) x = refl
ε-Mac-CTerm≡∙ lₐ (Return c) x = refl
ε-Mac-CTerm≡∙ lₐ (c >>= c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Throw c) x = refl
ε-Mac-CTerm≡∙ lₐ (Catch c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Mac c) x = refl
ε-Mac-CTerm≡∙ lₐ (Macₓ c) x = refl
ε-Mac-CTerm≡∙ lₐ (label x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (unlabel x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (join x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (read x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (write x c c₁) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (new x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ ∙ x = refl
