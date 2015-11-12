module Security.Distributivity where

open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality


εᶜ-distributes : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⟼ c₂ -> εᶜ lₐ c₁ ⟼ εᶜ lₐ c₂

--------------------------------------------------------------------------------
-- Labeled lemmas
--------------------------------------------------------------------------------
εᶜ-Labeled-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : lᵈ ⊑ lₐ) (Γ : Env Δ) (x : Labeled lᵈ τ ∈ Δ) -> 
                          εᶜ-Labeled lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Labeled-lookup {lᵈ} {lₐ = lₐ} p (x ∷ Γ) Here with lᵈ ⊑? lₐ
εᶜ-Labeled-lookup p (x ∷ Γ) Here | yes q rewrite extensional-⊑ p q = refl 
εᶜ-Labeled-lookup p (x ∷ Γ) Here | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Labeled-lookup p Γ x = refl


-- TODO
-- Why for εᶜ-Labeled-lookup we need extensionality and here we do not?
-- Maybe adjusting the definition we can avoid that postulate.
εᶜ-Labeled-∙-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (¬p : ¬ (lᵈ ⊑ lₐ)) (Γ : Env Δ) (x : Labeled lᵈ τ ∈ Δ) -> 
                          εᶜ-Labeled-∙ lₐ ¬p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Labeled-∙-lookup {lᵈ} {lₐ = lₐ} ¬p (x ∷ Γ) Here with lᵈ ⊑? lₐ
εᶜ-Labeled-∙-lookup ¬p (x ∷ Γ) Here | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-∙-lookup ¬p₁ (x ∷ Γ) Here | no ¬p = refl
εᶜ-Labeled-∙-lookup ¬p (_ ∷ Γ) (There x) rewrite εᶜ-Labeled-∙-lookup ¬p Γ x = refl

εᶜ-Labeled-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Labeled lᵈ τ)} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Labeled lₐ p c₁) ⟼ (εᶜ-Labeled lₐ p c₂)
εᶜ-Labeled-distributes lₐ p (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-Labeled-distributes {lᵈ} lₐ p Beta with lᵈ ⊑? lₐ
εᶜ-Labeled-distributes lₐ p Beta | yes p' = Beta
εᶜ-Labeled-distributes lₐ ¬p Beta | no p = ⊥-elim (p ¬p)
εᶜ-Labeled-distributes {lᵈ} {c₁ = Γ , Var x} lₐ p Lookup with lᵈ ⊑? lₐ
εᶜ-Labeled-distributes {lᵈ} {c₁ = Γ , Var x} lₐ p' Lookup | yes p rewrite εᶜ-Labeled-lookup p Γ x = Lookup
εᶜ-Labeled-distributes {lᵈ} {c₁ = Γ , Var x} lₐ p Lookup | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-distributes {lᵈ} {c₁ = Γ , App f x} lₐ p Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$
εᶜ-Labeled-distributes lₐ p Dist-If = Dist-If
εᶜ-Labeled-distributes lₐ p (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-Labeled-distributes {lᵈ} lₐ p IfTrue with lᵈ ⊑? lₐ
εᶜ-Labeled-distributes lₐ p₁ IfTrue | yes p = IfTrue
εᶜ-Labeled-distributes lₐ p IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-distributes {lᵈ} lₐ p IfFalse with lᵈ ⊑? lₐ
εᶜ-Labeled-distributes lₐ p₁ IfFalse | yes p = IfFalse
εᶜ-Labeled-distributes lₐ p IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-distributes lₐ p Dist-∙ = Dist-∙
εᶜ-Labeled-distributes lₐ p Hole = Hole

εᶜ-Labeled-∙-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Labeled lᵈ τ)} -> (lₐ : Label) -> (p : ¬ (lᵈ ⊑ lₐ)) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Labeled-∙ lₐ p c₁) ⟼ (εᶜ-Labeled-∙ lₐ p c₂)
εᶜ-Labeled-∙-distributes lₐ ¬p (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-Labeled-∙-distributes {lᵈ} lₐ ¬p Beta with lᵈ ⊑? lₐ
εᶜ-Labeled-∙-distributes lₐ ¬p Beta | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-∙-distributes lₐ ¬p₁ Beta | no ¬p = Beta
εᶜ-Labeled-∙-distributes {lᵈ} {c₁ = (Γ , Var x)} lₐ ¬p Lookup with lᵈ ⊑? lₐ
εᶜ-Labeled-∙-distributes {c₁ = (Γ , Var x)} lₐ ¬p Lookup | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-∙-distributes {c₁ = (Γ , Var x)} lₐ ¬p₁ Lookup | no ¬p rewrite εᶜ-Labeled-∙-lookup ¬p Γ x = Lookup
εᶜ-Labeled-∙-distributes {c₁ = Γ , App f x} lₐ ¬p Dist-$ rewrite εᶜ-Closure {t = x} lₐ = Dist-$
εᶜ-Labeled-∙-distributes lₐ ¬p Dist-If = Dist-If
εᶜ-Labeled-∙-distributes lₐ ¬p (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-Labeled-∙-distributes {lᵈ} lₐ ¬p IfTrue with lᵈ ⊑? lₐ
εᶜ-Labeled-∙-distributes lₐ ¬p IfTrue | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-∙-distributes lₐ ¬p₁ IfTrue | no ¬p = IfTrue
εᶜ-Labeled-∙-distributes {lᵈ} lₐ ¬p IfFalse with lᵈ ⊑? lₐ
εᶜ-Labeled-∙-distributes lₐ ¬p IfFalse | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-∙-distributes lₐ ¬p₁ IfFalse | no ¬p = IfFalse
εᶜ-Labeled-∙-distributes lₐ ¬p Dist-∙ = Dist-∙
εᶜ-Labeled-∙-distributes lₐ ¬p Hole = Hole

--------------------------------------------------------------------------------
-- Mac lemmas
--------------------------------------------------------------------------------

εᶜ-Mac-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : lᵈ ⊑ lₐ) (Γ : Env Δ) (x : Mac lᵈ τ ∈ Δ) -> εᶜ-Mac lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Mac-lookup {lᵈ} {lₐ = lₐ} p (x ∷ Γ) Here with lᵈ ⊑? lₐ
εᶜ-Mac-lookup p (x ∷ Γ) Here | yes q rewrite extensional-⊑ p q = refl 
εᶜ-Mac-lookup p (x ∷ Γ) Here | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Mac-lookup p Γ x = refl

εᶜ-Mac-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac lₐ p c₁) ⟼ (εᶜ-Mac lₐ p c₂)
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
εᶜ-Mac-distributes {lᵈ} lₐ p (label {l = .lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-distributes {lᵈ} lₐ d⊑a (label {l = .lᵈ} {h = lʰ} d⊑h) | yes d⊑a' with lʰ ⊑? lₐ
εᶜ-Mac-distributes lₐ d⊑a (label d⊑h) | yes d⊑a' | yes h⊑a = label d⊑h
εᶜ-Mac-distributes lₐ d⊑a (label d⊑h) | yes d⊑a' | no ¬h⊑a = label d⊑h
εᶜ-Mac-distributes lₐ p (label x) | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-distributes lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) | yes d⊑a = Dist-unlabel d⊑h
εᶜ-Mac-distributes lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) | no ¬d⊑a = Dist-unlabel d⊑h -- Also absurd using transitivity
εᶜ-Mac-distributes lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) | yes d⊑a with lʰ ⊑? lₐ
εᶜ-Mac-distributes lₐ h⊑a (unlabel d⊑h) | yes d⊑a | yes h⊑a' = unlabel d⊑h
εᶜ-Mac-distributes lₐ h⊑a (unlabel d⊑h) | yes d⊑a | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-distributes lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) | no ¬d⊑a with lʰ ⊑? lₐ
εᶜ-Mac-distributes lₐ h⊑a (unlabel d⊑h) | no ¬d⊑a | yes h⊑a' = ⊥-elim (¬d⊑a (trans-⊑ d⊑h h⊑a))
εᶜ-Mac-distributes lₐ h⊑a (unlabel d⊑h) | no ¬d⊑a | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-distributes lₐ h⊑a (unlabelCtx {l = lᵈ} {h = lʰ} d⊑h s) with lᵈ ⊑? lₐ
εᶜ-Mac-distributes lₐ h⊑a (unlabelCtx d⊑h s) | yes d⊑a = unlabelCtx d⊑h (εᶜ-Labeled-distributes lₐ d⊑a s)
εᶜ-Mac-distributes lₐ h⊑a (unlabelCtx d⊑h s) | no ¬p = unlabelCtx d⊑h (εᶜ-Labeled-∙-distributes lₐ ¬p s)
εᶜ-Mac-distributes lₐ p Dist-∙ = Dist-∙
εᶜ-Mac-distributes lₐ p Hole = Hole

εᶜ-Mac-∙-distributes : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) -> (p : ¬ (lᵈ ⊑ lₐ)) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac-∙ lₐ p c₁) ⟼ (εᶜ-Mac-∙ lₐ p c₂)
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

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ c₁ c₂ lₐ . if c₁ ⟼ c₂ then (εᶜ lₐ c₁) ⟼ (εᶜ lₐ c₂)
--------------------------------------------------------------------------------

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
εᶜ-distributes {Labeled lᵈ τ} lₐ s with lᵈ ⊑? lₐ
εᶜ-distributes {Labeled lᵈ τ} lₐ s | yes p = εᶜ-Labeled-distributes lₐ p s
εᶜ-distributes {Labeled lᵈ τ} lₐ s | no ¬p = εᶜ-Labeled-∙-distributes lₐ ¬p s
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
