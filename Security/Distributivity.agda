module Security.Distributivity where

open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality 

-- The closed term erasure function distributes over the small step semantics.
εᶜ-dist : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⟼ c₂ -> εᶜ lₐ c₁ ⟼ εᶜ lₐ c₂

--------------------------------------------------------------------------------
-- Auxliary distributivity lemmas for Labeled closed terms
--------------------------------------------------------------------------------

εᶜ-Labeled-lookup : ∀ {lᵈ lₐ τ Δ} (p : Dec (lᵈ ⊑ lₐ)) (Γ : Env Δ) (x : Labeled lᵈ τ ∈ Δ) -> 
                          εᶜ-Labeled lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Labeled-lookup {lᵈ} {lₐ} p (c ∷ Γ) Here rewrite εᶜ-Labeled-extensional p (lᵈ ⊑? lₐ) c = refl
εᶜ-Labeled-lookup p (_ ∷ Γ) (There x) = εᶜ-Labeled-lookup p Γ x 

εᶜ-Labeled-dist : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Labeled lᵈ τ)} -> (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) ->
                       c₁ ⟼ c₂ -> (εᶜ-Labeled lₐ x c₁) ⟼ (εᶜ-Labeled lₐ x c₂)
εᶜ-Labeled-dist lₐ x (AppL s) = AppL (εᶜ-dist lₐ s)
εᶜ-Labeled-dist {lᵈ} lₐ x Beta with lᵈ ⊑? lₐ
εᶜ-Labeled-dist lₐ x Beta | yes p = Beta
εᶜ-Labeled-dist lₐ x Beta | no ¬p = Beta
εᶜ-Labeled-dist {lᵈ} lₐ x Lookup with lᵈ ⊑? lₐ
εᶜ-Labeled-dist lₐ d (Lookup {Γ = Γ} {p = x}) | yes p rewrite εᶜ-Labeled-lookup (yes p) Γ x = Lookup
εᶜ-Labeled-dist lₐ d (Lookup {Γ = Γ} {p = x}) | no ¬p rewrite εᶜ-Labeled-lookup (no ¬p) Γ x = Lookup
εᶜ-Labeled-dist lₐ d (Dist-$ {x = x}) rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-Labeled-dist lₐ x Dist-If = Dist-If
εᶜ-Labeled-dist lₐ x (IfCond s) = IfCond (εᶜ-dist lₐ s)
εᶜ-Labeled-dist {lᵈ} lₐ x IfTrue with lᵈ ⊑? lₐ
εᶜ-Labeled-dist lₐ (yes p₁) (IfTrue {t = t}) | yes p rewrite εᶜ-Labeled-extensional (yes p) (yes p₁) t = IfTrue
εᶜ-Labeled-dist lₐ (no ¬p) IfTrue | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-dist lₐ (yes p) IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-dist lₐ (no ¬p₁) (IfTrue {t = t}) | no ¬p rewrite εᶜ-Labeled-extensional (no ¬p) (no ¬p₁) t = IfTrue
εᶜ-Labeled-dist {lᵈ} lₐ x IfFalse with lᵈ ⊑? lₐ
εᶜ-Labeled-dist lₐ (yes p₁) (IfFalse {e = e}) | yes p rewrite εᶜ-Labeled-extensional (yes p) (yes p₁) e = IfFalse
εᶜ-Labeled-dist lₐ (no ¬p) IfFalse | yes p = ⊥-elim (¬p p)
εᶜ-Labeled-dist lₐ (yes p) IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Labeled-dist lₐ (no ¬p₁) (IfFalse {e = e}) | no ¬p rewrite εᶜ-Labeled-extensional (no ¬p) (no ¬p₁) e = IfFalse
εᶜ-Labeled-dist lₐ x Dist-∙ = Dist-∙
εᶜ-Labeled-dist lₐ x Hole = Hole

--------------------------------------------------------------------------------
-- Auxliary distributivity lemmas for Mac closed terms
--------------------------------------------------------------------------------

εᶜ-Mac-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : lᵈ ⊑ lₐ) (Γ : Env Δ) (x : Mac lᵈ τ ∈ Δ)
                -> εᶜ-Mac lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Mac-lookup {lᵈ} {lₐ = lₐ} p (x ∷ Γ) Here with lᵈ ⊑? lₐ
εᶜ-Mac-lookup p (x ∷ Γ) Here | yes q rewrite extensional-⊑ p q = refl 
εᶜ-Mac-lookup p (x ∷ Γ) Here | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Mac-lookup p Γ x = refl

εᶜ-Mac-dist : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac lₐ p c₁) ⟼ (εᶜ-Mac lₐ p c₂)

εᶜ-Mac-∙-dist : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) -> (p : ¬ (lᵈ ⊑ lₐ)) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac-∙ lₐ p c₁) ⟼ (εᶜ-Mac-∙ lₐ p c₂)

εᶜ-Mac-Labeled-∙-dist : ∀ {lʰ lᵈ τ} {c₁ c₂ : CTerm (Mac lʰ τ)} -> (lₐ : Label) -> 
                      (d⊑a : lᵈ ⊑ lₐ) -> (¬h⊑a : ¬ lʰ ⊑ lₐ) -> c₁ ⟼ c₂ ->
                      εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a c₁ ⟼ εᶜ-Mac-Labeled-∙ lₐ d⊑a ¬h⊑a c₂
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (AppL s) = Hole
εᶜ-Mac-Labeled-∙-dist {lʰ} lₐ d⊑a ¬h⊑a Beta with lʰ ⊑? lₐ
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Beta | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Beta | no ¬h⊑a' = Hole
εᶜ-Mac-Labeled-∙-dist {lʰ} lₐ d⊑a ¬h⊑a Lookup with lʰ ⊑? lₐ
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Lookup | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Lookup | no ¬h⊑a' = Dist-∙
εᶜ-Mac-Labeled-∙-dist {c₁ = Γ , App f x} lₐ d⊑a ¬h⊑a Dist-$ = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Dist-If = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (IfCond s) = Hole
εᶜ-Mac-Labeled-∙-dist {lʰ} lₐ d⊑a ¬h⊑a IfTrue with lʰ ⊑? lₐ
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a IfTrue | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a IfTrue | no ¬h⊑a' = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a IfFalse = Hole
εᶜ-Mac-Labeled-∙-dist {lʰ} lₐ d⊑a ¬h⊑a Return with lʰ ⊑? lₐ
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Return | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Return | no ¬h⊑a' = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Dist->>= = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (BindCtx s) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Bind = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a BindEx = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Throw = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Dist-Catch = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (CatchCtx s) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Catch = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a CatchEx = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (label p) = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (Dist-unlabel p) = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (unlabel p) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (unlabelEx p) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (unlabelCtx p s) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (Dist-join {h = lʰ} p) = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (joinCtx {h = lʰ} p s) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ _ ¬d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a (joinEx p) = Hole
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Dist-∙ = Dist-∙
εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a Hole = Hole

εᶜ-Mac-dist lₐ p (AppL s) = AppL (εᶜ-dist lₐ s)
εᶜ-Mac-dist {lᵈ} lₐ p Beta with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ Beta | yes p = Beta
εᶜ-Mac-dist lₐ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist {lᵈ} {c₁ = Γ , Var x} lₐ p Lookup with lᵈ ⊑? lₐ
εᶜ-Mac-dist {lᵈ} {τ} {Γ , Var x} lₐ p₁ Lookup | yes p rewrite εᶜ-Mac-lookup p Γ x = Lookup
εᶜ-Mac-dist {lᵈ} {τ} {Γ , Var x} lₐ p Lookup | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ p (Dist-$ {α = Bool}) = Dist-$
εᶜ-Mac-dist lₐ p (Dist-$ {α = α => α₁}) = Dist-$
εᶜ-Mac-dist {c₁ = Γ , App f x} lₐ p  Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$ 
εᶜ-Mac-dist lₐ p Dist-If = Dist-If
εᶜ-Mac-dist lₐ p (IfCond s) = IfCond (εᶜ-dist lₐ s)
εᶜ-Mac-dist {lᵈ} lₐ p IfTrue with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ IfTrue | yes p = IfTrue
εᶜ-Mac-dist lₐ p IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist {lᵈ} lₐ p IfFalse with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ IfFalse | yes p = IfFalse
εᶜ-Mac-dist lₐ p IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist {lᵈ} lₐ p Return with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ Return | yes p = Return
εᶜ-Mac-dist lₐ p Return | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ p Dist->>= = Dist->>=
εᶜ-Mac-dist lₐ p (BindCtx s) = BindCtx (εᶜ-Mac-dist lₐ p s)
εᶜ-Mac-dist {lᵈ} {τ} {c₁ = (Γ , Mac t) >>= k} lₐ p Bind rewrite εᶜ-Closure t lₐ = Bind
εᶜ-Mac-dist {lᵈ} lₐ p BindEx with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ BindEx | yes p = BindEx
εᶜ-Mac-dist lₐ p BindEx | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist {lᵈ} lₐ p Throw with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ Throw | yes p = Throw
εᶜ-Mac-dist lₐ p Throw | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ p Dist-Catch = Dist-Catch
εᶜ-Mac-dist lₐ p (CatchCtx s) = CatchCtx (εᶜ-Mac-dist lₐ p s)
εᶜ-Mac-dist {lᵈ} lₐ p Catch with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ p₁ Catch | yes p = Catch
εᶜ-Mac-dist lₐ p Catch | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ p CatchEx = CatchEx
εᶜ-Mac-dist {lᵈ} lₐ p (label {l = .lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist {lᵈ} lₐ d⊑a (label {l = .lᵈ} {h = lʰ} d⊑h) | yes d⊑a' with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (label d⊑h) | yes d⊑a' | yes h⊑a = label d⊑h
εᶜ-Mac-dist lₐ d⊑a (label d⊑h) | yes d⊑a' | no ¬h⊑a = label d⊑h
εᶜ-Mac-dist lₐ p (label x) | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) | yes d⊑a = Dist-unlabel d⊑h
εᶜ-Mac-dist lₐ h⊑a (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) | no ¬d⊑a = Dist-unlabel d⊑h
εᶜ-Mac-dist lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) | yes d⊑a with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabel d⊑h) | yes d⊑a | yes h⊑a' = unlabel d⊑h
εᶜ-Mac-dist lₐ h⊑a (unlabel d⊑h) | yes d⊑a | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ h⊑a (unlabel {l = lᵈ} {h = lʰ} d⊑h) | no ¬d⊑a with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabel d⊑h) | no ¬d⊑a | yes h⊑a' = ⊥-elim (¬d⊑a (trans-⊑ d⊑h h⊑a))
εᶜ-Mac-dist lₐ h⊑a (unlabel d⊑h) | no ¬d⊑a | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ h⊑a (unlabelEx {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabelEx {l = lᵈ} {h = lʰ} d⊑h) | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabelEx d⊑h) | yes p₁ | yes p = unlabelEx d⊑h
εᶜ-Mac-dist lₐ h⊑a (unlabelEx d⊑h) | yes p | no ¬p = ⊥-elim (¬p h⊑a)
εᶜ-Mac-dist lₐ h⊑a (unlabelEx {l = lᵈ} {h = lʰ} d⊑h) | no ¬p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabelEx d⊑h) | no ¬p | yes p = ⊥-elim (¬p (trans-⊑ d⊑h h⊑a))
εᶜ-Mac-dist lₐ h⊑a (unlabelEx d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p h⊑a)
εᶜ-Mac-dist lₐ h⊑a (unlabelCtx {l = lᵈ} {h = lʰ} d⊑h s) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ h⊑a (unlabelCtx d⊑h s) | yes d⊑a = unlabelCtx d⊑h (εᶜ-Labeled-dist lₐ (yes d⊑a) s)
εᶜ-Mac-dist lₐ h⊑a (unlabelCtx d⊑h s) | no ¬p = unlabelCtx d⊑h (εᶜ-Labeled-dist lₐ (no ¬p) s)
εᶜ-Mac-dist lₐ d⊑a (Dist-join {l = lᵈ} {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (Dist-join {l = lᵈ} {h = lʰ} d⊑h) | yes h⊑a = Dist-join d⊑h
εᶜ-Mac-dist lₐ d⊑a (Dist-join d⊑h) | no ¬h⊑a = Dist-join d⊑h
εᶜ-Mac-dist lₐ d⊑a (joinCtx {l = lᵈ} {h = lʰ} d⊑h s) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinCtx d⊑h s) | yes h⊑a = joinCtx d⊑h (εᶜ-Mac-dist lₐ h⊑a s)
εᶜ-Mac-dist lₐ d⊑a (joinCtx {l = lᵈ} {h = lʰ} d⊑h s) | no ¬h⊑a = joinCtx d⊑h (εᶜ-Mac-Labeled-∙-dist lₐ d⊑a ¬h⊑a s)
εᶜ-Mac-dist lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) | yes h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) | yes h⊑a | yes d⊑a' with lʰ ⊑? lₐ 
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | yes h⊑a | yes d⊑a' | yes h⊑a' = join d⊑h
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | yes h⊑a | yes d⊑a' | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | yes h⊑a | no ¬d⊑a = ⊥-elim (¬d⊑a d⊑a)
εᶜ-Mac-dist lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) | no ¬h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (join {l = lᵈ} {h = lʰ} d⊑h) | no ¬h⊑a | yes d⊑a' with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | no ¬h⊑a | yes d⊑a' | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | no ¬h⊑a | yes d⊑a' | no ¬h⊑a' = join d⊑h
εᶜ-Mac-dist lₐ d⊑a (join d⊑h) | no ¬h⊑a | no ¬d⊑a = ⊥-elim (¬d⊑a d⊑a)
εᶜ-Mac-dist lₐ d⊑a (joinEx {l = lᵈ} {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinEx {l = lᵈ} {h = lʰ} d⊑h) | yes h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinEx {l = lᵈ} {h = lʰ} d⊑h) | yes h⊑a | yes d⊑a' with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | yes h⊑a | yes d⊑a' | yes h⊑a' = joinEx d⊑h
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | yes h⊑a | yes d⊑a' | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | yes h⊑a | no ¬d⊑a = ⊥-elim (¬d⊑a d⊑a)
εᶜ-Mac-dist lₐ d⊑a (joinEx {l = lᵈ} {h = lʰ} d⊑h) | no ¬h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinEx {l = lᵈ} {h = lʰ} d⊑h) | no ¬h⊑a | yes d⊑a' with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | no ¬h⊑a | yes d⊑a' | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | no ¬h⊑a | yes d⊑a' | no ¬h⊑a' = joinEx d⊑h
εᶜ-Mac-dist lₐ d⊑a (joinEx d⊑h) | no ¬h⊑a | no ¬d⊑a = ⊥-elim (¬d⊑a d⊑a)
εᶜ-Mac-dist lₐ p Dist-∙ = Dist-∙
εᶜ-Mac-dist lₐ p Hole = Hole

εᶜ-Mac-∙-dist lₐ ¬p (AppL s) = Hole
εᶜ-Mac-∙-dist lₐ ¬p Beta = Hole
εᶜ-Mac-∙-dist lₐ ¬p Lookup = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p Dist-$ = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p Dist-If = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p (IfCond s) = Hole
εᶜ-Mac-∙-dist lₐ ¬p IfTrue = Hole
εᶜ-Mac-∙-dist lₐ ¬p IfFalse = Hole 
εᶜ-Mac-∙-dist lₐ ¬p Return = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p Dist->>= = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p (BindCtx s) = Hole
εᶜ-Mac-∙-dist lₐ ¬p Bind = Hole
εᶜ-Mac-∙-dist lₐ ¬p BindEx = Hole
εᶜ-Mac-∙-dist lₐ ¬p Throw = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p Dist-Catch = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p (CatchCtx s) = Hole
εᶜ-Mac-∙-dist lₐ ¬p Catch = Hole
εᶜ-Mac-∙-dist lₐ ¬p CatchEx = Hole
εᶜ-Mac-∙-dist lₐ ¬p (label p) = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p (Dist-unlabel p) = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p (unlabel p) = Hole
εᶜ-Mac-∙-dist lₐ ¬p (unlabelEx p) = Hole
εᶜ-Mac-∙-dist lₐ ¬p (unlabelCtx p s) = Hole
εᶜ-Mac-∙-dist lₐ h⊑a (Dist-join d⊑h) = Dist-∙
εᶜ-Mac-∙-dist lₐ h⊑a (joinCtx d⊑h s) = Hole
εᶜ-Mac-∙-dist lₐ h⊑a (join d⊑h) = Hole
εᶜ-Mac-∙-dist lₐ h⊑a (joinEx d⊑h) = Hole
εᶜ-Mac-∙-dist lₐ ¬p Dist-∙ = Dist-∙
εᶜ-Mac-∙-dist lₐ ¬p Hole = Hole

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ c₁ c₂ lₐ . if c₁ ⟼ c₂ then (εᶜ lₐ c₁) ⟼ (εᶜ lₐ c₂)
--------------------------------------------------------------------------------

εᶜ-dist {Mac lᵈ τ} lₐ s with lᵈ ⊑? lₐ
εᶜ-dist {Mac lᵈ τ} lₐ s | yes p = εᶜ-Mac-dist lₐ p s
εᶜ-dist {Mac lᵈ τ} lₐ s | no ¬p = εᶜ-Mac-∙-dist lₐ ¬p s
εᶜ-dist {Bool} lₐ (AppL s) = AppL (εᶜ-dist lₐ s)
εᶜ-dist {Bool} lₐ Beta = Beta
εᶜ-dist {Bool} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-dist {Bool} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist {Bool} lₐ Dist-If = Dist-If
εᶜ-dist {Bool} lₐ (IfCond s) = IfCond (εᶜ-dist lₐ s)
εᶜ-dist {Bool} lₐ IfTrue = IfTrue
εᶜ-dist {Bool} lₐ IfFalse = IfFalse
εᶜ-dist {Bool} lₐ Dist-∙ = Dist-∙
εᶜ-dist {Bool} lₐ Hole = Hole
εᶜ-dist {τ => τ₁} lₐ (AppL s) = AppL (εᶜ-dist lₐ s)
εᶜ-dist {τ => τ₁} lₐ Beta = Beta
εᶜ-dist {τ => τ₁} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-dist {τ => τ₁} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist {τ => τ₁} lₐ Dist-If = Dist-If
εᶜ-dist {τ => τ₁} lₐ (IfCond s) = IfCond (εᶜ-dist lₐ s)
εᶜ-dist {τ => τ₁} lₐ IfTrue = IfTrue
εᶜ-dist {τ => τ₁} lₐ IfFalse = IfFalse
εᶜ-dist {τ => τ₁} lₐ Dist-∙ = Dist-∙
εᶜ-dist {τ => τ₁} lₐ Hole = Hole
εᶜ-dist {Labeled lᵈ τ} lₐ s = εᶜ-Labeled-dist lₐ (lᵈ ⊑? lₐ) s
εᶜ-dist {Exception} lₐ (AppL s) = AppL (εᶜ-dist lₐ s)
εᶜ-dist {Exception} lₐ Beta = Beta
εᶜ-dist {Exception} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup {{lₐ}} x Γ = Lookup
εᶜ-dist {Exception} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist {Exception} lₐ Dist-If = Dist-If
εᶜ-dist {Exception} lₐ (IfCond s) = IfCond (εᶜ-dist lₐ s)
εᶜ-dist {Exception} lₐ IfTrue = IfTrue
εᶜ-dist {Exception} lₐ IfFalse = IfFalse
εᶜ-dist {Exception} lₐ Dist-∙ = Dist-∙
εᶜ-dist {Exception} lₐ Hole = Hole
