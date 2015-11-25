module Security.Distributivity where

open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality 

-- The closed term erasure function distributes over the small step semantics.
εᶜ-dist : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⟼ c₂ -> εᶜ lₐ c₁ ⟼ εᶜ lₐ c₂

εᶜ-dist⇝ : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⇝ c₂ -> εᶜ lₐ c₁ ⇝ εᶜ lₐ c₂

--------------------------------------------------------------------------------
-- Auxliary distributivity lemmas for Mac closed terms
--------------------------------------------------------------------------------

εᶜ-Mac-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : Dec (lᵈ ⊑ lₐ)) (Γ : Env Δ) (x : Mac lᵈ τ ∈ Δ)
                -> εᶜ-Mac lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Mac-lookup {lᵈ} {lₐ = lₐ} p (c ∷ Γ) Here rewrite εᶜ-Mac-extensional p (lᵈ ⊑? lₐ) c = refl
εᶜ-Mac-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Mac-lookup p Γ x = refl

εᶜ-Mac-Labeled∙-dist⇝ : ∀ {lₐ lʰ τ} {c₁ c₂ : CTerm (Mac lʰ τ)} ->
                        c₁ ⇝ c₂ -> εᶜ-Mac-Labeled∙ lₐ c₁ ⇝ εᶜ-Mac-Labeled∙ lₐ c₂
εᶜ-Mac-Labeled∙-dist⇝ (AppL s) = Hole
εᶜ-Mac-Labeled∙-dist⇝ Beta = Hole
εᶜ-Mac-Labeled∙-dist⇝ Lookup = Dist-∙
εᶜ-Mac-Labeled∙-dist⇝ Dist-$ = Dist-∙
εᶜ-Mac-Labeled∙-dist⇝ Dist-If = Dist-∙
εᶜ-Mac-Labeled∙-dist⇝ (IfCond s) = Hole
εᶜ-Mac-Labeled∙-dist⇝ IfTrue = Hole
εᶜ-Mac-Labeled∙-dist⇝ IfFalse = Hole
εᶜ-Mac-Labeled∙-dist⇝ Dist-∙ = Dist-∙
εᶜ-Mac-Labeled∙-dist⇝ Hole = Hole

εᶜ-Mac-Labeled∙-dist : ∀ {lₐ lʰ τ} {c₁ c₂ : CTerm (Mac lʰ τ)} ->
                      c₁ ⟼ c₂ -> εᶜ-Mac-Labeled∙ lₐ c₁ ⟼ εᶜ-Mac-Labeled∙ lₐ c₂
εᶜ-Mac-Labeled∙-dist (Pure s) = Pure (εᶜ-Mac-Labeled∙-dist⇝ s)
εᶜ-Mac-Labeled∙-dist Return = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist Dist->>= = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist (BindCtx s) = Pure Hole
εᶜ-Mac-Labeled∙-dist Bind = Pure Hole
εᶜ-Mac-Labeled∙-dist BindEx = Pure Hole
εᶜ-Mac-Labeled∙-dist Throw = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist Dist-Catch = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist (CatchCtx s) = Pure Hole
εᶜ-Mac-Labeled∙-dist Catch = Pure Hole
εᶜ-Mac-Labeled∙-dist CatchEx = Pure Hole
εᶜ-Mac-Labeled∙-dist (label p) = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist (Dist-unlabel p) = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist (unlabel p) = Pure Hole
εᶜ-Mac-Labeled∙-dist (unlabelEx p) = Pure Hole
εᶜ-Mac-Labeled∙-dist (unlabelCtx p s) = Pure Hole
εᶜ-Mac-Labeled∙-dist (Dist-join p) = Pure Dist-∙
εᶜ-Mac-Labeled∙-dist (joinCtx p s) = Pure Hole
εᶜ-Mac-Labeled∙-dist (join p) = Pure Hole
εᶜ-Mac-Labeled∙-dist (joinEx p) = Pure Hole

-- Unfortuantely this is not useful because Agda refuses to rewrite the goal accordingly
-- claiming that the type signature of the auxiliary function is ill-typed.
-- εᶜ-Mac-Var : ∀ {lₐ lᵈ τ} {{Δ}} -> lᵈ ⊑ lₐ -> (x : Dec (lᵈ ⊑ lₐ))-> Var (Here {Δ} {Mac lᵈ τ}) ≡ ε-Mac lₐ x (Var Here)
-- εᶜ-Mac-Var p (yes p₁) = refl
-- εᶜ-Mac-Var p (no ¬p) = ⊥-elim (¬p p)

εᶜ-Mac-dist⇝ : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) -> (p : Dec (lᵈ ⊑ lₐ)) ->
                 c₁ ⇝ c₂ -> εᶜ-Mac lₐ p c₁ ⇝ εᶜ-Mac lₐ p c₂
εᶜ-Mac-dist⇝ lₐ (yes p) (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) Beta with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) Beta | yes p = Beta
εᶜ-Mac-dist⇝ lₐ (yes p) Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) (Lookup {Γ = Γ} {p = x}) rewrite εᶜ-Mac-lookup (lᵈ ⊑? lₐ) Γ x with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₂) Lookup | yes p = Lookup
εᶜ-Mac-dist⇝ lₐ (yes p₁) Lookup | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist⇝ lₐ (yes p) (Dist-$ {x = x}) rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-Mac-dist⇝ lₐ (yes p) Dist-If = Dist-If
εᶜ-Mac-dist⇝ lₐ (yes p) (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) IfTrue with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) (IfTrue {t = t}) | yes p rewrite εᶜ-Mac-extensional (yes p) (yes p₁) t = IfTrue
εᶜ-Mac-dist⇝ lₐ (yes p) IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) IfFalse with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) (IfFalse {e = e}) | yes p rewrite εᶜ-Mac-extensional (yes p) (yes p₁) e = IfFalse
εᶜ-Mac-dist⇝ lₐ (yes p) IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ lₐ (yes p) Dist-∙ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (yes p) Hole = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) (AppL s) =  Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Beta = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Lookup = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-$ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-If = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) (IfCond s) = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) IfTrue = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) IfFalse = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-∙ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Hole = Hole

εᶜ-Mac-dist : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) (p : Dec (lᵈ ⊑ lₐ)) -> 
                       c₁ ⟼ c₂ -> (εᶜ-Mac lₐ p c₁) ⟼ (εᶜ-Mac lₐ p c₂)
εᶜ-Mac-dist lₐ p (Pure s) = Pure (εᶜ-Mac-dist⇝ lₐ p s)
εᶜ-Mac-dist {lᵈ} lₐ (yes p) Return with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) Return | yes p = Return
εᶜ-Mac-dist lₐ (yes p) Return | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) Dist->>= = Dist->>=
εᶜ-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx (εᶜ-Mac-dist lₐ (yes p) s)
εᶜ-Mac-dist lₐ (yes p) (Bind {t = t}) rewrite εᶜ-Closure t lₐ = Bind
εᶜ-Mac-dist {lᵈ} lₐ (yes p) (BindEx {e = e}) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) BindEx | yes p = BindEx
εᶜ-Mac-dist lₐ (yes p) BindEx | no ¬p = ⊥-elim (¬p p) 
εᶜ-Mac-dist {lᵈ} lₐ (yes p) Throw with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) Throw | yes p = Throw
εᶜ-Mac-dist lₐ (yes p) Throw | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) Dist-Catch = Dist-Catch
εᶜ-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (εᶜ-Mac-dist lₐ (yes p) s)
εᶜ-Mac-dist {lᵈ} lₐ (yes p) Catch with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) Catch | yes p = Catch
εᶜ-Mac-dist lₐ (yes p) Catch | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) CatchEx = CatchEx
εᶜ-Mac-dist lₐ (yes p) (label {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist {lᵈ} lₐ (yes p₁) (label d⊑h) | yes h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (label {h = lʰ} d⊑h) | yes h⊑a | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (label d⊑h) | yes h⊑a | yes p₁ | yes p = label d⊑h
εᶜ-Mac-dist lₐ (yes p₁) (label d⊑h) | yes h⊑a | yes p | no ¬p = ⊥-elim (¬p h⊑a)
εᶜ-Mac-dist lₐ (yes p₁) (label d⊑h) | yes h⊑a | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist {lᵈ} lₐ (yes p) (label d⊑h) | no ¬h⊑a with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (label {h = lʰ} d⊑h) | no ¬h⊑a | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (label d⊑h) | no ¬h⊑a | yes p₁ | yes p = ⊥-elim (¬h⊑a p)
εᶜ-Mac-dist lₐ (yes p₁) (label d⊑h) | no ¬h⊑a | yes p | no ¬p = label d⊑h
εᶜ-Mac-dist lₐ (yes p) (label d⊑h) | no ¬h⊑a | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) = Dist-unlabel d⊑h
εᶜ-Mac-dist lₐ (yes p) (unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (unlabel {h = lʰ} d⊑h) | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (unlabel d⊑h) | yes p₁ | yes p = unlabel d⊑h
εᶜ-Mac-dist lₐ (yes p₁) (unlabel d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist lₐ (yes p) (unlabel {h = lʰ} d⊑h) | no ¬p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (unlabel d⊑h) | no ¬d⊑a | yes h⊑a = ⊥-elim (¬d⊑a (trans-⊑ d⊑h h⊑a))
εᶜ-Mac-dist lₐ (yes p) (unlabel d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) (unlabelEx {l = lᵈ} d⊑h) with lᵈ ⊑? lₐ
εᶜ-Mac-dist {lʰ} lₐ (yes p₁) (unlabelEx d⊑h) | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (unlabelEx d⊑h) | yes p₁ | yes p = unlabelEx d⊑h
εᶜ-Mac-dist lₐ (yes p₁) (unlabelEx d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist {lʰ} lₐ (yes p) (unlabelEx d⊑h) | no ¬p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (unlabelEx d⊑h) | no ¬p | yes h⊑a = ⊥-elim (¬p (trans-⊑ d⊑h p₁))
εᶜ-Mac-dist lₐ (yes p) (unlabelEx d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) (unlabelCtx d⊑h s) = unlabelCtx d⊑h (εᶜ-dist lₐ s)
εᶜ-Mac-dist lₐ (yes p) (Dist-join {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (Dist-join d⊑h) | yes p = Dist-join d⊑h
εᶜ-Mac-dist lₐ (yes p) (Dist-join d⊑h) | no ¬p = Dist-join d⊑h
εᶜ-Mac-dist lₐ (yes p) (joinCtx {h = lʰ} d⊑h s) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (joinCtx d⊑h s) | yes p = joinCtx d⊑h (εᶜ-Mac-dist lₐ (yes p) s)
εᶜ-Mac-dist lₐ (yes p) (joinCtx d⊑h s) | no ¬p = joinCtx d⊑h (εᶜ-Mac-Labeled∙-dist s)
εᶜ-Mac-dist lₐ (yes p) (join {l = lᵈ} {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (join {l = lᵈ} d⊑h) | yes p with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (join {h = lʰ} d⊑h) | yes p₁ | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₃) (join d⊑h) | yes p₂ | yes p₁ | yes p = join d⊑h
εᶜ-Mac-dist lₐ (yes p₂) (join d⊑h) | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist lₐ (yes p₁) (join d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist lₐ (yes p) (join {l = lᵈ} {h = lʰ} d⊑h) | no ¬p with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (join {h = lʰ} d⊑h) | no ¬p | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (join d⊑h) | no ¬p | yes p₁ | yes p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p₁) (join d⊑h) | no ¬p₁ | yes p | no ¬p = join d⊑h
εᶜ-Mac-dist lₐ (yes p) (join d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p) (joinEx {l = lᵈ} {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (joinEx {l = lᵈ} d⊑h) | yes p with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (joinEx {h = lʰ} d⊑h) | yes p₁ | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₃) (joinEx d⊑h) | yes p₂ | yes p₁ | yes p = joinEx d⊑h
εᶜ-Mac-dist lₐ (yes p₂) (joinEx d⊑h) | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist lₐ (yes p₁) (joinEx d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist lₐ (yes p) (joinEx {l = lᵈ} d⊑h) | no ¬p with lᵈ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₁) (joinEx {h = lʰ} d⊑h) | no ¬p | yes p with lʰ ⊑? lₐ
εᶜ-Mac-dist lₐ (yes p₂) (joinEx d⊑h) | no ¬p | yes p₁ | yes p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (yes p₁) (joinEx d⊑h) | no ¬p₁ | yes p | no ¬p = joinEx d⊑h
εᶜ-Mac-dist lₐ (yes p) (joinEx d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist lₐ (no ¬p) Return = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) Dist->>= = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) (BindCtx s) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) Bind = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) BindEx = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) Throw = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) Dist-Catch = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) (CatchCtx s) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) Catch = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) CatchEx = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (label p) = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) (Dist-unlabel p) = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) (unlabel p) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (unlabelEx p) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (unlabelCtx p s) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (Dist-join p) = Pure Dist-∙
εᶜ-Mac-dist lₐ (no ¬p) (joinCtx p s) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (join p) = Pure Hole
εᶜ-Mac-dist lₐ (no ¬p) (joinEx p) = Pure Hole

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ c₁ c₂ lₐ . if c₁ ⟼ c₂ then (εᶜ lₐ c₁) ⟼ (εᶜ lₐ c₂)
--------------------------------------------------------------------------------

-- This proof is repetitive because, even though the erasure
-- function is defined with a default case for all non Mac lᵈ τ types
-- reasoning requires to explicitly pattern match on each of them.
εᶜ-dist⇝ {Mac lᵈ τ} lₐ s = εᶜ-Mac-dist⇝ lₐ (lᵈ ⊑? lₐ) s
εᶜ-dist⇝ {（）} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {（）} lₐ Beta = Beta
εᶜ-dist⇝ {（）} lₐ (Lookup {Γ = Γ} {p = x}) rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {（）} lₐ (Dist-$ {Γ = Γ} {x = x}) rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {（）} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {（）} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {（）} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {（）} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {（）} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {（）} lₐ Hole = Hole
εᶜ-dist⇝ {Bool} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Bool} lₐ Beta = Beta
εᶜ-dist⇝ {Bool} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Bool} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Bool} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Bool} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Bool} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Bool} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Bool} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Bool} lₐ Hole = Hole
εᶜ-dist⇝ {τ => τ₁} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {τ => τ₁} lₐ Beta = Beta
εᶜ-dist⇝ {τ => τ₁} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {τ => τ₁} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {τ => τ₁} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {τ => τ₁} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {τ => τ₁} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {τ => τ₁} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {τ => τ₁} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {τ => τ₁} lₐ Hole = Hole
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Beta = Beta
εᶜ-dist⇝ {Labeled lᵈ τ} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Labeled lᵈ τ} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Hole = Hole
εᶜ-dist⇝ {Exception} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Exception} lₐ Beta = Beta
εᶜ-dist⇝ {Exception} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Exception} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Exception} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Exception} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Exception} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Exception} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Exception} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Exception} lₐ Hole = Hole

εᶜ-dist {（）} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᶜ-dist {Bool} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᶜ-dist {τ => τ₁} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᶜ-dist {Mac l τ} lₐ s = εᶜ-Mac-dist lₐ (l ⊑? lₐ) s
εᶜ-dist {Labeled l τ} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᶜ-dist {Exception} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s) 
