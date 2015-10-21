module Security.NonInterference where

open import Typed.Semantics
open import Security.Base
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
εᶜ-lookup : ∀ {{l}} {τ Δ} (p : τ ∈ Δ) (Γ : Env Δ) -> p !! (εᶜ-env l Γ) ≡ εᶜ l (p !! Γ)
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

-- New rule Dist-∙ : (Γ , ∙) ⟼ ∙
-- *** However if we define εᶜ l (Γ , ∙) = ∙ 
-- This should avoid introducting a new rule 


-- The erasure function distributes over the small step semantics
-- For simple proofs we do not need the Erasureᶜ.
εᶜ-distributes : ∀ {τ} {{l}} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> εᶜ l c₁ ⟼ εᶜ l c₂ 
εᶜ-distributes {Bool} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {τ => τ₁} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} {{l₁}} (AppL s) with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} (AppL s) | yes p = AppL (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} (AppL s) | no ¬p = Hole'
εᶜ-distributes {Labeled l₂ τ} {{l₁}} (AppL s) with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} (AppL s) | yes p = AppL (εᶜ-distributes s)
εᶜ-distributes {Labeled l₂ τ} (AppL s) | no ¬p = Hole'
εᶜ-distributes {Exception} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {Bool} Beta = Beta
εᶜ-distributes {τ => τ₁} Beta = Beta
εᶜ-distributes {Mac l₂ τ} {{l₁}} Beta with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Beta | yes p = Beta
εᶜ-distributes {Mac l₂ τ} Beta | no ¬p = {!!} -- ε should first inspect the type?
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Beta with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Beta | yes p = Beta
εᶜ-distributes {Labeled l₂ τ} Beta | no ¬p = {!!} -- Idem
εᶜ-distributes {Exception} Beta = Beta
εᶜ-distributes {c₁ = Γ , Var p} Lookup rewrite sym (εᶜ-lookup p Γ) = Lookup
εᶜ-distributes {Bool} Dist-$ = Dist-$
εᶜ-distributes {τ => τ₁} Dist-$ = Dist-$
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-$ with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Dist-$ | yes p = Dist-$
εᶜ-distributes {Mac l₂ τ} Dist-$ | no ¬p = {!!} -- App needs to be fixed this case! Inspect type!
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Dist-$ with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Dist-$ | yes p = Dist-$
εᶜ-distributes {Labeled l₂ τ} Dist-$ | no ¬p = {!!} -- Idem
εᶜ-distributes {Exception} Dist-$ = Dist-$
εᶜ-distributes Dist-If = Dist-If
εᶜ-distributes (IfCond s) = IfCond (εᶜ-distributes s)
εᶜ-distributes IfTrue = IfTrue
εᶜ-distributes IfFalse = IfFalse
εᶜ-distributes {{l₁}} (Return {l₂}) with l₁ ⊑? l₂
εᶜ-distributes Return | yes p = Return
εᶜ-distributes Return | no ¬p = Hole
εᶜ-distributes {{l₁}} (Dist->>= {l₂}) with l₁ ⊑? l₂
εᶜ-distributes Dist->>= | yes p = Dist->>=
εᶜ-distributes Dist->>= | no ¬p = {!!} -- *** 
εᶜ-distributes {{l₁}} (BindCtx {l₂} s) with l₁ ⊑? l₂
εᶜ-distributes (BindCtx s) | yes p = BindCtx (εᶜ-distributes s)
εᶜ-distributes (BindCtx s) | no ¬p = Hole'
εᶜ-distributes {{l₁}} (Bind {l₂}) with l₁ ⊑? l₂
εᶜ-distributes {{l₁}} (Bind {l₂}) | yes p with l₁ ⊑? l₂ -- Agda limitation, results are not shared
εᶜ-distributes Bind | yes p₁ | yes p = Bind
εᶜ-distributes Bind | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes Bind | no ¬p = Hole'
εᶜ-distributes {{l₁}} (BindEx {l₂}) with l₁ ⊑? l₂
εᶜ-distributes {{l₁}} (BindEx {l₂}) | yes p with l₁ ⊑? l₂ -- Agda limitation
εᶜ-distributes BindEx | yes p₁ | yes p = BindEx
εᶜ-distributes BindEx | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes BindEx | no ¬p = {!!} -- ***
εᶜ-distributes {{l₁}} (Throw {l₂}) with l₁ ⊑? l₂
εᶜ-distributes Throw | yes p = Throw
εᶜ-distributes Throw | no ¬p = Hole
εᶜ-distributes {{l₁}} (Dist-Catch {l₂}) with l₁ ⊑? l₂
εᶜ-distributes Dist-Catch | yes p = Dist-Catch
εᶜ-distributes Dist-Catch | no ¬p = {!!} -- ***
εᶜ-distributes {{l₁}} (CatchCtx {l₂} s) with l₁ ⊑? l₂
εᶜ-distributes (CatchCtx s) | yes p = CatchCtx (εᶜ-distributes s)
εᶜ-distributes (CatchCtx s) | no ¬p = Hole'
εᶜ-distributes {{l₁}} (Catch {l₂}) with l₁ ⊑? l₂
εᶜ-distributes {{l₁}} (Catch {l₂}) | yes p with l₁ ⊑? l₂
εᶜ-distributes Catch | yes p₁ | yes p = Catch
εᶜ-distributes Catch | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes Catch | no ¬p = {!!} -- ***
εᶜ-distributes {{l₁}} (CatchEx {l₂}) with l₁ ⊑? l₂
εᶜ-distributes {{l₁}} (CatchEx {l₂}) | yes p with l₁ ⊑? l₂
εᶜ-distributes CatchEx | yes p₁ | yes p = CatchEx
εᶜ-distributes CatchEx | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes CatchEx | no ¬p = Hole'
εᶜ-distributes {{l₁}} (label {l₂} p) with l₁ ⊑? l₂
εᶜ-distributes {{l₁}} (label {h = l₃} p₁) | yes p with l₁ ⊑? l₃
εᶜ-distributes (label p₂) | yes p₁ | yes p = label p₂
εᶜ-distributes (label l₂⊑l₃) | yes l₁⊑l₂ | no ¬l₁⊑l₃ = ⊥-elim (¬l₁⊑l₃ (trans-⊑ l₁⊑l₂ l₂⊑l₃))
εᶜ-distributes (label p) | no ¬p = Hole
εᶜ-distributes {{l₁}} (Dist-unlabel {l₂}) with l₁ ⊑? l₂
εᶜ-distributes Dist-unlabel | yes p = Dist-unlabel
εᶜ-distributes Dist-unlabel | no ¬p = {!!} -- ***  
εᶜ-distributes {{l₁}} (unlabel {l = l₂} {h = l₃}) with l₁ ⊑? l₂ | l₁ ⊑? l₃
εᶜ-distributes {{l₁}} (unlabel {l = l₂} {h = l₃}) | yes p | yes p₁ with l₁ ⊑? l₂
εᶜ-distributes unlabel | yes p₁ | yes p₂ | yes p = unlabel
εᶜ-distributes unlabel | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes (unlabel {p = l₂⊑l₃}) | yes l₁⊑l₂ | no ¬l₁⊑l₃ = ⊥-elim (¬l₁⊑l₃ (trans-⊑ l₁⊑l₂ l₂⊑l₃))
εᶜ-distributes {{l₁}} (unlabel {l = l₂} {h = l₃}) | no ¬l₁⊑l₂ | yes l₁⊑l₃ = {!!} -- ??? Check erasure of unlabel 
εᶜ-distributes unlabel | no ¬p | no ¬p₁ = {!!} -- ***
εᶜ-distributes {{l₁}} (unlabelCtx {l₂} s) with l₁ ⊑? l₂
εᶜ-distributes (unlabelCtx s) | yes p = unlabelCtx (εᶜ-distributes s)
εᶜ-distributes (unlabelCtx s) | no ¬p = Hole'
εᶜ-distributes Hole = Hole
εᶜ-distributes Hole' = Hole'

-- Reduction of pure and monadic terms with erasure
-- data _⟼ˡ_ {{l : Label}} (c₁ c₂ₑ : CTerm) : Set where
--   Step-εᶜ : ∀ {c₂} -> εᶜ l c₂ ≡ c₂ₑ -> c₁ ⟼ c₂ -> c₁ ⟼ˡ c₂ₑ 

-- -- The small step + erasure relation is also deterministic
-- determinismˡ : ∀ {l c₁ c₂ c₃} -> c₁ ⟼ˡ c₂ -> c₁ ⟼ˡ c₃ -> c₂ ≡ c₃
-- determinismˡ (Step-εᶜ eq₁ s₁) (Step-εᶜ eq₂ s₂) with determinism s₁ s₂
-- determinismˡ (Step-εᶜ refl s₁) (Step-εᶜ refl s₂) | refl = refl

-- Single-step collapsed simulation
-- liftˡ : ∀ {{l}} {c₁ c₂} -> c₁ ⟼ c₂ -> εᶜ l c₁ ⟼ˡ εᶜ l c₂
-- liftˡ {{l}} {c₁} {c₂} s with εᶜ-distributes _ _ s
-- ... | r = Step-εᶜ {c₂ = εᶜ l c₂} (sym (εᶜ-idem c₂)) r

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
-- data _≈ˡ_ {{l : Label}} (c₁ c₂ : CTerm) : Set where
--   εᶜ-≡ : εᶜ l c₁ ≡ εᶜ l c₂ -> c₁ ≈ˡ c₂


-- Non-interference
-- non-interference : ∀ {l c₁ c₂ c₁' c₂'} -> c₁ ≈ˡ c₂ -> c₁ ⟼ c₁' -> c₂ ⟼ c₂' -> c₁' ≈ˡ c₂'
-- non-interference (εᶜ-≡ eq) s₁ s₂ = εᶜ-≡ (aux eq (liftˡ s₁) (liftˡ s₂))
--   where aux : ∀ {c₁ c₂ c₃ c₄} -> c₁ ≡ c₂ -> c₁ ⟼ˡ c₃ -> c₂ ⟼ˡ c₄ -> c₃ ≡ c₄
--         aux refl s₁ s₂ = determinismˡ s₁ s₂
