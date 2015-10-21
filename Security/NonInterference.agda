module Security.NonInterference where

open import Typed.Semantics
open import Security.Base
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
εᶜ-lookup : ∀ {{l}} {τ Δ} (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ l (p !! Γ) ≡ p !! (εᶜ-env l Γ)
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

-- The erasure function distributes over the small step semantics
-- For simple proofs we do not need the Erasureᶜ.
εᶜ-distributes : ∀ {τ} {{l}} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> εᶜ l c₁ ⟼ εᶜ l c₂
εᶜ-distributes {Bool} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {Bool} Beta = Beta
εᶜ-distributes {Bool} {c₁ = Γ , Var p} Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes {Bool} Dist-$ = {!Dist-$!} -- I think here we should inspect the argument type to make any progress
εᶜ-distributes {Bool} Dist-If = Dist-If
εᶜ-distributes {Bool} (IfCond s) = IfCond (εᶜ-distributes s)
εᶜ-distributes {Bool} IfTrue = IfTrue
εᶜ-distributes {Bool} IfFalse = IfFalse
εᶜ-distributes {Bool} Hole = Hole
εᶜ-distributes {Bool} Hole' = Hole'
εᶜ-distributes {τ => τ₁} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {τ => τ₁} Beta = Beta
εᶜ-distributes {τ => τ₁} {c₁ = Γ , Var p} Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes {τ => τ₁} Dist-$ = {!Dist-$!}
εᶜ-distributes {τ => τ₁} Dist-If = Dist-If
εᶜ-distributes {τ => τ₁} (IfCond s) = IfCond (εᶜ-distributes s)
εᶜ-distributes {τ => τ₁} IfTrue = IfTrue
εᶜ-distributes {τ => τ₁} IfFalse = IfFalse
εᶜ-distributes {τ => τ₁} Hole = Hole
εᶜ-distributes {τ => τ₁} Hole' = Hole'
εᶜ-distributes {Mac l₂ τ} {{l₁}} s with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} (AppL s) | yes p = AppL (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} Beta | yes p = Beta
εᶜ-distributes {Mac l₂ τ} {{l₁}} {c₁ = Γ , Var p} Lookup | yes x = {!!} -- rewrite εᶜ-lookup {{l₁}} p Γ = {!Lookup!}
εᶜ-distributes {Mac l₂ τ} Dist-$ | yes p = {!!} 
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-If | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-If | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Dist-If | yes p₂ | yes p₁ | yes p = Dist-If
εᶜ-distributes {Mac l₂ τ} Dist-If | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} Dist-If | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} (IfCond s) | yes p = IfCond (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} {{l₁}} IfTrue | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} IfTrue | yes p₁ | yes p = {!!} -- Needs extensivity
εᶜ-distributes {Mac l₂ τ} IfTrue | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} IfFalse | yes p = {!IfFalse!} -- Needs extensivity
εᶜ-distributes {Mac l₂ τ} {{l₁}} Return | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Return | yes p₁ | yes p = Return
εᶜ-distributes {Mac l₂ τ} Return | yes p | no ¬p = Hole
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist->>= | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Dist->>= | yes p₁ | yes p = Dist->>=
εᶜ-distributes {Mac l₂ τ} Dist->>= | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₁ τ} (BindCtx s) | yes p = BindCtx (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Bind | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} Bind | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Bind | yes p₂ | yes p₁ | yes p = {!Bind!}
εᶜ-distributes {Mac l₂ τ} Bind | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} Bind | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} BindEx | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} BindEx | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} BindEx | yes p₂ | yes p₁ | yes p = BindEx
εᶜ-distributes {Mac l₂ τ} BindEx | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} BindEx | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Throw | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Throw | yes p₁ | yes p = Throw
εᶜ-distributes {Mac l₂ τ} Throw | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-Catch | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-Catch | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Dist-Catch | yes p₂ | yes p₁ | yes p = Dist-Catch
εᶜ-distributes {Mac l₂ τ} Dist-Catch | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} Dist-Catch | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₁ τ} (CatchCtx s) | yes p = CatchCtx (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Catch | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} Catch | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Catch | yes p₂ | yes p₁ | yes p = Catch
εᶜ-distributes {Mac l₂ τ} Catch | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} Catch | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} CatchEx | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} CatchEx | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} CatchEx | yes p₂ | yes p₁ | yes p = CatchEx
εᶜ-distributes {Mac l₂ τ} CatchEx | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Mac l₂ τ} CatchEx | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ ._} {{l₁}} (label p₁) | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ ._} {{l₁}} (label {h = l₃} l₂⊑l₃) | yes p₁ | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ ._} (label l₂⊑l₃) | yes p₂ | yes p₁ | yes p = label l₂⊑l₃
εᶜ-distributes {Mac l₂ ._} (label l₂⊑l₃) | yes p₁ | yes p | no ¬p = {!!} -- Fix εᶜ definition for label
εᶜ-distributes {Mac l₂ ._} (label p₁) | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Dist-unlabel | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} (Dist-unlabel {l = l₃}) | yes p₁ | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ τ} {{l₁}} (Dist-unlabel {l = l₃}) | yes p₂ | yes p₁ | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ τ} Dist-unlabel | yes p₃ | yes p₂ | yes p₁ | yes p = {!Dist-unlabel!} -- Extensivity
εᶜ-distributes {Mac l₂ τ} Dist-unlabel | yes p₂ | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} Dist-unlabel | yes p₁ | yes p | no ¬p = {!Dist-unlabel!} -- ???
εᶜ-distributes {Mac l₂ τ} Dist-unlabel | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} {{l₁}} unlabel | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} {{l₁}} (unlabel {l = l₃}) | yes p₁ | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ τ} {{l₁}} (unlabel {l = l₃}) | yes p₂ | yes p₁ | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ τ} unlabel | yes p₃ | yes p₂ | yes p₁ | yes p = unlabel
εᶜ-distributes {Mac l₂ τ} unlabel | yes p₂ | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} unlabel | yes p₁ | yes p | no ¬p = {!!} -- ???
εᶜ-distributes {Mac l₂ τ} {{l₁}} (unlabel {l = l₃}) | yes p | no ¬p with l₁ ⊑? l₃ 
εᶜ-distributes {Mac l₂ τ} {{l₁}} (unlabel {l = l₃}) | yes p₁ | no ¬p | yes p with l₁ ⊑? l₃
εᶜ-distributes {Mac l₂ τ} unlabel | yes p₂ | no ¬p | yes p₁ | yes p = ⊥-elim (¬p p₂)
εᶜ-distributes {Mac l₂ τ} unlabel | yes p₁ | no ¬p₁ | yes p | no ¬p = ⊥-elim (¬p₁ p₁)
εᶜ-distributes {Mac l₂ τ} unlabel | yes p | no ¬p₁ | no ¬p = ⊥-elim (¬p₁ p)
εᶜ-distributes {Mac l₂ ._} (unlabelCtx s) | yes p = unlabelCtx (εᶜ-distributes s)
εᶜ-distributes {Mac l₂ τ} {{l₁}} Hole | yes p with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} Hole | yes p₁ | yes p = Hole
εᶜ-distributes {Mac l₂ τ} Hole | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac l₂ τ} Hole' | yes p = Hole'
εᶜ-distributes {Mac l₂ τ} s | no ¬p = Hole'
εᶜ-distributes {Labeled l₂ τ} {{l₁}} s with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} (AppL s) | yes p = AppL (εᶜ-distributes s)
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Beta | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Beta | yes p₁ | yes p = Beta
εᶜ-distributes {Labeled l₂ τ} Beta | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Lookup | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Lookup | yes p₁ | yes p = {!Lookup!}
εᶜ-distributes {Labeled l₂ τ} Lookup | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Labeled l₂ τ} Dist-$ | yes p = {!!}
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Dist-If | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Dist-If | yes p₁ | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Dist-If | yes p₂ | yes p₁ | yes p = Dist-If
εᶜ-distributes {Labeled l₂ τ} Dist-If | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᶜ-distributes {Labeled l₂ τ} Dist-If | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Labeled l₂ τ} (IfCond s) | yes p = IfCond (εᶜ-distributes s)
εᶜ-distributes {Labeled l₂ τ} {{l₁}} IfTrue | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} IfTrue | yes p₁ | yes p = {!IfTrue!} -- Extensivity
εᶜ-distributes {Labeled l₂ τ} IfTrue | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Labeled l₂ τ} IfFalse | yes p = {!!} -- Idem
εᶜ-distributes {Labeled l₂ τ} {{l₁}} Hole | yes p with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} Hole | yes p₁ | yes p = Hole
εᶜ-distributes {Labeled l₂ τ} Hole | yes p | no ¬p = Hole
εᶜ-distributes {Labeled l₂ τ} Hole' | yes p = Hole'
εᶜ-distributes {Labeled l₂ τ} s | no ¬p = Hole'
εᶜ-distributes {Exception} (AppL s) = AppL (εᶜ-distributes s)
εᶜ-distributes {Exception} Beta = Beta
εᶜ-distributes {Exception} {c₁ = Γ , Var p} Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes {Exception} Dist-$ = {!!}
εᶜ-distributes {Exception} Dist-If = Dist-If
εᶜ-distributes {Exception} (IfCond s) = IfCond (εᶜ-distributes s)
εᶜ-distributes {Exception} IfTrue = IfTrue
εᶜ-distributes {Exception} IfFalse = IfFalse
εᶜ-distributes {Exception} Hole = Hole
εᶜ-distributes {Exception} Hole' = Hole'

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
