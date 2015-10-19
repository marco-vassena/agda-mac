module Security.NonInterference where

open import Security.Base
open import Proofs
open import Semantics
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
-- εᶜ-lookup : ∀ {{l}} {n} (Γ : Env n) (p : Fin n) -> lookup p (εᶜ-env l Γ) ≡ εᶜ l (lookup p Γ)
-- εᶜ-lookup [] ()
-- εᶜ-lookup (c ∷ Γ) zero = refl
-- εᶜ-lookup (c ∷ Γ) (suc p) rewrite εᶜ-lookup Γ p = refl

-- The erasure function distributes over the small step semantics
-- For simple proofs we do not need the Erasureᶜ.
εᶜ-distributes : ∀ {{l}} {c₁ c₂ : CTerm} -> (τ : Ty) -> c₁ ⟼ c₂ -> (x : c₁ :: τ) (y : c₂ :: τ) -> εᶜ l τ x ⟼ εᶜ l τ y 
εᶜ-distributes Bool s (Γ , t) y = {!!}
εᶜ-distributes Bool s (x₁ $ x₂) y = {!!}
εᶜ-distributes Bool (IfCond s) (If x Then x₁ Else x₂) (If y Then y₁ Else y₂) = {!IfCond ?!}
εᶜ-distributes Bool IfTrue (If Γ₁ , True Then x₁ Else x₂) y = {!IfTrue!}
εᶜ-distributes Bool IfFalse (If Γ₁ , False Then x₁ Else x₂) y = {!IfFalse!}
εᶜ-distributes Bool Hole' ∙ ∙ = Hole'
εᶜ-distributes (τ => τ₁) s x y = {!!}
εᶜ-distributes (Mac x τ) s x₁ y = {!!}
εᶜ-distributes (Labeled x τ) s x₁ y = {!!}
εᶜ-distributes Exception s x y = {!!} 

-- εᶜ-distributes (c₁ $ x) (c₂ $ .x) (AppL s) = AppL (εᶜ-distributes c₁ c₂ s)
-- εᶜ-distributes ._ ._ Beta = Beta
-- εᶜ-distributes (Γ , Var p) .(lookup p Γ) Lookup rewrite sym (εᶜ-lookup Γ p) = Lookup
-- εᶜ-distributes ._ ._ Dist-$ = Dist-$
-- εᶜ-distributes ._ ._ Dist-If = Dist-If
-- εᶜ-distributes ._ ._ (IfCond s) = IfCond (εᶜ-distributes _ _ s)
-- εᶜ-distributes ._ c₂ IfTrue = IfTrue
-- εᶜ-distributes ._ c₂ IfFalse = IfFalse
-- εᶜ-distributes ._ ._ Return = Return
-- εᶜ-distributes ._ ._ Dist->>= = Dist->>=
-- εᶜ-distributes ._ ._ (BindCtx s) = BindCtx (εᶜ-distributes _ _ s)
-- εᶜ-distributes ._ ._ Bind = Bind
-- εᶜ-distributes ._ ._ BindEx = BindEx
-- εᶜ-distributes ._ ._ Throw = Throw
-- εᶜ-distributes ._ ._ Dist-Catch = Dist-Catch
-- εᶜ-distributes ._ ._ (CatchCtx s) = CatchCtx (εᶜ-distributes _ _ s)
-- εᶜ-distributes ._ ._ Catch = Catch
-- εᶜ-distributes ._ ._ CatchEx = CatchEx
-- εᶜ-distributes {{l₁}} ._ ._ (label {h = l₂} p) with l₁ ⊑? l₂
-- εᶜ-distributes ._ ._ (label p) | yes _ = label p
-- εᶜ-distributes ._ ._ (label p) | no _ = label p
-- εᶜ-distributes ._ ._ Dist-unlabel = Dist-unlabel
-- εᶜ-distributes {{l₁}} (unlabel (Γ , Res .l₂ t)) (.Γ , Return .t) (unlabel {l = l₂}) with l₁ ⊑? l₂
-- εᶜ-distributes (unlabel (Γ , Res ._ t)) (.Γ , Return .t) unlabel | yes l₁⊑l₂ = unlabel
-- -- FIX Issue with proof
-- -- c₁ = unlabel (Γ , Res l₂ t)
-- -- c₂ = (Γ , Return t)
-- -- unlabel : c₁ ⟼ c₂
-- -- Since l₁ ⋢ l₂, t is erased from c₁, leading to c₁ₑ = unlabel (Γ , Res l₂ ∙)
-- -- For c₂ instead the erasure function is applied homorphically, c₂ₑ = (εᶜ-env l₁ Γ , Return (ε l₁ t)) 
-- -- Since ∙ is in general different from ε l t the rule unlabel does not apply.
-- -- My best guess is that the erasure function should be adjusted to perform the same check in Return x
-- -- After all if we type Return x : Mac H a we are marking sensitive data, isn'it ?
-- εᶜ-distributes (unlabel (Γ , Res ._ t)) (.Γ , Return .t) unlabel | no l₁⋢l₂ = {!unlabel !}
-- εᶜ-distributes ._ ._ (unlabelCtx s) = unlabelCtx (εᶜ-distributes _ _ s)
-- εᶜ-distributes ._ ._ Hole = Hole

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
