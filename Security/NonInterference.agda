module Security.NonInterference where

open import Typed.Semantics
open import Security.Base
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
εᶜ-lookup : ∀ {{l}} {τ Δ} (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ l (p !! Γ) ≡ p !! (εᶜ-env l Γ)
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

εᶜ-lookup-Mac : ∀ {l₁ l₂ τ Δ} {p : l₁ ⊑ l₂} -> (x : Mac l₂ τ ∈ Δ) (Γ : Env Δ) -> εᶜ-Mac l₁ p (x !! Γ) ≡ x !! εᶜ-env l₁ Γ
εᶜ-lookup-Mac {l₁} {l₂} Here (x ∷ Γ) with l₁ ⊑? l₂
εᶜ-lookup-Mac Here (x ∷ Γ) | yes p = refl
εᶜ-lookup-Mac {p = p} Here (x ∷ Γ) | no ¬p = ⊥-elim (¬p p)
εᶜ-lookup-Mac {p = p} (There x) (_ ∷ Γ) rewrite εᶜ-lookup-Mac {p = p} x Γ = refl  

εᶜ-lookup-Labeled : ∀ {l₁ l₂ τ Δ} {p : l₁ ⊑ l₂} -> (x : Labeled l₂ τ ∈ Δ) (Γ : Env Δ) -> εᶜ-Labeled l₁ p (x !! Γ) ≡ x !! εᶜ-env l₁ Γ
εᶜ-lookup-Labeled {l₁} {l₂} Here (x ∷ Γ) with l₁ ⊑? l₂
εᶜ-lookup-Labeled Here (x ∷ Γ) | yes p = refl
εᶜ-lookup-Labeled {p = p} Here (x ∷ Γ) | no ¬p = ⊥-elim (¬p p)
εᶜ-lookup-Labeled {p = p} (There x) (_ ∷ Γ) rewrite εᶜ-lookup-Labeled {p = p} x Γ = refl

εᶜ-distributes-Bool : {c₁ c₂ : CTerm Bool} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Bool l c₁ ⟼ εᶜ-Bool l c₂
εᶜ-distributes-Fun : ∀ {α β} {c₁ c₂ : CTerm (α => β)} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Fun l c₁ ⟼ εᶜ-Fun l c₂
εᶜ-distributes-Labeled : ∀ {l₂ τ} {c₁ c₂ : CTerm (Labeled l₂ τ)} -> 
                         (l₁ : Label) (p : l₁ ⊑ l₂) -> c₁ ⟼ c₂ -> εᶜ-Labeled l₁ p c₁ ⟼ εᶜ-Labeled l₁ p c₂
εᶜ-distributes-Exception : {c₁ c₂ : CTerm Exception} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Excpetion l c₁ ⟼ εᶜ-Excpetion l c₂

εᶜ-distributes-Closure : ∀ {τ Δ} (l : Label) (Γ : Env Δ) (t : Term Δ τ) -> εᶜ l (Γ , t) ≡  (εᶜ-env l Γ , ε l t) 
εᶜ-distributes-Closure {τ = Bool} l Γ t  = refl
εᶜ-distributes-Closure {τ = τ => τ₁} l Γ t  = refl
εᶜ-distributes-Closure {τ = Mac l₂ τ} l₁ Γ t  with l₁ ⊑? l₂
εᶜ-distributes-Closure {Mac l₂ τ} l₁ Γ t | yes p = refl
εᶜ-distributes-Closure {Mac l₂ τ} l₁ Γ t | no ¬p = {!!} -- This just does not hold
εᶜ-distributes-Closure {τ = Labeled l₂ τ} l₁ Γ t with l₁ ⊑? l₂
εᶜ-distributes-Closure {Labeled l₂ τ} l₁ Γ t | yes p = refl
εᶜ-distributes-Closure {Labeled l₂ τ} l₁ Γ t | no ¬p = {!!} -- This just does not hold
εᶜ-distributes-Closure {τ = Exception} l Γ t = refl
 
εᶜ-distributes-Bool l (AppL s) = AppL (εᶜ-distributes-Fun l s)
εᶜ-distributes-Bool l Beta = Beta
εᶜ-distributes-Bool {Γ , Var p} l Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes-Bool {Γ , App f x} l Dist-$ rewrite εᶜ-distributes-Closure l Γ x = Dist-$
εᶜ-distributes-Bool l Dist-If = Dist-If
εᶜ-distributes-Bool l (IfCond s) = IfCond (εᶜ-distributes-Bool l s)
εᶜ-distributes-Bool l IfTrue = IfTrue
εᶜ-distributes-Bool l IfFalse = IfFalse
εᶜ-distributes-Bool l Hole = Hole
εᶜ-distributes-Bool l Hole' = Hole'

εᶜ-distributes-Fun l (AppL s) = AppL (εᶜ-distributes-Fun l s)
εᶜ-distributes-Fun l Beta = Beta
εᶜ-distributes-Fun {c₁ = Γ , Var p} l Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes-Fun {c₁ = Γ , App f x} l Dist-$ rewrite εᶜ-distributes-Closure l Γ x = Dist-$
εᶜ-distributes-Fun l Dist-If = Dist-If
εᶜ-distributes-Fun l (IfCond s) = IfCond (εᶜ-distributes-Bool l s)
εᶜ-distributes-Fun l IfTrue = IfTrue
εᶜ-distributes-Fun l IfFalse = IfFalse
εᶜ-distributes-Fun l Hole = Hole
εᶜ-distributes-Fun l Hole' = Hole'

εᶜ-distributes-Mac : ∀ {l₂ τ} {c₁ c₂ : CTerm (Mac l₂ τ)} -> (l₁ : Label) (p : l₁ ⊑ l₂) -> c₁ ⟼ c₂ -> εᶜ-Mac l₁ p c₁ ⟼ εᶜ-Mac l₁ p c₂
εᶜ-distributes-Mac l₁ p (AppL s) = AppL (εᶜ-distributes-Fun l₁ s)
εᶜ-distributes-Mac {l₂} l₁ p Beta with l₁ ⊑? l₂
εᶜ-distributes-Mac l₁ p₁ Beta | yes p = Beta
εᶜ-distributes-Mac l₁ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes-Mac {c₁ = Γ , Var x} l₁ p Lookup rewrite εᶜ-lookup-Mac {p = p} x Γ = Lookup
εᶜ-distributes-Mac {c₁ = Γ , App f x} l₁ p Dist-$ rewrite εᶜ-distributes-Closure l₁ Γ x = Dist-$
εᶜ-distributes-Mac l₁ p Dist-If = Dist-If
εᶜ-distributes-Mac l₁ p (IfCond s) = IfCond (εᶜ-distributes-Bool l₁ s)
εᶜ-distributes-Mac l₁ p IfTrue = IfTrue
εᶜ-distributes-Mac l₁ p IfFalse = IfFalse
εᶜ-distributes-Mac l₁ p Return = Return
εᶜ-distributes-Mac l₁ p Dist->>= = Dist->>=
εᶜ-distributes-Mac l₁ p (BindCtx s) = BindCtx (εᶜ-distributes-Mac l₁ p s)
εᶜ-distributes-Mac {c₁ = (Γ , Mac t) >>= k } l₁ p Bind rewrite εᶜ-distributes-Closure l₁ Γ t = Bind
εᶜ-distributes-Mac l₁ p BindEx = BindEx
εᶜ-distributes-Mac l₁ p Throw = Throw
εᶜ-distributes-Mac l₁ p Dist-Catch = Dist-Catch
εᶜ-distributes-Mac l₁ p (CatchCtx s) = CatchCtx (εᶜ-distributes-Mac l₁ p s)
εᶜ-distributes-Mac l₁ p Catch = Catch
εᶜ-distributes-Mac l₁ p CatchEx = CatchEx
εᶜ-distributes-Mac l₁ p (label {h = l₃} l₂⊑l₃) with l₁ ⊑? l₃
εᶜ-distributes-Mac l₁ p₁ (label l₂⊑l₃) | yes p = label l₂⊑l₃
εᶜ-distributes-Mac l₁ p (label l₂⊑l₃) | no ¬p = {!label ?!} -- Fix erasure function
εᶜ-distributes-Mac l₁ p (Dist-unlabel {l = l₃}) with l₁ ⊑? l₃
εᶜ-distributes-Mac l₁ p₁ Dist-unlabel | yes p = Dist-unlabel
εᶜ-distributes-Mac l₁ p Dist-unlabel | no ¬p = {!Dist-unlabel!} -- Fix erasure function
εᶜ-distributes-Mac l₁ p (unlabel {l = l₃}) with l₁ ⊑? l₃
εᶜ-distributes-Mac l₁ p₁ unlabel | yes p = unlabel
εᶜ-distributes-Mac l₁ p unlabel | no ¬p = {!!} -- Fix erasure function
εᶜ-distributes-Mac l₁ p (unlabelCtx {l = l₃} s) with l₁ ⊑? l₃
εᶜ-distributes-Mac l₁ p₁ (unlabelCtx s) | yes p = unlabelCtx (εᶜ-distributes-Labeled l₁ p s)
εᶜ-distributes-Mac l₁ p (unlabelCtx s) | no ¬p = unlabelCtx Hole'
εᶜ-distributes-Mac l₁ p Hole = Hole
εᶜ-distributes-Mac l₁ p Hole' = Hole'

εᶜ-distributes-Labeled l₁ p (AppL s) = AppL (εᶜ-distributes-Fun l₁ s)
εᶜ-distributes-Labeled {l₂} l₁ p Beta with l₁ ⊑? l₂
εᶜ-distributes-Labeled l₁ p₁ Beta | yes p = Beta
εᶜ-distributes-Labeled l₁ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes-Labeled {c₁ = Γ , Var x} l₁ p Lookup rewrite εᶜ-lookup-Labeled {p = p} x Γ = Lookup
εᶜ-distributes-Labeled l₁ p Dist-$ = {!Dist-$!}
εᶜ-distributes-Labeled l₁ p Dist-If = Dist-If
εᶜ-distributes-Labeled l₁ p (IfCond s) = IfCond (εᶜ-distributes-Bool l₁ s)
εᶜ-distributes-Labeled l₁ p IfTrue = IfTrue
εᶜ-distributes-Labeled l₁ p IfFalse = IfFalse
εᶜ-distributes-Labeled l₁ p Hole = Hole
εᶜ-distributes-Labeled l₁ p Hole' = Hole'

εᶜ-distributes-Exception l (AppL s) = AppL (εᶜ-distributes-Fun l s)
εᶜ-distributes-Exception l Beta = Beta
εᶜ-distributes-Exception {Γ , Var p} l Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes-Exception {Γ , App f x} l Dist-$ rewrite εᶜ-distributes-Closure l Γ x = Dist-$
εᶜ-distributes-Exception l Dist-If = Dist-If
εᶜ-distributes-Exception l (IfCond s) = IfCond (εᶜ-distributes-Bool l s)
εᶜ-distributes-Exception l IfTrue = IfTrue
εᶜ-distributes-Exception l IfFalse = IfFalse
εᶜ-distributes-Exception l Hole = Hole
εᶜ-distributes-Exception l Hole' = Hole'


-- The erasure function distributes over the small step semantics
-- For simple proofs we do not need the Erasureᶜ.
εᶜ-distributes : ∀ {τ} {c₁ c₂ : CTerm τ} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ l c₁ ⟼ εᶜ l c₂
εᶜ-distributes {Bool} l s = εᶜ-distributes-Bool l s
εᶜ-distributes {τ => τ₁} l s = εᶜ-distributes-Fun l s
εᶜ-distributes {Mac l₂ τ} l₁ s with l₁ ⊑? l₂
εᶜ-distributes {Mac l₂ τ} l₁ s | yes p = εᶜ-distributes-Mac l₁ p s
εᶜ-distributes {Mac l₂ τ} l₁ s | no ¬p = Hole'
εᶜ-distributes {Labeled l₂ τ} l₁ s with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₂ τ} l₁ s | yes p = εᶜ-distributes-Labeled l₁ p s
εᶜ-distributes {Labeled l₂ τ} l₁ s | no ¬p = Hole'
εᶜ-distributes {Exception} l s = εᶜ-distributes-Exception l s

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
