module Security.NonInterference where

open import Typed.Semantics
open import Typed.Proofs
open import Security.Base
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
εᶜ-lookup : ∀ {{l}} {τ Δ} (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ l (p !! Γ) ≡ p !! (εᶜ-env l Γ)
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

εᶜ-lookup-Mac : ∀ {l₁ l₂ τ Δ} {p : l₁ ⊑ l₂} -> (x : Mac l₁ τ ∈ Δ) (Γ : Env Δ) -> εᶜ-Mac l₂ p (x !! Γ) ≡ x !! εᶜ-env l₂ Γ
εᶜ-lookup-Mac {l₁} {l₂} Here (x ∷ Γ) with l₁ ⊑? l₂
εᶜ-lookup-Mac Here (x ∷ Γ) | yes p = refl
εᶜ-lookup-Mac {p = p} Here (x ∷ Γ) | no ¬p = ⊥-elim (¬p p)
εᶜ-lookup-Mac {p = p} (There x) (_ ∷ Γ) rewrite εᶜ-lookup-Mac {p = p} x Γ = refl  

εᶜ-lookup-Labeled : ∀ {l₁ l₂ τ Δ} {p : l₁ ⊑ l₂} -> (x : Labeled l₁ τ ∈ Δ) (Γ : Env Δ) -> εᶜ-Labeled l₂ p (x !! Γ) ≡ x !! εᶜ-env l₂ Γ
εᶜ-lookup-Labeled {l₁} {l₂} Here (x ∷ Γ) with l₁ ⊑? l₂
εᶜ-lookup-Labeled Here (x ∷ Γ) | yes p = refl
εᶜ-lookup-Labeled {p = p} Here (x ∷ Γ) | no ¬p = ⊥-elim (¬p p)
εᶜ-lookup-Labeled {p = p} (There x) (_ ∷ Γ) rewrite εᶜ-lookup-Labeled {p = p} x Γ = refl

εᶜ-distributes-Bool : {c₁ c₂ : CTerm Bool} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Bool l c₁ ⟼ εᶜ-Bool l c₂
εᶜ-distributes-Fun : ∀ {α β} {c₁ c₂ : CTerm (α => β)} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Fun l c₁ ⟼ εᶜ-Fun l c₂
εᶜ-distributes-Labeled : ∀ {l₁ τ} {c₁ c₂ : CTerm (Labeled l₁ τ)} -> 
                         (l₂ : Label) (p : l₁ ⊑ l₂) -> c₁ ⟼ c₂ -> εᶜ-Labeled l₂ p c₁ ⟼ εᶜ-Labeled l₂ p c₂
εᶜ-distributes-Exception : {c₁ c₂ : CTerm Exception} -> (l : Label) -> c₁ ⟼ c₂ -> εᶜ-Excpetion l c₁ ⟼ εᶜ-Excpetion l c₂

εᶜ-distributes-Closure : ∀ {τ Δ} (l : Label) (Γ : Env Δ) (t : Term Δ τ) -> εᶜ l (Γ , t) ≡  (εᶜ-env l Γ , ε l t) 
εᶜ-distributes-Closure {τ = Bool} l Γ t  = refl
εᶜ-distributes-Closure {τ = τ => τ₁} l Γ t  = refl
εᶜ-distributes-Closure {τ = Mac l₁ τ} l₂ Γ t  with l₁ ⊑? l₂
εᶜ-distributes-Closure {Mac l₂ τ} l₁ Γ t | yes p = refl
εᶜ-distributes-Closure {Mac l₂ τ} l₁ Γ t | no ¬p = {!!} -- This just does not hold
εᶜ-distributes-Closure {τ = Labeled l₁ τ} l₂ Γ t with l₁ ⊑? l₂
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

εᶜ-distributes-Mac : ∀ {l₁ τ} {c₁ c₂ : CTerm (Mac l₁ τ)} -> (l₂ : Label) (p : l₁ ⊑ l₂) -> c₁ ⟼ c₂ -> εᶜ-Mac l₂ p c₁ ⟼ εᶜ-Mac l₂ p c₂
εᶜ-distributes-Mac l₂ p (AppL s) = AppL (εᶜ-distributes-Fun l₂ s)
εᶜ-distributes-Mac {l₁} l₂ p Beta with l₁ ⊑? l₂
εᶜ-distributes-Mac l₂ p₁ Beta | yes p = Beta
εᶜ-distributes-Mac l₂ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes-Mac {c₁ = Γ , Var x} l₂ p Lookup rewrite εᶜ-lookup-Mac {p = p} x Γ = Lookup
εᶜ-distributes-Mac {c₁ = Γ , App f x} l₂ p Dist-$ rewrite εᶜ-distributes-Closure l₂ Γ x = Dist-$
εᶜ-distributes-Mac l₂ p Dist-If = Dist-If
εᶜ-distributes-Mac l₂ p (IfCond s) = IfCond (εᶜ-distributes-Bool l₂ s)
εᶜ-distributes-Mac l₂ p IfTrue = IfTrue
εᶜ-distributes-Mac l₂ p IfFalse = IfFalse
εᶜ-distributes-Mac l₂ p Return = Return
εᶜ-distributes-Mac l₂ p Dist->>= = Dist->>=
εᶜ-distributes-Mac l₂ p (BindCtx s) = BindCtx (εᶜ-distributes-Mac l₂ p s)
εᶜ-distributes-Mac {c₁ = (Γ , Mac t) >>= k } l₂ p Bind rewrite εᶜ-distributes-Closure l₂ Γ t = Bind
εᶜ-distributes-Mac l₂ p BindEx = BindEx
εᶜ-distributes-Mac l₂ p Throw = Throw
εᶜ-distributes-Mac l₂ p Dist-Catch = Dist-Catch
εᶜ-distributes-Mac l₂ p (CatchCtx s) = CatchCtx (εᶜ-distributes-Mac l₂ p s)
εᶜ-distributes-Mac l₂ p Catch = Catch
εᶜ-distributes-Mac l₂ p CatchEx = CatchEx
εᶜ-distributes-Mac l₂ l₁⊑l₂ (label {l = l₁} {h = l₃} l₁⊑l₃) with l₃ ⊑? l₂
εᶜ-distributes-Mac l₂ l₁⊑l₂ (label l₁⊑l₃) | yes l₃⊑l₂ = label l₁⊑l₃
εᶜ-distributes-Mac l₂ l₁⊑l₂ (label {l = l₁} {h = l₃} l₁⊑l₃) | no ¬l₃⊑l₂ = {!label l₁⊑l₃!}
εᶜ-distributes-Mac l₂ l₃⊑l₂ (Dist-unlabel {l = l₁} {h = l₃} l₁⊑l₃) with l₁ ⊑? l₂
εᶜ-distributes-Mac l₂ l₃⊑l₂ (Dist-unlabel l₁⊑l₃) | yes l₁⊑l₂ = Dist-unlabel l₁⊑l₃
εᶜ-distributes-Mac l₂ l₃⊑l₂ (Dist-unlabel l₁⊑l₃) | no ¬l₁⊑l₂ = ⊥-elim (¬l₁⊑l₂ (trans-⊑ l₁⊑l₃ l₃⊑l₂))
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabel {l = l₁} {h = l₃} l₁⊑l₃) with l₁ ⊑? l₂
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabel l₁⊑l₃) | yes l₁⊑l₂ = unlabel l₁⊑l₃
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabel l₁⊑l₃) | no ¬l₁⊑l₂ = ⊥-elim (¬l₁⊑l₂ (trans-⊑ l₁⊑l₃ l₃⊑l₂))
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabelCtx {l = l₁} {h = l₃} l₁⊑l₃ s) with l₁ ⊑? l₂
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabelCtx l₁⊑l₃ s) | yes l₁⊑l₂ = unlabelCtx l₁⊑l₃ (εᶜ-distributes-Labeled l₂ l₁⊑l₂ s)
εᶜ-distributes-Mac l₂ l₃⊑l₂ (unlabelCtx l₁⊑l₃ s) | no ¬l₁⊑l₂ = ⊥-elim (¬l₁⊑l₂ (trans-⊑ l₁⊑l₃ l₃⊑l₂))
εᶜ-distributes-Mac l₂ p Hole = Hole
εᶜ-distributes-Mac l₂ p Hole' = Hole'

εᶜ-distributes-Labeled l₂ p (AppL s) = AppL (εᶜ-distributes-Fun l₂ s)
εᶜ-distributes-Labeled {l₁} l₂ p Beta with l₁ ⊑? l₂
εᶜ-distributes-Labeled l₂ p₁ Beta | yes p = Beta
εᶜ-distributes-Labeled l₂ p Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes-Labeled {c₁ = Γ , Var x} l₂ p Lookup rewrite εᶜ-lookup-Labeled {p = p} x Γ = Lookup
-- Here I am inlining the lemma εᶜ-distributes-Closure
εᶜ-distributes-Labeled l₂ p (Dist-$ {α = Bool}) = Dist-$
εᶜ-distributes-Labeled l₂ p (Dist-$ {α = α => α₁}) = Dist-$
εᶜ-distributes-Labeled l₂ p (Dist-$ {α = Mac l₁ α}) with l₁ ⊑? l₂
εᶜ-distributes-Labeled l₂ p₁ (Dist-$ {Δ} {Mac l₁ α}) | yes p = Dist-$
εᶜ-distributes-Labeled l₂ p (Dist-$ {Δ} {Mac l₁ α}) | no ¬p = {!Dist-$!}
εᶜ-distributes-Labeled l₂ p (Dist-$ {α = Labeled l₁ α}) = {!!}
εᶜ-distributes-Labeled l₂ p (Dist-$ {α = Exception}) = Dist-$
εᶜ-distributes-Labeled l₂ p Dist-If = Dist-If
εᶜ-distributes-Labeled l₂ p (IfCond s) = IfCond (εᶜ-distributes-Bool l₂ s)
εᶜ-distributes-Labeled l₂ p IfTrue = IfTrue
εᶜ-distributes-Labeled l₂ p IfFalse = IfFalse
εᶜ-distributes-Labeled l₂ p Hole = Hole
εᶜ-distributes-Labeled l₂ p Hole' = Hole'

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
εᶜ-distributes {Mac l₁ τ} l₂ s with l₁ ⊑? l₂
εᶜ-distributes {Mac l₁ τ} l₂ s | yes p = εᶜ-distributes-Mac l₂ p s
εᶜ-distributes {Mac l₁ τ} l₂ s | no ¬p = Hole'
εᶜ-distributes {Labeled l₁ τ} l₂ s with l₁ ⊑? l₂
εᶜ-distributes {Labeled l₁ τ} l₂ s | yes p = εᶜ-distributes-Labeled l₂ p s
εᶜ-distributes {Labeled l₁ τ} l₂ s | no ¬p = Hole'
εᶜ-distributes {Exception} l s = εᶜ-distributes-Exception l s

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
data _≈ˡ_ {{l : Label}} {τ : Ty} (c₁ c₂ : CTerm τ) : Set where
  εᶜ-≡ : εᶜ l c₁ ≡ εᶜ l c₂ -> c₁ ≈ˡ c₂


-- Non-interference
-- As expected we need only determinism.
non-interference : ∀ {l τ} {c₁ c₂ c₁' c₂' : CTerm τ} -> c₁ ≈ˡ c₂ -> c₁ ⟼ c₁' -> c₂ ⟼ c₂' -> c₁' ≈ˡ c₂'
non-interference {l} (εᶜ-≡ eq) s₁ s₂ = εᶜ-≡ (aux eq (εᶜ-distributes l s₁) (εᶜ-distributes l s₂))
  where aux : ∀ {τ} {c₁ c₂ c₃ c₄ : CTerm τ} -> c₁ ≡ c₂ -> c₁ ⟼ c₃ -> c₂ ⟼ c₄ -> c₃ ≡ c₄
        aux refl s₁ s₂ = determinism s₁ s₂
