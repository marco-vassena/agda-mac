module Security.NonInterference where

open import Security.Base
open import Proofs
open import Semantics
open import Relation.Binary.PropositionalEquality


-- Looking up in an erased environment is equivalent to
-- firstly looking up and then erasing the result.
εᶜ-lookup : ∀ {{l}} {n} (Γ : Env n) (p : Fin n) -> lookup p (εᶜ-env l Γ) ≡ εᶜ l (lookup p Γ)
εᶜ-lookup [] ()
εᶜ-lookup (c ∷ Γ) zero = refl
εᶜ-lookup (c ∷ Γ) (suc p) rewrite εᶜ-lookup Γ p = refl

-- The erasure function distributes over the small step semantics
-- For simple proofs we do not need the Erasureᶜ.
εᶜ-distributes : ∀ {l} (c₁ c₂ : CTerm) -> c₁ ⟼ c₂ -> εᶜ l c₁ ⟼ εᶜ l c₂ 
εᶜ-distributes (c₁ $ x) (c₂ $ .x) (AppL s) = AppL (εᶜ-distributes c₁ c₂ s)
εᶜ-distributes ._ ._ Beta = Beta
εᶜ-distributes (Γ , Var p) .(lookup p Γ) Lookup rewrite sym (εᶜ-lookup Γ p) = Lookup
εᶜ-distributes ._ ._ Dist-$ = Dist-$
εᶜ-distributes ._ ._ Dist-If = Dist-If
εᶜ-distributes ._ ._ (IfCond s) = IfCond (εᶜ-distributes _ _ s)
εᶜ-distributes ._ c₂ IfTrue = IfTrue
εᶜ-distributes ._ c₂ IfFalse = IfFalse
εᶜ-distributes ._ ._ Return = Return
εᶜ-distributes ._ ._ Dist->>= = Dist->>=
εᶜ-distributes ._ ._ (BindCtx s) = BindCtx (εᶜ-distributes _ _ s)
εᶜ-distributes ._ ._ Bind = Bind
εᶜ-distributes ._ ._ BindEx = BindEx
εᶜ-distributes ._ ._ Throw = Throw
εᶜ-distributes ._ ._ Dist-Catch = Dist-Catch
εᶜ-distributes ._ ._ (CatchCtx s) = CatchCtx (εᶜ-distributes _ _ s)
εᶜ-distributes ._ ._ Catch = Catch
εᶜ-distributes ._ ._ CatchEx = CatchEx
εᶜ-distributes {l₁} ._ ._ (label {h = l₂} p) with l₁ ⊑? l₂
εᶜ-distributes ._ ._ (label p) | yes _ = label p
εᶜ-distributes ._ ._ (label p) | no _ = label p
εᶜ-distributes ._ ._ Dist-unlabel = Dist-unlabel
εᶜ-distributes {l₁} (unlabel (Γ , Res .l₂ t)) (.Γ , Return .t) (unlabel {l = l₂}) with l₁ ⊑? l₂
εᶜ-distributes (unlabel (Γ , Res ._ t)) (.Γ , Return .t) unlabel | yes l₁⊑l₂ = unlabel
-- FIX Issue with proof
-- c₁ = unlabel (Γ , Res l₂ t)
-- c₂ = (Γ , Return t)
-- unlabel : c₁ ⟼ c₂
-- Since l₁ ⋢ l₂, t is erased from c₁, leading to c₁ₑ = unlabel (Γ , Res l₂ ∙)
-- For c₂ instead the erasure function is applied homorphically, c₂ₑ = (εᶜ-env l₁ Γ , Return (ε l₁ t)) 
-- Since ∙ is in general different from ε l t the rule unlabel does not apply.
-- My best guess is that the erasure function should be adjusted to perform the same check in Return x
-- After all if we type Return x : Mac H a we are marking sensitive data, isn'it ?
εᶜ-distributes (unlabel (Γ , Res ._ t)) (.Γ , Return .t) unlabel | no l₁⋢l₂ = {!unlabel !}
εᶜ-distributes ._ ._ (unlabelCtx s) = unlabelCtx (εᶜ-distributes _ _ s)
εᶜ-distributes ._ ._ Hole = Hole


-- Reduction of pure and monadic terms with erasure
data _⟼ˡ_ {{l : Label}} : CTerm -> CTerm -> Set where
  Step-εᶜ : ∀ {c₁ c₂ c₂ₑ} -> c₁ ⟼ c₂ -> Erasureᶜ l c₂ c₂ₑ -> c₁ ⟼ˡ c₂ₑ 

-- l-equivalence
-- Two closed terms are l-equivalent if they are equivalent
-- after applying on them the erasure function with label l.
data _≈ˡ_ {{l : Label}} (c₁ c₂ : CTerm) : Set where
  εᶜ-≡ : ∀ {c₁ₑ c₂ₑ} -> Erasureᶜ l c₁ c₁ₑ -> Erasureᶜ l c₂ c₂ₑ -> c₁ₑ ≡ c₂ₑ -> c₁ ≈ˡ c₂

-- The small step + erasure relation is also deterministic
-- determinismˡ : ∀ {l c₁ c₂ c₃} -> c₁ ⟼ˡ c₂ -> c₁ ⟼ˡ c₃ -> c₂ ≡ c₃
-- determinismˡ (Step-εᶜ s₁ e₁) (Step-εᶜ s₂ e₂) 
--   with determinism s₁ s₂ | Erasureᶜ-εᶜ e₁ | Erasureᶜ-εᶜ e₂
-- determinismˡ (Step-εᶜ s₁ e₁) (Step-εᶜ s₂ e₂) | refl | refl | refl = refl

-- Non-interference
-- non-interference : ∀ {l c₁ c₂ c₁' c₂'} -> c₁ ≈ˡ c₂ -> c₁ ⟼ c₁' -> c₂ ⟼ c₂' -> c₁' ≈ˡ c₂'
--   non-interference {l} {c₁} {c₂} {c₁'} {c₂'} (εᶜ-≡ {c₁ₑ = c₁ₑ} {c₂ₑ = .c₁ₑ} e₁ e₂ refl) s₁ s₂ with Step-εᶜ {c₁} {c₁'} s₁ {!e₁!} | Step-εᶜ {!!} {!!} 
-- ... | a | b = {!!}

-- non-interference (εᶜ-≡ e₁ e₂ eq) s₁ s₂ | refl | refl = {!!}
--  determinismˡ (Step-εᶜ s₁ {!e₁!}) {!!}
-- ... | r = {!!}
