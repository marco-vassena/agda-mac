module Proofs where

open import Semantics
open import Data.Sum
open import Relation.Binary.PropositionalEquality

-- Every closed term is either a value or can be reduced further
progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , App f x) = inj₁ (Step Dist-$)
progress (Γ , Abs t) = inj₂ tt
progress (Γ , Var x) = inj₁ (Step Lookup)
progress (Γ , (If c Then t Else e)) = inj₁ (Step Dist-If)
progress (f $ x) with progress f
progress (f $ x) | inj₁ (Step s) = inj₁ (Step (AppL s))
progress (Γ , App j j₁ $ x) | inj₂ ()
progress (Γ , Abs j $ x) | inj₂ tt = inj₁ (Step Beta)
progress (Γ , Var x $ x₁) | inj₂ ()
progress (Γ , (If j Then j₁ Else j₂) $ x) | inj₂ ()
progress ((f $ f₁) $ x) | inj₂ ()
progress (If f Then f₁ Else f₂ $ x) | inj₂ ()
progress (If c Then t Else e) with progress c
progress (If c Then t Else e) | inj₁ (Step x) = inj₁ (Step (IfCond x))
progress (If Γ , True Then t₁ Else e) | inj₂ tt = inj₁ (Step IfTrue)
progress (If Γ , False Then t₁ Else e) | inj₂ tt = inj₁ (Step IfFalse)
progress (If Γ , App j j₁ Then t₃ Else e) | inj₂ ()
progress (If Γ , Var x Then t₁ Else e) | inj₂ ()
progress (If Γ , (If j Then j₁ Else j₂) Then t₄ Else e) | inj₂ ()
progress (If c $ c₁ Then t Else e) | inj₂ ()
progress (If If c Then c₁ Else c₂ Then t Else e) | inj₂ ()

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex (Γ , True) isV (Step ())
valueNotRedex (Γ , False) isV (Step ())
valueNotRedex (Γ , App f x) () nf
valueNotRedex (Γ , Abs j) isV (Step ())
valueNotRedex (Γ , Var x) () nf
valueNotRedex (Γ , (If j Then j₁ Else j₂)) () nf
valueNotRedex (c $ c₁) () nf
valueNotRedex (If c Then c₁ Else c₂) () nf

-- | The small step semantics is deterministic.
-- At most one rule apply per term.
determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinism (AppL s₁) (AppL s₂) rewrite determinism s₁ s₂ = refl
determinism {c₁ = Γ , Abs j $ x} (AppL s₁) Beta = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₁)) -- AppL does not apply
determinism {c₁ = Γ , Abs j $ x} Beta (AppL s₂) = ⊥-elim (valueNotRedex (Γ , Abs j) tt (Step s₂)) -- Idem
determinism Beta Beta = refl
determinism Lookup Lookup = refl
determinism Dist-$ Dist-$ = refl
determinism Dist-If Dist-If = refl
determinism (IfCond s₁) (IfCond s₂) with determinism s₁ s₂
determinism (IfCond s₁) (IfCond s₂) | refl = refl
determinism (IfCond s₁) IfTrue = ⊥-elim (valueNotRedex (_ , True) tt (Step s₁))
determinism (IfCond s₁) IfFalse = ⊥-elim (valueNotRedex (_ , False) tt (Step s₁))
determinism IfTrue (IfCond s₂) = ⊥-elim (valueNotRedex (_ , True) tt (Step s₂))
determinism IfTrue IfTrue = refl
determinism IfFalse (IfCond s₂) = ⊥-elim (valueNotRedex (_ , False) tt (Step s₂))
determinism IfFalse IfFalse = refl

-- Type preservation is trivial because it is enforced by the definition of c₁ ⟼ c₂
-- in which two closed terms always have the same type.
preservation : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation _ = refl
