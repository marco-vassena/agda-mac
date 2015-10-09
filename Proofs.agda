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
progress (Γ , Return j) = inj₁ (Step Return)
progress (Γ , m >>= k) = inj₁ (Step Dist->>=)
progress (Γ , ξ) = inj₂ tt
progress (Γ , Throw e) = inj₁ (Step Throw)
progress (Γ , Catch m h) = inj₁ (Step Dist-Catch)
progress (Γ , Mac j) = inj₂ tt
progress (Γ , Macₓ j) = inj₂ tt
progress (Γ , label x j) = inj₁ (Step (label x))
progress (Γ , unlabel x j) = inj₁ (Step Dist-unlabel)
progress (Γ , Res j) = inj₂ tt
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
progress (m >>= k) with progress m
progress (m >>= k) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress ((Γ , App j j₁) >>= k) | inj₂ ()
progress ((Γ , Var x) >>= k) | inj₂ ()
progress ((Γ , (If j Then j₁ Else j₂)) >>= k) | inj₂ ()
progress ((Γ , Return j) >>= k) | inj₂ ()
progress ((Γ , j >>= j₁) >>= k₁) | inj₂ ()
progress ((Γ , Throw j) >>= k) | inj₂ ()
progress ((Γ , Catch j j₁) >>= k) | inj₂ ()
progress ((Γ , Mac j) >>= k) | inj₂ tt = inj₁ (Step Bind)
progress ((Γ , Macₓ j) >>= k) | inj₂ tt = inj₁ (Step BindEx)
progress ((Γ , label x j) >>= k) | inj₂ ()
progress ((Γ , unlabel x j) >>= k) | inj₂ ()
progress ((m $ m₁) >>= k) | inj₂ ()
progress ((If m Then m₁ Else m₂) >>= k) | inj₂ ()
progress (m >>= m₁ >>= k) | inj₂ ()
progress (Catch m m₁ >>= k) | inj₂ ()
progress (unlabel x m >>= k) | inj₂ ()
progress (Catch m h) with progress m
progress (Catch m h) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch (Γ , App t t₃) h) | inj₂ ()
progress (Catch (Γ , Var x) h) | inj₂ ()
progress (Catch (Γ , (If t Then t₄ Else t₅)) h) | inj₂ ()
progress (Catch (Γ , Return t₁) h) | inj₂ ()
progress (Catch (Γ , t₁ >>= t₂) h) | inj₂ ()
progress (Catch (Γ , Throw t₁) h) | inj₂ ()
progress (Catch (Γ , Catch t₁ t₂) h₁) | inj₂ ()
progress (Catch (Γ , Mac t₁) h) | inj₂ tt = inj₁ (Step Catch)
progress (Catch (Γ , Macₓ t₁) h) | inj₂ tt = inj₁ (Step CatchEx)
progress (Catch (Γ , label x j) h₁) | inj₂ ()
progress (Catch (Γ , unlabel x j) h) | inj₂ ()
progress (Catch (m $ m₁) h) | inj₂ ()
progress (Catch (If m Then m₁ Else m₂) h) | inj₂ ()
progress (Catch (m >>= m₁) h) | inj₂ ()
progress (Catch (Catch m m₁) h) | inj₂ ()
progress (Catch (unlabel x m) h₁) | inj₂ ()
progress (unlabel p x) with progress x
progress (unlabel p x) | inj₁ (Step s) = inj₁ (Step (unlabelCtx s))
progress (unlabel p (Γ , App j j₁)) | inj₂ ()
progress (unlabel p (Γ , Var x)) | inj₂ ()
progress (unlabel p (Γ , (If j Then j₁ Else j₂))) | inj₂ ()
progress (unlabel p (Γ , Res j)) | inj₂ tt = inj₁ (Step (unlabel p))
progress (unlabel p (x $ x₁)) | inj₂ ()
progress (unlabel p (If x Then x₁ Else x₂)) | inj₂ ()

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex (Γ , True) isV (Step ())
valueNotRedex (Γ , False) isV (Step ())
valueNotRedex (Γ , App f x) () nf
valueNotRedex (Γ , Abs j) isV (Step ())
valueNotRedex (Γ , Var x) () nf
valueNotRedex (Γ , (If j Then j₁ Else j₂)) () nf
valueNotRedex (Γ , Return j) () s
valueNotRedex (Γ , j >>= j₁) () s
valueNotRedex (Γ , ξ) isV (Step ())
valueNotRedex (Γ , Throw j) () nf
valueNotRedex (Γ , Catch j j₁) () nf
valueNotRedex (Γ , Mac j) tt (Step ())
valueNotRedex (Γ , Macₓ j) isV (Step ())
valueNotRedex (Γ , label x j) () nf
valueNotRedex (Γ , unlabel x j) () nf
valueNotRedex (Γ , Res j) isV (Step ())
valueNotRedex (c $ c₁) () nf
valueNotRedex (If c Then c₁ Else c₂) () nf
valueNotRedex (c >>= c₁) () s
valueNotRedex (Catch c c₁) () nf
valueNotRedex (unlabel x c) () nf


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
determinism Return Return = refl
determinism Dist->>= Dist->>= = refl
determinism (BindCtx s₁) (BindCtx s₂) with determinism s₁ s₂
determinism (BindCtx s₁) (BindCtx s₂) | refl = refl
determinism (BindCtx ()) Bind
determinism (BindCtx ()) BindEx
determinism Bind (BindCtx ())
determinism Bind Bind = refl
determinism BindEx (BindCtx ())
determinism BindEx BindEx = refl
determinism Throw Throw = refl
determinism Dist-Catch Dist-Catch = refl
determinism (CatchCtx s₁) (CatchCtx s₂) rewrite determinism s₁ s₂ = refl
determinism (CatchCtx ()) Catch
determinism (CatchCtx ()) CatchEx
determinism Catch (CatchCtx ())
determinism Catch Catch = refl
determinism CatchEx (CatchCtx ())
determinism CatchEx CatchEx = refl
determinism (label p) (label .p) = refl
determinism Dist-unlabel Dist-unlabel = refl
determinism (unlabel p) (unlabel .p) = refl
determinism (unlabel p) (unlabelCtx ())
determinism (unlabelCtx ()) (unlabel p)
determinism (unlabelCtx s₁) (unlabelCtx s₂) rewrite determinism s₁ s₂ = refl

-- Type preservation is trivial because it is enforced by the definition of c₁ ⟼ c₂
-- in which two closed terms always have the same type.
preservation : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation _ = refl
