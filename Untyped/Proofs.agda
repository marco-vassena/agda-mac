module Untyped.Proofs where

open import Untyped.Semantics
open import Data.Sum
open import Relation.Binary.PropositionalEquality

-- Every well-typed closed term is either a value or can be reduced further
progress : ∀ {c τ} -> c :: τ -> (Redex c) ⊎ (IsValue c)
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , App f x) = inj₁ (Step Dist-$)
progress (Γ , Abs t) = inj₂ tt
progress (Γ , Var p) = inj₁ (Step Lookup)
progress (Γ , (If c Then t Else e)) = inj₁ (Step Dist-If)
progress (Γ , Return t) = inj₁ (Step Return)
progress (Γ , m >>= k) = inj₁ (Step Dist->>=)
progress (Γ , ξ) = inj₂ tt
progress (Γ , Throw e) = inj₁ (Step Throw)
progress (Γ , Catch m h) = inj₁ (Step Dist-Catch)
progress (Γ , Mac t) = inj₂ tt
progress (Γ , Macₓ e) = inj₂ tt
progress (Γ , label p t) = inj₁ (Step (label p))
progress (Γ , unlabel p t) = inj₁ (Step Dist-unlabel)
progress (Γ , Res t) = inj₂ tt
progress (Γ , ∙) = inj₁ (Step Hole)
progress (f $ x) with progress f
progress (f $ x) | inj₁ (Step s) = inj₁ (Step (AppL s))
progress (Γ₁ , App f f₁ $ x₁) | inj₂ ()
progress (Γ₁ , Abs f $ x₁) | inj₂ tt = inj₁ (Step Beta)
progress (Γ₁ , Var p $ x₁) | inj₂ ()
progress (Γ₁ , (If f Then f₁ Else f₂) $ x₁) | inj₂ ()
progress (Γ₁ , ∙ $ x₁) | inj₂ ()
progress ((f $ y) $ x) | inj₂ ()
progress (If f Then f₁ Else f₂ $ x₁) | inj₂ ()
progress (∙ $ x₁) | inj₂ () 
progress (If c Then t Else e) with progress c
progress (If c Then t Else e) | inj₁ (Step s) = inj₁ (Step (IfCond s))
progress (If Γ₁ , True Then t₁ Else e₁) | inj₂ y = inj₁ (Step IfTrue)
progress (If Γ₁ , False Then t₁ Else e₁) | inj₂ y = inj₁ (Step IfFalse)
progress (If Γ₁ , App c c₁ Then t₃ Else e₁) | inj₂ ()
progress (If Γ₁ , Var p Then t₁ Else e₁) | inj₂ ()
progress (If Γ₁ , (If c Then c₁ Else c₂) Then t₄ Else e₁) | inj₂ ()
progress (If Γ₁ , ∙ Then t₁ Else e₁) | inj₂ ()
progress (If c $ c₁ Then t₁ Else e₁) | inj₂ ()
progress (If If c₁ Then c₂ Else c₃ Then t₂ Else e₂) | inj₂ ()
progress (If ∙ Then c₂ Else c₃) | inj₂ ()
progress (m >>= k) with progress m
progress (m₁ >>= k₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress ((Γ₁ , App x₁ x₂) >>= k₁) | inj₂ ()
progress ((Γ₁ , Var p) >>= k₁) | inj₂ ()
progress ((Γ₁ , (If x₁ Then x₂ Else x₃)) >>= k₁) | inj₂ ()
progress ((Γ₁ , Return x₁) >>= k₁) | inj₂ ()
progress ((Γ₁ , x₁ >>= x₂) >>= k₂) | inj₂ ()
progress ((Γ₁ , Throw x₁) >>= k₁) | inj₂ ()
progress ((Γ₁ , Catch x₁ x₂) >>= k₁) | inj₂ ()
progress ((Γ₁ , Mac x₁) >>= k₁) | inj₂ tt = inj₁ (Step Bind)
progress ((Γ₁ , Macₓ x₁) >>= k₁) | inj₂ tt = inj₁ (Step BindEx)
progress ((Γ₁ , label p x₁) >>= k₁) | inj₂ ()
progress ((Γ₁ , unlabel x x₁) >>= k₁) | inj₂ ()
progress ((Γ₁ , ∙) >>= k₁) | inj₂ ()
progress ((m₁ $ m₂) >>= k₁) | inj₂ ()
progress ((If m₁ Then m₂ Else m₃) >>= k₁) | inj₂ ()
progress (m₁ >>= m₂ >>= k₂) | inj₂ ()
progress (Catch m₁ m₂ >>= k₁) | inj₂ ()
progress (unlabel m₁ >>= k₁) | inj₂ ()
progress (∙ >>= k₁) | inj₂ ()
progress (Catch m h) with progress m
progress (Catch m₁ h₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch (̋Γ , App m m₁) h₁) | inj₂ ()
progress (Catch (̋Γ , Var p) h₁) | inj₂ ()
progress (Catch (̋Γ , (If m Then m₁ Else m₂)) h₁) | inj₂ ()
progress (Catch (̋Γ , Return m) h₁) | inj₂ ()
progress (Catch (̋Γ , m >>= m₁) h₁) | inj₂ ()
progress (Catch (̋Γ , Throw m) h₁) | inj₂ ()
progress (Catch (̋Γ , Catch m m₁) h₂) | inj₂ ()
progress (Catch (̋Γ , Mac m) h₁) | inj₂ y = inj₁ (Step Catch)
progress (Catch (̋Γ , Macₓ m) h₁) | inj₂ y = inj₁ (Step CatchEx)
progress (Catch (̋Γ , label p m) h₂) | inj₂ ()
progress (Catch (̋Γ , unlabel x m) h₁) | inj₂ ()
progress (Catch (̋Γ , ∙) h₁) | inj₂ ()
progress (Catch (m₁ $ m₂) h₁) | inj₂ ()
progress (Catch (If m₁ Then m₂ Else m₃) h₁) | inj₂ ()
progress (Catch (m₁ >>= m₂) h₁) | inj₂ ()
progress (Catch (Catch m₁ m₂) h₂) | inj₂ ()
progress (Catch (unlabel m₁) h₁) | inj₂ ()
progress (Catch ∙ h₁) | inj₂ ()
progress (unlabel t) with progress t
progress (unlabel t₁) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x))
progress (unlabel (Γ₁ , App t t₃)) | inj₂ ()
progress (unlabel (Γ₁ , Var p)) | inj₂ ()
progress (unlabel (Γ₁ , (If t Then t₄ Else t₅))) | inj₂ ()
progress (unlabel (Γ₁ , Res t₁)) | inj₂ tt = inj₁ (Step unlabel)
progress (unlabel (Γ₁ , ∙)) | inj₂ ()
progress (unlabel (t₁ $ t₂)) | inj₂ ()
progress (unlabel (If t₁ Then t₂ Else t₃)) | inj₂ ()
progress (unlabel ∙) | inj₂ ()
progress ∙ = inj₁ (Step Hole')

-- Lemma.
-- Values are not reducible.
valueNotRedex : ∀ (c : CTerm) -> IsValue c -> NormalForm c
valueNotRedex (Γ , True) isV (Step ())
valueNotRedex (Γ , False) isV (Step ())
valueNotRedex (Γ , App f x) () nf
valueNotRedex (Γ , Abs t) isV (Step ())
valueNotRedex (Γ , Var x) () nf
valueNotRedex (Γ , (If c Then t Else e)) () nf
valueNotRedex (Γ , Return t) () s
valueNotRedex (Γ , m >>= k) () s
valueNotRedex (Γ , ξ) isV (Step ())
valueNotRedex (Γ , Throw t) () nf
valueNotRedex (Γ , Catch m h) () nf
valueNotRedex (Γ , Mac t) tt (Step ())
valueNotRedex (Γ , Macₓ t) isV (Step ())
valueNotRedex (Γ , label x t) () nf
valueNotRedex (Γ , unlabel t) () nf
valueNotRedex (Γ , Res p t) isV (Step ())
valueNotRedex (Γ , ∙) () s
valueNotRedex (f $ x) () nf
valueNotRedex (If c Then t Else e) () nf
valueNotRedex (m >>= k) () s
valueNotRedex (Catch m h) () nf
valueNotRedex (unlabel t) () nf
valueNotRedex ∙ () nf

-- | The small step semantics is deterministic.
-- At most one rule apply per term.
determinism : ∀ {c₁ c₂ c₃ : CTerm} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
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
determinism unlabel unlabel = refl
determinism unlabel (unlabelCtx ())
determinism (unlabelCtx ()) unlabel
determinism (unlabelCtx s₁) (unlabelCtx s₂) rewrite determinism s₁ s₂ = refl
determinism Hole Hole = refl
determinism Hole' Hole' = refl

-- A well-typed closed term when reduced preserves its type.
preservation : ∀ {τ} {c₁ c₂ : CTerm} -> c₁ :: τ -> c₁ ⟼ c₂ -> c₂ :: τ
preservation (f $ x) (AppL s) = preservation f s $ x
preservation (Γ , Abs t $ x) Beta = x ∷ Γ , t
preservation ([] , Var ()) Lookup
preservation (x ∷ Γ , Var Here) Lookup = x
preservation (x ∷ Γ , Var (There p)) Lookup = preservation (Γ , Var p) Lookup
preservation (Γ , App f x) Dist-$ = Γ , f $ Γ , x
preservation (Γ , (If c Then t Else e)) Dist-If = If Γ , c Then Γ , t Else (Γ , e)
preservation (If c Then t Else e) (IfCond s) = If preservation c s Then t Else e
preservation (If Γ , True Then t₂ Else t₃) IfTrue = t₂
preservation (If Γ , False Then t₂ Else t₃) IfFalse = t₃
preservation (Γ , Return t) Return = Γ , (Mac t)
preservation (Γ , m >>= k) Dist->>= = (Γ , m) >>= (Γ , k)
preservation (m >>= k) (BindCtx s) = preservation m s >>= k
preservation ((Γ , Mac m) >>= k) Bind = k $ Γ , m
preservation ((Γ , Macₓ e) >>= k) BindEx = Γ , (Throw e)
preservation (Γ , Throw t) Throw = Γ , (Macₓ t)
preservation (Γ , Catch m h) Dist-Catch = Catch (Γ , m) (Γ , h)
preservation (Catch m h) (CatchCtx s) = Catch (preservation m s) h
preservation (Catch (Γ , Mac t) h) Catch = Γ , (Return t)
preservation (Catch (Γ , Macₓ t) h) CatchEx = h $ (Γ , t)
preservation (Γ , label p t) (label .p) = Γ , (Return (Res t))
preservation (Γ , unlabel x t) Dist-unlabel = unlabel (Γ , t)
preservation (unlabel (Γ , Res t)) unlabel = Γ , (Return t)
preservation (unlabel t) (unlabelCtx s) = unlabel (preservation t s)
preservation (Γ , ∙) Hole = Γ , ∙
preservation ∙ Hole' = ∙
