module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality

-- A closed term is a Redex if it can be reduced further
data Redex {τ : Ty}(c : CTerm τ) : Set where
  Step : ∀ {c' : CTerm τ} -> c ⟼ c' -> Redex c

-- Normal forms
-- A closed term is in normal form if it cannot be reduced further
NormalForm : ∀ {τ} -> CTerm τ -> Set
NormalForm c = ¬ Redex c

valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
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
valueNotRedex (Γ , unlabel x t) () nf
valueNotRedex (Γ , Res t) isV (Step ())
valueNotRedex (Γ , ∙) () s
valueNotRedex (f $ x) () nf
valueNotRedex (If c Then t Else e) () nf
valueNotRedex (m >>= k) () s
valueNotRedex (Catch m h) () nf
valueNotRedex (unlabel x t) () nf
valueNotRedex (f $ˡ Γ , v) () nf



-- In principle once we prove the bijection between typed and untyped semantics
-- we can keep only one proof and derive the other.
determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinism (AppL s₁) (AppL s₂) rewrite determinism s₁ s₂ = refl
determinism (AppL ()) Beta
determinism Beta (AppL ())
determinism Beta Beta = refl
determinism Lookup Lookup = refl
determinism Dist-$ Dist-$ = refl
determinism Dist-If Dist-If = refl
determinism (IfCond s₁) (IfCond s₂) rewrite determinism s₁ s₂ = refl
determinism (IfCond ()) IfTrue
determinism (IfCond ()) IfFalse
determinism IfTrue (IfCond ())
determinism IfTrue IfTrue = refl
determinism IfFalse (IfCond ())
determinism IfFalse IfFalse = refl
determinism Return Return = refl
determinism Dist->>= Dist->>= = refl
determinism (BindCtx s₁) (BindCtx s₂) rewrite determinism s₁ s₂ = refl
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
determinism (Dist-unlabel p) (Dist-unlabel .p) = refl
determinism (unlabel p) (unlabel .p) = refl
determinism (unlabel p) (unlabelCtx .p ())
determinism (unlabelCtx p ()) (unlabel .p)
determinism (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinism s₁ s₂ = refl
determinism Hole Hole = refl

preservation : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation s = refl
