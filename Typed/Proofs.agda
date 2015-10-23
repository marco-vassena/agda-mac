module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality
open import Data.Sum

progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , Var x) = inj₁ (Step Lookup)
progress (Γ , Abs t) = inj₂ tt
progress (Γ , App t t₁) = inj₁ (Step Dist-$)
progress (Γ , If t Then t₁ Else t₂) = inj₁ (Step Dist-If)
progress (Γ , Return t) = inj₁ (Step Return)
progress (Γ , t >>= t₁) = inj₁ (Step Dist->>=)
progress (Γ , ξ) = inj₂ tt
progress (Γ , Throw t) = inj₁ (Step Throw)
progress (Γ , Catch m h) = inj₁ (Step Dist-Catch)
progress (Γ , Mac t) = inj₂ tt
progress (Γ , Macₓ t) = inj₂ tt
progress (Γ , Res t) = inj₂ tt
progress (Γ , label x t) = inj₁ (Step (label x))
progress (Γ , unlabel x t) = inj₁ (Step (Dist-unlabel x))
progress (Γ , ∙) = inj₁ (Step Hole)
progress (c $ c₁) with progress c
progress (c $ c₁) | inj₁ (Step x) = inj₁ (Step (AppL x))
progress (x , Var x₁ $ c₁) | inj₂ ()
progress (x , Abs x₁ $ c₁) | inj₂ tt = inj₁ (Step Beta)
progress (x , App x₁ x₂ $ c₁) | inj₂ ()
progress (x , If x₁ Then x₂ Else x₃ $ c₁) | inj₂ ()
progress (x , ∙ $ c₁) | inj₂ ()
progress ((c $ c₁) $ c₂) | inj₂ ()
progress (If c Then c₁ Else c₂ $ c₃) | inj₂ ()
progress (c $ˡ x , x₁) with progress c
progress (c $ˡ x₁ , x₂) | inj₁ (Step x) = inj₁ (Step (AppLˡ x))
progress ((x , Var x₁) $ˡ x₂ , x₃) | inj₂ ()
-- Problem! Here the enviroments should be the same but this is not the case 
-- in general. Putting a different enviroment seems an ad hoc solution, different from Beta
progress ((Γ , Abs x₁) $ˡ Γ' , x₃) | inj₂ tt = inj₁ (Step {!Betaˡ!}) 
progress ((Γ , App x₁ x₂) $ˡ Γ' , x₄) | inj₂ ()
progress ((x , If x₁ Then x₂ Else x₃) $ˡ x₄ , x₅) | inj₂ ()
progress ((x , ∙) $ˡ x₂ , x₃) | inj₂ ()
progress ((c $ c₁) $ˡ x , x₁) | inj₂ ()
progress ((If c Then c₁ Else c₂) $ˡ x , x₁) | inj₂ ()
progress (If c Then c₁ Else c₂) = {!!}
progress (c >>= c₁) = {!!}
progress (Catch c c₁) = {!!}
progress (unlabel x c) = {!!}

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
determinism (AppLˡ s₁) (AppLˡ s₂) rewrite determinism s₁ s₂ = refl
determinism (AppLˡ ()) Betaˡ
determinism Betaˡ (AppLˡ ())
determinism Betaˡ Betaˡ = refl
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
