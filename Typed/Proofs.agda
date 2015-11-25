module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality
open import Data.Sum

progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , （）) = inj₂ (Γ , （）)
progress (Γ , True) = inj₂ (Γ , True)
progress (Γ , False) = inj₂ (Γ , False)
progress (Γ , Var x) = inj₁ (Step (Pure Lookup))
progress (Γ , Abs t) = inj₂ (Γ , Abs t)
progress (Γ , App t t₁) = inj₁ (Step (Pure Dist-$))
progress (Γ , If t Then t₁ Else t₂) = inj₁ (Step (Pure Dist-If))
progress (Γ , Return t) = inj₁ (Step Return)
progress (Γ , t >>= t₁) = inj₁ (Step Dist->>=)
progress (Γ , ξ) = inj₂ (Γ , ξ)
progress (Γ , Throw t) = inj₁ (Step Throw)
progress (Γ , Catch m h) = inj₁ (Step Dist-Catch)
progress (Γ , Mac t) = inj₂ (Γ , (Mac t))
progress (Γ , Macₓ t) = inj₂ (Γ , (Macₓ t))
progress (Γ , Res t) = inj₂ (Γ , (Res t))
progress (Γ , Resₓ t) = inj₂ (Γ , (Resₓ t))
progress (Γ , label x t) = inj₁ (Step (label x))
progress (Γ , unlabel x t) = inj₁ (Step (Dist-unlabel x))
progress (Γ , join x t) = inj₁ (Step (Dist-join x))
progress (Γ , ∙) = inj₁ (Step (Pure Dist-∙))
progress (f $ x) with progress f
progress (f $ x₁) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (AppL x))) 
progress (.(Γ , Abs t) $ x₁) | inj₂ (Γ , Abs t) = inj₁ (Step (Pure Beta))
progress (If c Then t Else e) with progress c
progress (If c Then t Else e) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (IfCond x)))
progress (If .(Γ , True) Then t₁ Else e) | inj₂ (Γ , True) = inj₁ (Step (Pure IfTrue))
progress (If .(Γ , False) Then t₁ Else e) | inj₂ (Γ , False) = inj₁ (Step (Pure IfFalse))
progress (m >>= k) with progress m
progress (m >>= k) | inj₁ (Step s) = inj₁ (Step (BindCtx s))
progress (.(Γ , Mac t) >>= k) | inj₂ (Γ , Mac t) = inj₁ (Step Bind)
progress (.(Γ , Macₓ e) >>= k) | inj₂ (Γ , Macₓ e) = inj₁ (Step BindEx)
progress (Catch m h) with progress m
progress (Catch m h) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch ._ h) | inj₂ (Γ , Mac t) = inj₁ (Step Catch)
progress (Catch ._ h) | inj₂ (Γ , Macₓ e) = inj₁ (Step (CatchEx {Γ = Γ} {e = e} {h = h}))
progress (unlabel x c) with progress c
progress (unlabel x c) | inj₁ (Step s) = inj₁ (Step (unlabelCtx x s))
progress (unlabel x ._) | inj₂ (Γ , Res t) = inj₁ (Step (unlabel x))
progress (unlabel x ._) | inj₂ (Γ , Resₓ e) = inj₁ (Step (unlabelEx x))
progress (join x c) with progress c
progress (join x c) | inj₁ (Step s) = inj₁ (Step (joinCtx x s))
progress (join x ._) | inj₂ (Γ , Mac t) = inj₁ (Step (join x))
progress (join x ._) | inj₂ (Γ , Macₓ e) = inj₁ (Step (joinEx {e = e} x))
progress ∙ = inj₁ (Step (Pure Hole))

valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex .(Γ , （）) (Γ , （）) (Step (Pure ()))
valueNotRedex .(Γ , True) (Γ , True) (Step (Pure ()))
valueNotRedex .(Γ , False) (Γ , False) (Step (Pure ()))
valueNotRedex .(Γ , Abs t) (Γ , Abs t) (Step (Pure ()))
valueNotRedex .(Γ , ξ) (Γ , ξ) (Step (Pure ()))
valueNotRedex .(Γ , Mac t) (Γ , Mac t) (Step (Pure ()))
valueNotRedex .(Γ , Macₓ e) (Γ , Macₓ e) (Step (Pure ()))
valueNotRedex .(Γ , Res t) (Γ , Res t) (Step (Pure ()))
valueNotRedex .(Γ , Resₓ e) (Γ , Resₓ e) (Step (Pure ()))

determinism⇝ : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃
determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (AppL ()) Beta
determinism⇝ Beta (AppL ())
determinism⇝ Beta Beta = refl
determinism⇝ Lookup Lookup = refl
determinism⇝ Dist-$ Dist-$ = refl
determinism⇝ Dist-If Dist-If = refl
determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (IfCond ()) IfTrue
determinism⇝ (IfCond ()) IfFalse
determinism⇝ IfTrue (IfCond ())
determinism⇝ IfTrue IfTrue = refl
determinism⇝ IfFalse (IfCond ())
determinism⇝ IfFalse IfFalse = refl
determinism⇝ Dist-∙ Dist-∙ = refl 
determinism⇝ Hole Hole = refl

determinismMixed : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinismMixed s₁ (Pure s₂) = determinism⇝ s₁ s₂
determinismMixed () Return
determinismMixed () Dist->>=
determinismMixed () (BindCtx s₂)
determinismMixed () Bind
determinismMixed () BindEx
determinismMixed () Throw
determinismMixed () Dist-Catch
determinismMixed () (CatchCtx s₂)
determinismMixed () Catch
determinismMixed () CatchEx
determinismMixed () (label p)
determinismMixed () (Dist-unlabel p)
determinismMixed () (unlabel p)
determinismMixed () (unlabelEx p)
determinismMixed () (unlabelCtx p s₂)
determinismMixed () (Dist-join p)
determinismMixed () (joinCtx p s₂)
determinismMixed () (join p)
determinismMixed () (joinEx p)

determinism : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinism (Pure s₁) s₂ = determinismMixed s₁ s₂
determinism s₁ (Pure s₂) = sym (determinismMixed s₂ s₁)
determinism Return Return = refl
determinism Dist->>= Dist->>= = refl
determinism (BindCtx s₁) (BindCtx s₂) rewrite determinism s₁ s₂ = refl
determinism (BindCtx (Pure ())) Bind
determinism (BindCtx (Pure ())) BindEx
determinism Bind (BindCtx (Pure ()))
determinism Bind Bind = refl
determinism BindEx (BindCtx (Pure ()))
determinism BindEx BindEx = refl
determinism Throw Throw = refl
determinism Dist-Catch Dist-Catch = refl
determinism (CatchCtx s₁) (CatchCtx s₂) rewrite determinism s₁ s₂ = refl
determinism (CatchCtx (Pure ())) Catch
determinism (CatchCtx (Pure ())) CatchEx
determinism Catch (CatchCtx (Pure ()))
determinism Catch Catch = refl
determinism CatchEx (CatchCtx (Pure ()))
determinism CatchEx CatchEx = refl
determinism (label p) (label .p) = refl
determinism (Dist-unlabel p) (Dist-unlabel .p) = refl
determinism (unlabel p) (unlabel .p) = refl
determinism (unlabel p) (unlabelCtx .p (Pure ()))
determinism (unlabelCtx p (Pure ())) (unlabel .p)
determinism (unlabelCtx p (Pure ())) (unlabelEx .p)
determinism (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinism s₁ s₂ = refl
determinism (unlabelEx p) (unlabelEx .p) = refl
determinism (unlabelEx p) (unlabelCtx .p (Pure ()))
determinism (Dist-join p) (Dist-join .p) = refl
determinism (joinCtx p s₁) (joinCtx .p s₂) rewrite determinism s₁ s₂ = refl
determinism (joinCtx p (Pure ())) (join .p)
determinism (joinCtx p (Pure ())) (joinEx .p)
determinism (join p) (joinCtx .p (Pure ()))
determinism (join p) (join .p) = refl
determinism (joinEx p) (joinCtx .p (Pure ()))
determinism (joinEx p) (joinEx .p) = refl

preservation : ∀ {l : Label} {τ : Ty} {c₁ c₂ : CTerm τ} -> c₁ ⟼ c₂ -> τ ≡ τ
preservation s = refl
