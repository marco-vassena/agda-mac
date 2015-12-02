module Typed.Proofs where

open import Typed.Semantics
open import Typed.Valid
open import Relation.Binary.PropositionalEquality
open import Data.Sum

-- A closed term with valid references with respect to the given memory context
-- either can be reduced further or it is a value.
progress : ∀ {τ Δᵐ} {{m : Memory Δᵐ}} (c : CTerm τ) -> Valid Δᵐ c -> (Redex m c) ⊎ (IsValue c)
progress (Γ , （）) v = inj₂ (Γ , （）)
progress (Γ , True) v = inj₂ (Γ , True)
progress (Γ , False) v = inj₂ (Γ , False)
progress (Γ , Var x) v = inj₁ (Step (Pure Lookup))
progress (Γ , Abs t) v = inj₂ (Γ , Abs t)
progress (Γ , App t t₁) v = inj₁ (Step (Pure Dist-$))
progress (Γ , If t Then t₁ Else t₂) v = inj₁ (Step (Pure Dist-If))
progress (Γ , Return t) v = inj₁ (Step Return)
progress (Γ , t >>= t₁) v = inj₁ (Step Dist->>=)
progress (Γ , ξ) v = inj₂ (Γ , ξ)
progress (Γ , Throw t) v = inj₁ (Step Throw)
progress (Γ , Catch m h) v = inj₁ (Step Dist-Catch)
progress (Γ , Mac t) v = inj₂ (Γ , (Mac t))
progress (Γ , Macₓ t) v = inj₂ (Γ , (Macₓ t))
progress (Γ , Res t) v = inj₂ (Γ , (Res t))
progress (Γ , Resₓ t) v = inj₂ (Γ , (Resₓ t))
progress (Γ , label x t) v = inj₁ (Step (label x))
progress (Γ , unlabel x t) v = inj₁ (Step (Dist-unlabel x))
progress (Γ , join x t) v = inj₁ (Step (Dist-join x))
progress (Γ , Ref r) v = inj₂ (Γ , (Ref r))
progress (Γ , read p r) v = inj₁ (Step (Dist-read p))
progress (Γ , write p r t) v = inj₁ (Step (Dist-write p))
progress (Γ , new p r) v = inj₁ (Step (new p))
progress (Γ , ∙) v = inj₁ (Step (Pure Dist-∙))
progress (f $ x) (v₁ $ v₂) with progress f v₁
progress (f $ x₁) (v₁ $ v₂) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (AppL x)))
progress (.(Γ , Abs t) $ x₁) (v₁ $ v₂) | inj₂ (Γ , Abs t) = inj₁ (Step (Pure Beta))
progress (If c₁ Then c₂ Else e) (If v₁ Then v₂ Else v₃) with progress c₁ v₁
progress (If c₁ Then c₃ Else e) (If v₁ Then v₂ Else v₃) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (IfCond x)))
progress (If .(Γ , True) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , True) = inj₁ (Step (Pure IfTrue))
progress (If .(Γ , False) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , False) = inj₁ (Step (Pure IfFalse))
progress (m >>= k) (v >>= v₁) with progress m v
progress (m₁ >>= k) (v >>= v₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress (.(Γ , Mac t) >>= k) (v >>= v₁) | inj₂ (Γ , Mac t) = inj₁ (Step Bind)
progress (.(Γ , Macₓ e) >>= k) (v >>= v₁) | inj₂ (Γ , Macₓ e) = inj₁ (Step BindEx)
progress (Catch m h) (Catch v v₁) with progress m v
progress (Catch m₁ h) (Catch v v₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch .(Γ , Mac t) h) (Catch v v₁) | inj₂ (Γ , Mac t) = inj₁ (Step Catch)
progress (Catch .(Γ , Macₓ e) h) (Catch v v₁) | inj₂ (Γ , Macₓ e) = inj₁ (Step CatchEx)
progress (unlabel x c) (unlabel .x v) with progress c v
progress (unlabel x₁ c) (unlabel .x₁ v) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x₁ x))
progress (unlabel x₁ .(Γ , Res t)) (unlabel .x₁ v) | inj₂ (Γ , Res t) = inj₁ (Step (unlabel x₁))
progress (unlabel x₁ .(Γ , Resₓ e)) (unlabel .x₁ v) | inj₂ (Γ , Resₓ e) = inj₁ (Step (unlabelEx x₁))
progress (join x c) (join .x v) with progress c v
progress (join x₁ c) (join .x₁ v) | inj₁ (Step x) = inj₁ (Step (joinCtx x₁ x))
progress (join x₁ .(Γ , Mac t)) (join .x₁ v) | inj₂ (Γ , Mac t) = inj₁ (Step (join x₁))
progress (join x₁ .(Γ , Macₓ e)) (join .x₁ v) | inj₂ (Γ , Macₓ e) = inj₁ (Step (joinEx x₁))
progress (write p r c) (write .p v v₁) with progress r v
progress (write p r c) (write .p v v₁) | inj₁ (Step x) = inj₁ (Step (writeCtx p x))
progress (write p (Γ , Ref α) c) (write .p (Γ' , Ref r) v₁) | inj₂ (.Γ , Ref .α) = inj₁ (Step (write p r))
progress (read p r) (read .p v) with progress r v
progress (read p r) (read .p v) | inj₁ (Step x) = inj₁ (Step (readCtx p x))
progress (read p (Γ , Ref α)) (read .p (Γ' , Ref r)) | inj₂ (.Γ , Ref .α) = inj₁ (Step (read p r))
progress ∙ v = inj₁ (Step (Pure Hole))

-- valueNotRedex : ∀ {τ Δ} {m : Memory Δ} -> (c : CTerm τ) -> IsValue c -> NormalForm m c
-- valueNotRedex .(Γ , （）) (Γ , （）) (Step (Pure ()))
-- valueNotRedex .(Γ , True) (Γ , True) (Step (Pure ()))
-- valueNotRedex .(Γ , False) (Γ , False) (Step (Pure ()))
-- valueNotRedex .(Γ , Abs t) (Γ , Abs t) (Step (Pure ()))
-- valueNotRedex .(Γ , ξ) (Γ , ξ) (Step (Pure ()))
-- valueNotRedex .(Γ , Mac t) (Γ , Mac t) (Step (Pure ()))
-- valueNotRedex .(Γ , Macₓ e) (Γ , Macₓ e) (Step (Pure ()))
-- valueNotRedex .(Γ , Res t) (Γ , Res t) (Step (Pure ()))
-- valueNotRedex .(Γ , Resₓ e) (Γ , Resₓ e) (Step (Pure ()))

-- determinism⇝ : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃
-- determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
-- determinism⇝ (AppL ()) Beta
-- determinism⇝ Beta (AppL ())
-- determinism⇝ Beta Beta = refl
-- determinism⇝ Lookup Lookup = refl
-- determinism⇝ Dist-$ Dist-$ = refl
-- determinism⇝ Dist-If Dist-If = refl
-- determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
-- determinism⇝ (IfCond ()) IfTrue
-- determinism⇝ (IfCond ()) IfFalse
-- determinism⇝ IfTrue (IfCond ())
-- determinism⇝ IfTrue IfTrue = refl
-- determinism⇝ IfFalse (IfCond ())
-- determinism⇝ IfFalse IfFalse = refl
-- determinism⇝ Dist-∙ Dist-∙ = refl 
-- determinism⇝ Hole Hole = refl

-- determinismMixed : ∀ {Δ τ} {m : Memory Δ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> ⟨ m ∥ c₁ ⟩ ⟼ ⟨ m ∥ c₃ ⟩ -> c₂ ≡ c₃
-- determinismMixed s₁ (Pure s₂) = determinism⇝ s₁ s₂
-- determinismMixed () Return
-- determinismMixed () Dist->>=
-- determinismMixed () (BindCtx s₂)
-- determinismMixed () Bind
-- determinismMixed () BindEx
-- determinismMixed () Throw
-- determinismMixed () Dist-Catch
-- determinismMixed () (CatchCtx s₂)
-- determinismMixed () Catch
-- determinismMixed () CatchEx
-- determinismMixed () (label p)
-- determinismMixed () (Dist-unlabel p)
-- determinismMixed () (unlabel p)
-- determinismMixed () (unlabelEx p)
-- determinismMixed () (unlabelCtx p s₂)
-- determinismMixed () (Dist-join p)
-- determinismMixed () (joinCtx p s₂)
-- determinismMixed () (join p)
-- determinismMixed () (joinEx p)

-- -- TODO
-- -- @Ale I think I should prove this for some m₃ and show also that m₂ ≡ m₃
-- determinism : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} ->
--                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> c₂ ≡ c₃
-- determinism (Pure s₁) s₂ = determinismMixed s₁ s₂
-- determinism s₁ (Pure s₂) = sym (determinismMixed s₂ s₁)
-- determinism Return Return = refl
-- determinism Dist->>= Dist->>= = refl
-- determinism (BindCtx s₁) (BindCtx s₂) rewrite determinism s₁ s₂ = refl
-- determinism (BindCtx (Pure ())) Bind
-- determinism (BindCtx (Pure ())) BindEx
-- determinism Bind (BindCtx (Pure ()))
-- determinism Bind Bind = refl
-- determinism BindEx (BindCtx (Pure ()))
-- determinism BindEx BindEx = refl
-- determinism Throw Throw = refl
-- determinism Dist-Catch Dist-Catch = refl
-- determinism (CatchCtx s₁) (CatchCtx s₂) rewrite determinism s₁ s₂ = refl
-- determinism (CatchCtx (Pure ())) Catch
-- determinism (CatchCtx (Pure ())) CatchEx
-- determinism Catch (CatchCtx (Pure ()))
-- determinism Catch Catch = refl
-- determinism CatchEx (CatchCtx (Pure ()))
-- determinism CatchEx CatchEx = refl
-- determinism (label p) (label .p) = refl
-- determinism (Dist-unlabel p) (Dist-unlabel .p) = refl
-- determinism (unlabel p) (unlabel .p) = refl
-- determinism (unlabel p) (unlabelCtx .p (Pure ()))
-- determinism (unlabelCtx p (Pure ())) (unlabel .p)
-- determinism (unlabelCtx p (Pure ())) (unlabelEx .p)
-- determinism (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinism s₁ s₂ = refl
-- determinism (unlabelEx p) (unlabelEx .p) = refl
-- determinism (unlabelEx p) (unlabelCtx .p (Pure ()))
-- determinism (Dist-join p) (Dist-join .p) = refl
-- determinism (joinCtx p s₁) (joinCtx .p s₂) rewrite determinism s₁ s₂ = refl
-- determinism (joinCtx p (Pure ())) (join .p)
-- determinism (joinCtx p (Pure ())) (joinEx .p)
-- determinism (join p) (joinCtx .p (Pure ()))
-- determinism (join p) (join .p) = refl
-- determinism (joinEx p) (joinCtx .p (Pure ()))
-- determinism (joinEx p) (joinEx .p) = refl

-- preservation : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {τ : Ty} {c₁ c₂ : CTerm τ} -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> τ ≡ τ
-- preservation s = refl
