module Typed.Proofs where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H

open import Typed.Semantics
open import Typed.Valid

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
progress (Γ , (t >>= t₁)) v = inj₁ (Step Dist->>=)
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
progress (If c₁ Then c₃ Else e) (If v₁ Then v₂ Else v₃) | inj₁ (Step (Pure x)) 
  = inj₁ (Step (Pure (IfCond x)))
progress (If .(Γ , True) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , True) 
  = inj₁ (Step (Pure IfTrue))
progress (If .(Γ , False) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , False) 
  = inj₁ (Step (Pure IfFalse))
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
progress (write p (Γ , Ref n) c) (write .p (Γ' , Ref x) v₁) | inj₂ (.Γ , Ref .n) 
  =  inj₁ (Step (write p x))
progress (read p r) (read .p v) with progress r v
progress (read p r) (read .p v) | inj₁ (Step x) = inj₁ (Step (readCtx p x))
progress (read p (Γ , Ref n)) (read .p (Γ' , Ref x)) | inj₂ (.Γ , Ref .n) = inj₁ (Step (read p x))
progress ∙ v = inj₁ (Step (Pure Hole))

valueNotRedex : ∀ {τ Δ} {m : Memory Δ} -> (c : CTerm τ) -> IsValue c -> NormalForm m c
valueNotRedex .(Γ , （）) (Γ , （）) (Step (Pure ()))
valueNotRedex .(Γ , True) (Γ , True) (Step (Pure ()))
valueNotRedex .(Γ , False) (Γ , False) (Step (Pure ()))
valueNotRedex .(Γ , Abs t) (Γ , Abs t) (Step (Pure ()))
valueNotRedex .(Γ , ξ) (Γ , ξ) (Step (Pure ()))
valueNotRedex .(Γ , Mac t) (Γ , Mac t) (Step (Pure ()))
valueNotRedex .(Γ , Macₓ e) (Γ , Macₓ e) (Step (Pure ()))
valueNotRedex .(Γ , Res t) (Γ , Res t) (Step (Pure ()))
valueNotRedex .(Γ , Resₓ e) (Γ , Resₓ e) (Step (Pure ()))
valueNotRedex .(Γ , Ref α) (Γ , Ref α) (Step (Pure ()))

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

determinismMixedC : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> c₂ ≡ c₃
determinismMixedC (AppL s₁) (Pure s₂) = determinism⇝ (AppL s₁) s₂
determinismMixedC Beta (Pure s₁) = determinism⇝ Beta s₁
determinismMixedC Lookup (Pure s) = determinism⇝ Lookup s
determinismMixedC Dist-$ (Pure s₁) = determinism⇝ Dist-$ s₁
determinismMixedC Dist-If (Pure s) = determinism⇝ Dist-If s
determinismMixedC (IfCond s₁) (Pure s) = determinism⇝ (IfCond s₁) s
determinismMixedC IfTrue (Pure s) = determinism⇝ IfTrue s
determinismMixedC IfFalse (Pure s) = determinism⇝ IfFalse s
determinismMixedC Dist-∙ (Pure s) = determinism⇝ Dist-∙ s
determinismMixedC Hole (Pure s) = determinism⇝ Hole s

determinismC : ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> c₂ ≡ c₃
determinismC (Pure s₁) s₂ = determinismMixedC s₁ s₂
determinismC s₁ (Pure s₂) = P.sym (determinismMixedC s₂ s₁)
determinismC Return Return = refl
determinismC Dist->>= Dist->>= = refl
determinismC (BindCtx s₁) (BindCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (BindCtx (Pure ())) Bind
determinismC (BindCtx (Pure ())) BindEx
determinismC Bind (BindCtx (Pure ()))
determinismC Bind Bind = refl
determinismC BindEx (BindCtx (Pure ()))
determinismC BindEx BindEx = refl
determinismC Throw Throw = refl
determinismC Dist-Catch Dist-Catch = refl
determinismC (CatchCtx s₁) (CatchCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (CatchCtx (Pure ())) Catch
determinismC (CatchCtx (Pure ())) CatchEx
determinismC Catch (CatchCtx (Pure ()))
determinismC Catch Catch = refl
determinismC CatchEx (CatchCtx (Pure ()))
determinismC CatchEx CatchEx = refl
determinismC (label p) (label .p) = refl
determinismC (Dist-unlabel p) (Dist-unlabel .p) = refl
determinismC (unlabel p) (unlabel .p) = refl
determinismC (unlabel p) (unlabelCtx .p (Pure ()))
determinismC (unlabelCtx p (Pure ())) (unlabel .p)
determinismC (unlabelCtx p (Pure ())) (unlabelEx .p)
determinismC (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (unlabelEx p) (unlabelEx .p) = refl
determinismC (unlabelEx p) (unlabelCtx .p (Pure ()))
determinismC (Dist-join p) (Dist-join .p) = refl
determinismC (joinCtx p s₁) (joinCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (joinCtx p (Pure ())) (join .p)
determinismC (joinCtx p (Pure ())) (joinEx .p)
determinismC (join p) (joinCtx .p (Pure ()))
determinismC (join p) (join .p) = refl
determinismC (joinEx p) (joinCtx .p (Pure ()))
determinismC (joinEx p) (joinEx .p) = refl
determinismC (new p) (new .p) = refl
determinismC (Dist-write p) (Dist-write .p) = refl
determinismC (Dist-read p) (Dist-read .p) = refl
determinismC (writeCtx p s₁) (writeCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (writeCtx p (Pure ())) (write .p r)
determinismC (write p r) (writeCtx .p (Pure ()))
determinismC (write p i) (write .p j) = refl
determinismC (readCtx p s₁) (readCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (readCtx p (Pure ())) (read .p r)
determinismC (read p i) (readCtx .p (Pure ()))
determinismC (read p i) (read .p j) rewrite uniqueIx i j = refl

determinismMixedM : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> m₁ ≅ m₂
determinismMixedM (AppL s₁) (Pure s₂) = refl
determinismMixedM Beta (Pure x₁) = refl
determinismMixedM Lookup (Pure s₂) = refl
determinismMixedM Dist-$ (Pure s₂) = refl
determinismMixedM Dist-If (Pure s₂) = refl
determinismMixedM (IfCond s₁) (Pure s₂) = refl
determinismMixedM IfTrue (Pure s₂) = refl
determinismMixedM IfFalse (Pure s₂) = refl
determinismMixedM Dist-∙ (Pure s₂) = refl
determinismMixedM Hole (Pure s₂) = refl

determinismM : ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> m₂ ≅ m₃
determinismM (Pure s₁) s₂ = determinismMixedM  s₁ s₂
determinismM s₁ (Pure s₂) = H.sym (determinismMixedM s₂ s₁)
determinismM Return Return = refl
determinismM Dist->>= Dist->>= = refl
determinismM (BindCtx s₁) (BindCtx s₂) = determinismM s₁ s₂
determinismM (BindCtx (Pure ())) Bind
determinismM (BindCtx (Pure ())) BindEx
determinismM Bind (BindCtx (Pure ()))
determinismM Bind Bind = refl
determinismM BindEx (BindCtx (Pure ()))
determinismM BindEx BindEx = refl
determinismM Throw Throw = refl
determinismM Dist-Catch Dist-Catch = refl
determinismM (CatchCtx s₁) (CatchCtx s₂) = determinismM s₁ s₂
determinismM (CatchCtx (Pure ())) Catch
determinismM (CatchCtx (Pure ())) CatchEx
determinismM Catch (CatchCtx (Pure ()))
determinismM Catch Catch = refl
determinismM CatchEx (CatchCtx (Pure ()))
determinismM CatchEx CatchEx = refl
determinismM (label p) (label .p) = refl
determinismM (Dist-unlabel p) (Dist-unlabel .p) = refl
determinismM (unlabel p) (unlabel .p) = refl
determinismM (unlabel p) (unlabelCtx .p (Pure ()))
determinismM (unlabelCtx p (Pure ())) (unlabel .p)
determinismM (unlabelCtx p (Pure ())) (unlabelEx .p)
determinismM (unlabelCtx p s₁) (unlabelCtx .p s₂) = determinismM s₁ s₂
determinismM (unlabelEx p) (unlabelEx .p) = refl
determinismM (unlabelEx p) (unlabelCtx .p (Pure ()))
determinismM (Dist-join p) (Dist-join .p) = refl
determinismM (joinCtx p s₁) (joinCtx .p s₂) = determinismM s₁ s₂
determinismM (joinCtx p (Pure ())) (join .p)
determinismM (joinCtx p (Pure ())) (joinEx .p)
determinismM (join p) (joinCtx .p (Pure ()))
determinismM (join p) (join .p) = refl
determinismM (joinEx p) (joinCtx .p (Pure ()))
determinismM (joinEx p) (joinEx .p) = refl
determinismM (new p) (new .p) = refl
determinismM (Dist-write p) (Dist-write .p) = refl
determinismM (Dist-read p) (Dist-read .p) = refl
determinismM (writeCtx p s₁) (writeCtx .p s₂) = determinismM s₁ s₂
determinismM (writeCtx p (Pure ())) (write .p r)
determinismM (write p r) (writeCtx .p (Pure ()))
determinismM (write p i) (write .p j) rewrite uniqueIx i j = refl
determinismM (readCtx p s₁) (readCtx .p s₂) = determinismM s₁ s₂
determinismM (readCtx p (Pure ())) (read .p r)
determinismM (read p i) (readCtx .p (Pure ()))
determinismM (read p i) (read .p j) = refl

determinism :  ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> m₂ ≅ m₃ × c₂ ≡ c₃
determinism s₁ s₂ = (determinismM s₁ s₂) , (determinismC s₁ s₂)

preservation : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {τ : Ty} {c₁ c₂ : CTerm τ} ->
               ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂ × τ ≡ τ
preservation s = context⊆ s , refl
