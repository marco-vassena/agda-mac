module Typed.Proofs where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as P

open import Typed.Semantics
open import Typed.Valid

-- A closed term with valid references with respect to the given memory context
-- either can be reduced further or it is a value.
progress : ∀ {τ Δᵐ} {{m : Memory Δᵐ}} (c : CTerm τ) -> Valid Δᵐ c -> (Redex m c) ⊎ (IsValue c)
progress （） v = inj₂ （）
progress True v = inj₂ True
progress False v = inj₂ False
progress (Var ()) v
progress (Abs c) v = inj₂ (Abs c)
progress {{m}} (App c c₁) (App v v₁) with progress {{m}} c v
progress (App c c₁) (App v v₁) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (AppL x)))
progress (App .∙ c₁) (App v v₁) | inj₁ (Step (Hole x)) = inj₁ (Step (Pure (AppL Hole)))
progress (App .(Abs t) c₁) (App v v₁) | inj₂ (Abs t) = inj₁ (Step (Pure Beta))
progress {{m}} (If c Then t Else c₂) (If v Then v₁ Else v₂) with progress {{m}} c v
progress (If c Then t Else c₃) (If v Then v₁ Else v₂) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (IfCond x)))
progress (If .∙ Then t Else c₃) (If v Then v₁ Else v₂) | inj₁ (Step (Hole x)) = inj₁ (Step (Pure (IfCond Hole)))
progress (If .True Then t Else c₂) (If v Then v₁ Else v₂) | inj₂ True = inj₁ (Step (Pure IfTrue))
progress (If .False Then t Else c₂) (If v Then v₁ Else v₂) | inj₂ False = inj₁ (Step (Pure IfFalse))
progress (Return c) v = inj₁ (Step (Pure Return))
progress {{m}} (c >>= c₁) (v >>= v₁) with progress {{m}} c v
progress (c >>= c₁) (v >>= v₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress (.(Mac t) >>= c₁) (v >>= v₁) | inj₂ (Mac t) = inj₁ (Step (Pure Bind))
progress (.(Macₓ e) >>= c₁) (v >>= v₁) | inj₂ (Macₓ e) = inj₁ (Step (Pure BindEx))
progress ξ v = inj₂ ξ
progress (Throw c) v = inj₁ (Step (Pure Throw))
progress {{m}} (Catch c c₁) (Catch v v₁) with progress {{m}} c v
progress (Catch c c₁) (Catch v v₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch .(Mac t) c₁) (Catch v v₁) | inj₂ (Mac t) = inj₁ (Step (Pure Catch))
progress (Catch .(Macₓ e) c₁) (Catch v v₁) | inj₂ (Macₓ e) = inj₁ (Step (Pure CatchEx))
progress (Mac c) v = inj₂ (Mac c)
progress (Macₓ c) v = inj₂ (Macₓ c)
progress (Res c) v = inj₂ (Res c)
progress (Resₓ c) v = inj₂ (Resₓ c)
progress (label x c) (label .x v) = inj₁ (Step (Pure (label x)))
progress {{m}} (unlabel x c) (unlabel .x v) with progress {{m}} c v
progress (unlabel x₁ c) (unlabel .x₁ v) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x₁ x))
progress (unlabel x .(Res t)) (unlabel .x v) | inj₂ (Res t) = inj₁ (Step (Pure (unlabel x)))
progress (unlabel x .(Resₓ e)) (unlabel .x v) | inj₂ (Resₓ e) = inj₁ (Step (Pure (unlabelEx x)))
progress {{m}} (join x c) (join .x v) with progress {{m}} c v
progress (join x₁ c) (join .x₁ v) | inj₁ (Step x) = inj₁ (Step (joinCtx x₁ x))
progress (join x .(Mac t)) (join .x v) | inj₂ (Mac t) = inj₁ (Step (join x))
progress (join x .(Macₓ e)) (join .x v) | inj₂ (Macₓ e) = inj₁ (Step (joinEx x))
progress (Ref x) v = inj₂ (Ref x)
progress {{m}} (read x c) (read .x v) with progress {{m}} c v
progress (read x₁ c) (read .x₁ v) | inj₁ (Step x) = inj₁ (Step (readCtx x₁ x))
progress (read x .(Ref n)) (read .x (Ref x₁)) | inj₂ (Ref n) = inj₁ (Step (read x x₁))
progress {{m}} (write x c c₁) (write .x v v₁) with progress {{m}} c v
progress (write x₁ c c₁) (write .x₁ v v₁) | inj₁ (Step x) = inj₁ (Step (writeCtx x₁ x))
progress (write x .(Ref n) c₁) (write .x (Ref x₁) v₁) | inj₂ (Ref n) = inj₁ (Step (write x x₁))
progress (new x c) (new .x v) = inj₁ (Step (new x))
progress ∙ v = inj₁ (Step (Pure Hole))

valueNotRedex : ∀ {τ Δ} {m : Memory Δ} -> (c : CTerm τ) -> IsValue c -> NormalForm m c
valueNotRedex .（） （） (Step (Pure ()))
valueNotRedex .True True (Step (Pure ()))
valueNotRedex .False False (Step (Pure ()))
valueNotRedex .(Abs t) (Abs t) (Step (Pure ()))
valueNotRedex .ξ ξ (Step (Pure ()))
valueNotRedex .(Mac t) (Mac t) (Step (Pure ()))
valueNotRedex .(Macₓ e) (Macₓ e) (Step (Pure ()))
valueNotRedex .(Res t) (Res t) (Step (Pure ()))
valueNotRedex .(Resₓ e) (Resₓ e) (Step (Pure ()))
valueNotRedex .(Ref n) (Ref n) (Step (Pure ()))

determinism⇝ : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃
determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (AppL ()) Beta
determinism⇝ Beta (AppL ())
determinism⇝ Beta Beta = refl
determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (IfCond ()) IfTrue
determinism⇝ (IfCond ()) IfFalse
determinism⇝ IfTrue (IfCond ())
determinism⇝ IfTrue IfTrue = refl
determinism⇝ IfFalse (IfCond ())
determinism⇝ IfFalse IfFalse = refl
determinism⇝ Return Return = refl
determinism⇝ Throw Throw = refl
determinism⇝ Bind Bind = refl
determinism⇝ BindEx BindEx = refl
determinism⇝ Catch Catch = refl
determinism⇝ CatchEx CatchEx = refl
determinism⇝ (label p) (label .p) = refl
determinism⇝ (unlabel p) (unlabel .p) = refl
determinism⇝ (unlabelEx p) (unlabelEx .p) = refl
determinism⇝ Hole Hole = refl

determinismMixedC : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> c₂ ≡ c₃
determinismMixedC (AppL s₁) (Pure s₂) = determinism⇝ (AppL s₁) s₂
determinismMixedC Beta (Pure s₁) = determinism⇝ Beta s₁
determinismMixedC (IfCond s₁) (Pure s) = determinism⇝ (IfCond s₁) s
determinismMixedC IfTrue (Pure s) = determinism⇝ IfTrue s
determinismMixedC IfFalse (Pure s) = determinism⇝ IfFalse s
determinismMixedC Hole (Pure s) = determinism⇝ Hole s
determinismMixedC Return (Pure s) = determinism⇝ Return s
determinismMixedC Throw (Pure x) = determinism⇝ Throw x
determinismMixedC Bind (Pure x) = determinism⇝ Bind x
determinismMixedC Bind (BindCtx (Pure ()))
determinismMixedC BindEx (Pure x) = determinism⇝ BindEx x
determinismMixedC BindEx (BindCtx (Pure ()))
determinismMixedC Catch (Pure x) = determinism⇝ Catch x
determinismMixedC Catch (CatchCtx (Pure ()))
determinismMixedC CatchEx (Pure x) = determinism⇝ CatchEx x
determinismMixedC CatchEx (CatchCtx (Pure ()))
determinismMixedC (label p) (Pure x) = determinism⇝ (label p) x
determinismMixedC (unlabel p) (Pure x) = determinism⇝ (unlabel p) x
determinismMixedC (unlabel p) (unlabelCtx .p (Pure ()))
determinismMixedC (unlabelEx p) (Pure x) = determinism⇝ (unlabelEx p) x
determinismMixedC (unlabelEx p) (unlabelCtx .p (Pure ()))
determinismMixedC Hole (Hole x) = refl

determinismC : ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> c₂ ≡ c₃
determinismC (Pure s₁) s₂ = determinismMixedC s₁ s₂
determinismC s₁ (Pure s₂) = P.sym (determinismMixedC s₂ s₁)
determinismC (BindCtx s₁) (BindCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (CatchCtx s₁) (CatchCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (joinCtx p s₁) (joinCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (joinCtx p (Pure ())) (join .p)
determinismC (joinCtx p (Pure ())) (joinEx .p)
determinismC (join p) (joinCtx .p (Pure ()))
determinismC (join p) (join .p) = refl
determinismC (joinEx p) (joinCtx .p (Pure ()))
determinismC (joinEx p) (joinEx .p) = refl
determinismC (new p) (new .p) = refl
determinismC (writeCtx p s₁) (writeCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (writeCtx p (Pure ())) (write .p r)
determinismC (write p r) (writeCtx .p (Pure ()))
determinismC (write p i) (write .p j) = refl
determinismC (readCtx p s₁) (readCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (readCtx p (Pure ())) (read .p r)
determinismC (read p i) (readCtx .p (Pure ()))
determinismC (read p i) (read .p j) rewrite uniqueIx i j = refl
determinismC (Hole x) (Hole y) = refl

determinismMixedM : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> m₁ ≅ m₂
determinismMixedM (AppL s₁) (Pure x₁) = refl-≅
determinismMixedM Beta (Pure x₁) = refl-≅
determinismMixedM (IfCond s₁) (Pure x) = refl-≅
determinismMixedM IfTrue (Pure x) = refl-≅
determinismMixedM IfFalse (Pure x) = refl-≅
determinismMixedM Return (Pure x) = refl-≅
determinismMixedM Throw (Pure x) = refl-≅
determinismMixedM Bind (Pure x) = refl-≅
determinismMixedM Bind (BindCtx (Pure ()))
determinismMixedM BindEx (Pure x) = refl-≅
determinismMixedM BindEx (BindCtx (Pure ()))
determinismMixedM Catch (Pure x) = refl-≅
determinismMixedM Catch (CatchCtx (Pure ()))
determinismMixedM CatchEx (Pure x) = refl-≅
determinismMixedM CatchEx (CatchCtx (Pure ()))
determinismMixedM (label p) (Pure (label .p)) = refl-≅
determinismMixedM (unlabel p) (Pure x) = refl-≅
determinismMixedM (unlabel p) (unlabelCtx .p (Pure ()))
determinismMixedM (unlabelEx p) (Pure x) = refl-≅
determinismMixedM (unlabelEx p) (unlabelCtx .p (Pure ()))
determinismMixedM Hole (Pure Hole) = refl-≅
determinismMixedM Hole (Hole x) = hole

determinismM : ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> m₂ ≅ m₃
determinismM (Pure s₁) s₂ = determinismMixedM  s₁ s₂
determinismM s₁ (Pure s₂) = sym-≅ (determinismMixedM s₂ s₁)
determinismM (BindCtx s₁) (BindCtx s₂) = determinismM s₁ s₂
determinismM (CatchCtx s₁) (CatchCtx s₂) = determinismM s₁ s₂
determinismM (unlabelCtx p s₁) (unlabelCtx .p s₂) = determinismM s₁ s₂
determinismM (joinCtx p s₁) (joinCtx .p s₂) = determinismM s₁ s₂
determinismM (joinCtx p (Pure ())) (join .p)
determinismM (joinCtx p (Pure ())) (joinEx .p)
determinismM (join p) (joinCtx .p (Pure ()))
determinismM (join p) (join .p) = refl-≅
determinismM (joinEx p) (joinCtx .p (Pure ()))
determinismM (joinEx p) (joinEx .p) = refl-≅
determinismM (new p) (new .p) = refl-≅
determinismM (writeCtx p s₁) (writeCtx .p s₂) = determinismM s₁ s₂
determinismM (writeCtx p (Pure ())) (write .p r)
determinismM (write p r) (writeCtx .p (Pure ()))
determinismM (write p i) (write .p j) rewrite uniqueIx i j = refl-≅
determinismM (readCtx p s₁) (readCtx .p s₂) = determinismM s₁ s₂
determinismM (readCtx p (Pure ())) (read .p r)
determinismM (read p i) (readCtx .p (Pure ()))
determinismM (read p i) (read .p j) = refl-≅
determinismM (Hole x) (Hole y) = hole

determinism :  ∀ {τ Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₃ ∥ c₃ ⟩ -> m₂ ≅ m₃ × c₂ ≡ c₃
determinism s₁ s₂ = (determinismM s₁ s₂) , (determinismC s₁ s₂)

preservation : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {τ : Ty} {c₁ c₂ : CTerm τ} ->
               ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂ × τ ≡ τ
preservation s = context-⊆ s , refl
