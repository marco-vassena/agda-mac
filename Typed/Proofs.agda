
module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality as P

-- open import Typed.Valid

-- A closed term with valid references with respect to the given memory context
-- either can be reduced further or it is a value.
-- progress : ∀ {τ Δᵐ} {{m : Memory Δᵐ}} (c : CTerm τ) -> Valid Δᵐ c -> (Redex m c) ⊎ (IsValue c)
-- progress （） v = inj₂ （）
-- progress True v = inj₂ True
-- progress False v = inj₂ False
-- progress (Var ()) v
-- progress (Abs c) v = inj₂ (Abs c)
-- progress {{m}} (App c c₁) (App v v₁) with progress {{m}} c v
-- progress (App c c₁) (App v v₁) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (AppL x)))
-- progress (App .∙ c₁) (App v v₁) | inj₁ (Step (Hole x)) = inj₁ (Step (Pure (AppL Hole)))
-- progress (App .(Abs t) c₁) (App v v₁) | inj₂ (Abs t) = inj₁ (Step (Pure Beta))
-- progress {{m}} (If c Then t Else c₂) (If v Then v₁ Else v₂) with progress {{m}} c v
-- progress (If c Then t Else c₃) (If v Then v₁ Else v₂) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (IfCond x)))
-- progress (If .∙ Then t Else c₃) (If v Then v₁ Else v₂) | inj₁ (Step (Hole x)) = inj₁ (Step (Pure (IfCond Hole)))
-- progress (If .True Then t Else c₂) (If v Then v₁ Else v₂) | inj₂ True = inj₁ (Step (Pure IfTrue))
-- progress (If .False Then t Else c₂) (If v Then v₁ Else v₂) | inj₂ False = inj₁ (Step (Pure IfFalse))
-- progress (Return c) v = inj₁ (Step (Pure Return))
-- progress {{m}} (c >>= c₁) (v >>= v₁) with progress {{m}} c v
-- progress (c >>= c₁) (v >>= v₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
-- progress (.(Mac t) >>= c₁) (v >>= v₁) | inj₂ (Mac t) = inj₁ (Step (Pure Bind))
-- progress (.(Macₓ e) >>= c₁) (v >>= v₁) | inj₂ (Macₓ e) = inj₁ (Step (Pure BindEx))
-- progress ξ v = inj₂ ξ
-- progress (Throw c) v = inj₁ (Step (Pure Throw))
-- progress {{m}} (Catch c c₁) (Catch v v₁) with progress {{m}} c v
-- progress (Catch c c₁) (Catch v v₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
-- progress (Catch .(Mac t) c₁) (Catch v v₁) | inj₂ (Mac t) = inj₁ (Step (Pure Catch))
-- progress (Catch .(Macₓ e) c₁) (Catch v v₁) | inj₂ (Macₓ e) = inj₁ (Step (Pure CatchEx))
-- progress (Mac c) v = inj₂ (Mac c)
-- progress (Macₓ c) v = inj₂ (Macₓ c)
-- progress (Res c) v = inj₂ (Res c)
-- progress (Resₓ c) v = inj₂ (Resₓ c)
-- progress (label x c) (label .x v) = inj₁ (Step (Pure (label x)))
-- progress {{m}} (unlabel x c) (unlabel .x v) with progress {{m}} c v
-- progress (unlabel x₁ c) (unlabel .x₁ v) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x₁ x))
-- progress (unlabel x .(Res t)) (unlabel .x v) | inj₂ (Res t) = inj₁ (Step (Pure (unlabel x)))
-- progress (unlabel x .(Resₓ e)) (unlabel .x v) | inj₂ (Resₓ e) = inj₁ (Step (Pure (unlabelEx x)))
-- progress {{m}} (join x c) (join .x v) with progress {{m}} c v
-- progress (join x₁ c) (join .x₁ v) | inj₁ (Step x) = {!!} -- We need a progress⇓ lemma tailored for big step semantics
-- progress (join x .(Mac t)) (join .x v) | inj₂ (Mac t) = inj₁ (Step (join x (BigStep (Mac t) [])))
-- progress (join x .(Macₓ e)) (join .x v) | inj₂ (Macₓ e) = inj₁ (Step (joinEx x (BigStep (Macₓ e) [])))
-- progress (Ref x) v = inj₂ (Ref x)
-- progress {{m}} (read x c) (read .x v) with progress {{m}} c v
-- progress (read x₁ c) (read .x₁ v) | inj₁ (Step x) = inj₁ (Step (readCtx x₁ x))
-- progress (read x .(Ref n)) (read .x (Ref x₁)) | inj₂ (Ref n) = inj₁ (Step (read x x₁))
-- progress {{m}} (write x c c₁) (write .x v v₁) with progress {{m}} c v
-- progress (write x₁ c c₁) (write .x₁ v v₁) | inj₁ (Step x) = inj₁ (Step (writeCtx x₁ x))
-- progress (write x .(Ref n) c₁) (write .x (Ref x₁) v₁) | inj₂ (Ref n) = inj₁ (Step (write x x₁))
-- progress (new x c) (new .x v) = inj₁ (Step (new x))
-- progress ∙ v = inj₁ (Step (Pure Hole))

preservation : ∀ {ls} {s₁ s₂ : Store ls} {τ : Ty} {c₁ c₂ : CTerm τ} -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> τ ≡ τ
preservation s = refl
