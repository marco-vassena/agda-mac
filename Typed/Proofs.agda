module Typed.Proofs where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as P

open import Typed.Semantics
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

-- Value and Redex are mutually exclusive. A term is either a value or a redex, but not both.
valueNotRedex : ∀ {τ ls} {s : Store ls} -> (c : CTerm τ) -> IsValue c -> NormalForm s c
valueNotRedex .（） （） (Step (Pure ()))
valueNotRedex .True True (Step (Pure ()))
valueNotRedex .False False (Step (Pure ()))
valueNotRedex .(Abs t) (Abs t) (Step (Pure ()))
valueNotRedex .ξ ξ (Step (Pure ()))
valueNotRedex .(Mac t) (Mac t) (Step (Pure ()))
valueNotRedex .(Macₓ e) (Macₓ e) (Step (Pure ()))
valueNotRedex .(Res t) (Res t) (Step (Pure ()))
valueNotRedex .(Resₓ e) (Resₓ e) (Step (Pure ()))
valueNotRedex (suc n') (suc n) (Step (Pure ()))
valueNotRedex .zero zero (Step (Pure ()))

data PureRedex {τ : Ty} (t : CTerm τ) : Set where
  Step : ∀ {t' : CTerm τ} -> t ⇝ t' -> PureRedex t

valueNotRedex⇝ : ∀ {τ} {c₁ : CTerm τ} -> IsValue c₁ -> ¬ (PureRedex c₁)
valueNotRedex⇝ （） (Step ())
valueNotRedex⇝ True (Step ())
valueNotRedex⇝ False (Step ())
valueNotRedex⇝ (Abs t) (Step ())
valueNotRedex⇝ ξ (Step ())
valueNotRedex⇝ (Mac t) (Step ())
valueNotRedex⇝ (Macₓ e) (Step ())
valueNotRedex⇝ (Res t) (Step ())
valueNotRedex⇝ (Resₓ e) (Step ())
valueNotRedex⇝ zero (Step ())
valueNotRedex⇝ (suc isV) (Step ())

-- The pure small step semantics is deterministic.
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
determinism⇝ fmap (fmapCtx₁ ())
determinism⇝ fmap (fmapCtx₂ ())
determinism⇝ fmap fmap = refl
determinism⇝ fmapEx (fmapCtx₂ ())
determinism⇝ fmapEx fmapEx = refl
determinism⇝ (fmapCtx₁ s₁) (fmapCtx₁ s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (fmapCtx₁ ()) (fmapCtx₂ s₂)
determinism⇝ (fmapCtx₁ ()) fmap
determinism⇝ (fmapCtx₂ ()) (fmapCtx₁ s₂)
determinism⇝ (fmapCtx₂ s₁) (fmapCtx₂ s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (fmapCtx₂ ()) fmap
determinism⇝ (fmapCtx₂ ()) fmapEx
determinism⇝ fmap∙ (fmapCtx₁∙ ())
determinism⇝ fmap∙ (fmapCtx₂∙ ())
determinism⇝ fmap∙ fmap∙ = refl
determinism⇝ fmapEx∙ (fmapCtx₁∙ ())
determinism⇝ fmapEx∙ (fmapCtx₂∙ ())
determinism⇝ fmapEx∙ fmapEx∙ = refl
determinism⇝ (fmapCtx₁∙ s₁) (fmapCtx₁∙ s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (fmapCtx₁∙ ()) (fmapCtx₂∙ s₂)
determinism⇝ (fmapCtx₁∙ ()) fmap∙
determinism⇝ (fmapCtx₁∙ ()) fmapEx∙
determinism⇝ (fmapCtx₂∙ s₁) (fmapCtx₁∙ ())
determinism⇝ (fmapCtx₂∙ s₁) (fmapCtx₂∙ s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (fmapCtx₂∙ ()) fmap∙
determinism⇝ (fmapCtx₂∙ ()) fmapEx∙
determinism⇝ (relabelCtx p s₁) (relabelCtx .p s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (relabelCtx p ()) (relabel .p)
determinism⇝ (relabelCtx p ()) (relabelEx .p)
determinism⇝ (relabel p) (relabelCtx .p ())
determinism⇝ (relabel p) (relabel .p) = refl
determinism⇝ (relabelEx p) (relabelCtx .p ())
determinism⇝ (relabelEx p) (relabelEx .p) = refl
determinism⇝ (relabelCtx∙ p s₁) (relabelCtx∙ .p s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (relabelCtx∙ p ()) (relabel∙ .p)
determinism⇝ (relabelCtx∙ p ()) (relabelEx∙ .p)
determinism⇝ (relabel∙ p) (relabelCtx∙ .p ())
determinism⇝ (relabel∙ p) (relabel∙ .p) = refl
determinism⇝ (relabelEx∙ p) (relabelCtx∙ .p ())
determinism⇝ (relabelEx∙ p) (relabelEx∙ .p) = refl
determinism⇝ Hole Hole = refl

determinismMixedC : ∀ {ls τ} {s₁ s₂ : Store ls} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₃ ⟩ -> c₂ ≡ c₃
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
determinismMixedC fmap (Pure s₂) = determinism⇝ fmap s₂
determinismMixedC fmapEx (Pure s₂) = determinism⇝ fmapEx s₂
determinismMixedC (fmapCtx₁ s₁) (Pure s₂) = determinism⇝ (fmapCtx₁ s₁) s₂
determinismMixedC (fmapCtx₂ s₁) (Pure s₂) = determinism⇝ (fmapCtx₂ s₁) s₂
determinismMixedC fmap∙ (Pure s₂) = determinism⇝ fmap∙ s₂
determinismMixedC fmapEx∙ (Pure s₂) = determinism⇝ fmapEx∙ s₂
determinismMixedC (fmapCtx₁∙ s₁) (Pure s₂) = determinism⇝ (fmapCtx₁∙ s₁) s₂
determinismMixedC (fmapCtx₂∙ s₁) (Pure s₂) = determinism⇝ (fmapCtx₂∙ s₁) s₂
determinismMixedC (relabelCtx p s₂) (Pure x) = determinism⇝ (relabelCtx p s₂) x
determinismMixedC (relabel p) (Pure s₂) = determinism⇝ (relabel p) s₂ 
determinismMixedC (relabelEx p) (Pure s₂) = determinism⇝ (relabelEx p) s₂
determinismMixedC (relabelCtx∙ p s₁) (Pure s₂) = determinism⇝ (relabelCtx∙ p s₁) s₂
determinismMixedC (relabel∙ p) (Pure s₂) = determinism⇝ (relabel∙ p) s₂
determinismMixedC (relabelEx∙ p) (Pure s₂) = determinism⇝ (relabelEx∙ p) s₂

-- The small-step semantics for programs is deterministic.
determinismC : ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₃ ∥ c₃ ⟩ -> c₂ ≡ c₃

-- Store determinism for the small-step semantics of stores.
determinismS : ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₃ ∥ c₃ ⟩ -> s₂ ≡ s₃

-- Determinism naturally extends to the transitive reflexive closure of the small step semantics.
determinismC⋆ : ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ c₂ ⟩ -> IsValue c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₃ ∥ c₃ ⟩ -> IsValue c₃ -> c₂ ≡ c₃
determinismC⋆ [] isV₁ [] isV₂ = refl
determinismC⋆ [] isV₁ (x ∷ ss₂) isV₂ = ⊥-elim (valueNotRedex _ isV₁ (Step x))
determinismC⋆ (x ∷ ss₁) isV₁ [] isV₂ = ⊥-elim (valueNotRedex _ isV₂ (Step x))
determinismC⋆ (s₁ ∷ ss₁) isV₁ (s₂ ∷ ss₂) isV₂
  rewrite determinismC s₁ s₂ | determinismS s₁ s₂ | determinismC⋆ ss₁ isV₁ ss₂ isV₂ = refl


nonDeterminismC-⊥ :  ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                     ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₃ ∥ c₃ ⟩ -> ¬ (c₂ ≡ c₃) -> ⊥
nonDeterminismC-⊥ s₁ s₂ ¬p = ⊥-elim (¬p (determinismC s₁ s₂))                    

nonDeterminismC⋆-⊥ :  ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                      ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ c₂ ⟩ -> IsValue c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₃ ∥ c₃ ⟩ -> IsValue c₃ -> ¬ (c₂ ≡ c₃) -> ⊥
nonDeterminismC⋆-⊥ [] isV₁ [] isV₂ ¬p = ¬p refl
nonDeterminismC⋆-⊥ [] isV₁ (x ∷ ss₂) isV₂ ¬p = ⊥-elim (valueNotRedex _ isV₁ (Step x))
nonDeterminismC⋆-⊥ (x ∷ ss₁) isV₁ [] isV₂ ¬p = ⊥-elim (valueNotRedex _ isV₂ (Step x))
nonDeterminismC⋆-⊥ (s₁ ∷ ss₁) isV₁ (s₂ ∷ ss₂) isV₂ ¬p
  rewrite determinismC s₁ s₂ | determinismS s₁ s₂ = nonDeterminismC⋆-⊥ ss₁ isV₁ ss₂ isV₂ ¬p

determinismC (Pure s₁) s₂ = determinismMixedC s₁ s₂
determinismC s₁ (Pure s₂) = P.sym (determinismMixedC s₂ s₁)
determinismC (BindCtx s₁) (BindCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (CatchCtx s₁) (CatchCtx s₂) rewrite determinismC s₁ s₂ = refl
determinismC (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (join p (BigStep isV₁ ss₁)) (join .p (BigStep isV₂ ss₂)) with determinismC⋆ ss₁ isV₁ ss₂ isV₂
determinismC (join p (BigStep isV₁ ss₁)) (join .p (BigStep isV₂ ss₂)) | refl = refl
determinismC (join p (BigStep isV₁ ss₁)) (joinEx .p (BigStep isV₂ ss₂)) = ⊥-elim (nonDeterminismC⋆-⊥ ss₁ isV₁ ss₂ isV₂ (λ ()))
determinismC (joinEx p (BigStep isV₁ ss₁)) (joinEx .p (BigStep isV₂ ss₂)) with determinismC⋆  ss₁ isV₁ ss₂ isV₂
determinismC (joinEx p (BigStep isV₁ ss₁)) (joinEx .p (BigStep isV₂ ss₂)) | refl = refl
determinismC (joinEx p (BigStep isV₁ ss₁)) (join .p (BigStep isV₂ ss₂)) = ⊥-elim (nonDeterminismC⋆-⊥ ss₁ isV₁ ss₂ isV₂ (λ ()))
determinismC {s₁ = s₁} (new p q₁) (new .p q₂) rewrite store-unique s₁ q₁ q₂ = refl
determinismC (writeCtx p s₁) (writeCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (writeCtx p (Pure ())) (write .p q r)
determinismC (write p q r) (writeCtx .p (Pure ()))
determinismC (write p q₁ r₁) (write .p q₂ r₂) = refl
determinismC (writeEx p q₁ r₁) (writeEx .p q₂ r₂) = refl
determinismC (writeEx p q₁ r₁) (writeCtx .p (Pure ()))
determinismC (writeCtx p (Pure ())) (writeEx .p q₁ r₁)
determinismC (readCtx p s₁) (readCtx .p s₂) rewrite determinismC s₁ s₂ = refl
determinismC (readCtx p (Pure ())) (read .p q r)
determinismC (read p q i) (readCtx .p (Pure ()))
determinismC {s₁ = s₁} (read p q₁ r₁) (read .p q₂ r₂) rewrite store-unique s₁ q₁ q₂ | index-unique r₁ r₂ = refl
determinismC (readEx p) (readEx .p) = refl
determinismC (readEx p) (readCtx .p (Pure ()))
determinismC (readCtx p (Pure ())) (readEx .p)

determinismMixedS : ∀ {ls τ} {s₁ s₂ : Store ls} {c₁ c₂ c₃ : CTerm τ} -> 
                   c₁ ⇝ c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₃ ⟩ -> s₁ ≡ s₂
determinismMixedS (AppL s₁) (Pure x₁) = refl
determinismMixedS Beta (Pure x₁) = refl
determinismMixedS (IfCond s₁) (Pure x) = refl
determinismMixedS IfTrue (Pure x) = refl
determinismMixedS IfFalse (Pure x) = refl
determinismMixedS Return (Pure x) = refl
determinismMixedS Throw (Pure x) = refl
determinismMixedS Bind (Pure x) = refl
determinismMixedS Bind (BindCtx (Pure ()))
determinismMixedS BindEx (Pure x) = refl
determinismMixedS BindEx (BindCtx (Pure ()))
determinismMixedS Catch (Pure x) = refl
determinismMixedS Catch (CatchCtx (Pure ()))
determinismMixedS CatchEx (Pure x) = refl
determinismMixedS CatchEx (CatchCtx (Pure ()))
determinismMixedS (label p) (Pure (label .p)) = refl
determinismMixedS (unlabel p) (Pure x) = refl
determinismMixedS (unlabel p) (unlabelCtx .p (Pure ()))
determinismMixedS (unlabelEx p) (Pure x) = refl
determinismMixedS (unlabelEx p) (unlabelCtx .p (Pure ()))
determinismMixedS Hole (Pure Hole) = refl
determinismMixedS (relabelCtx p s₁) (Pure s₂) = refl
determinismMixedS (relabel p) (Pure s₂) = refl
determinismMixedS (relabelEx p) (Pure s₂) = refl 
determinismMixedS (relabelCtx∙ p s₁) (Pure s₂) = refl
determinismMixedS (relabel∙ p) (Pure s₂) = refl
determinismMixedS (relabelEx∙ p) (Pure s₂) = refl
determinismMixedS fmap (Pure s₂) = refl
determinismMixedS fmapEx (Pure s₂) = refl
determinismMixedS (fmapCtx₁ s₁) (Pure s₂) = refl
determinismMixedS (fmapCtx₂ s₁) (Pure s₂) = refl
determinismMixedS fmap∙ (Pure s₂) = refl
determinismMixedS fmapEx∙ (Pure s₂) = refl
determinismMixedS (fmapCtx₁∙ s₁) (Pure s₂) = refl
determinismMixedS (fmapCtx₂∙ s₁) (Pure s₂) = refl

determinismS⋆ : ∀ {τ ls} {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
                 ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ c₂ ⟩ -> IsValue c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₃ ∥ c₃ ⟩ -> IsValue c₃ -> s₂ ≡ s₃
determinismS⋆ [] isV₁ [] isV₂ = refl
determinismS⋆ [] isV₁ (x ∷ ss₂) isV₂ = ⊥-elim (valueNotRedex _ isV₁ (Step x))
determinismS⋆ (x ∷ ss₁) isV₁ [] isV₂ = ⊥-elim (valueNotRedex _ isV₂ (Step x))
determinismS⋆ (s₁ ∷ ss₁) isV₁ (s₂ ∷ ss₂) isV₂
  rewrite determinismS s₁ s₂ | determinismC s₁ s₂ | determinismS⋆ ss₁ isV₁ ss₂ isV₂ =  refl

determinismS (Pure s₁) s₂ = determinismMixedS  s₁ s₂
determinismS s₁ (Pure s₂) = sym (determinismMixedS s₂ s₁)
determinismS (BindCtx s₁) (BindCtx s₂) = determinismS s₁ s₂
determinismS (CatchCtx s₁) (CatchCtx s₂) = determinismS s₁ s₂
determinismS (unlabelCtx p s₁) (unlabelCtx .p s₂) = determinismS s₁ s₂
determinismS (join p (BigStep isV₁ ss₁)) (join .p (BigStep isV₂ ss₂)) = determinismS⋆ ss₁ isV₁ ss₂ isV₂
determinismS (join p (BigStep isV₁ ss₁)) (joinEx .p (BigStep isV₂ ss₂)) = ⊥-elim (nonDeterminismC⋆-⊥ ss₁ isV₁ ss₂ isV₂ (λ ()))
determinismS (joinEx p (BigStep isV₁ ss₁)) (joinEx .p (BigStep isV₂ ss₂)) = determinismS⋆ ss₁ isV₁ ss₂ isV₂
determinismS (joinEx p (BigStep isV₁ ss₁)) (join .p (BigStep isV₂ ss₂)) = ⊥-elim (nonDeterminismC⋆-⊥ ss₁ isV₁ ss₂ isV₂ (λ ()))
determinismS {s₁ = s} (new p q₁) (new .p q₂) rewrite store-unique s q₁ q₂ = refl
determinismS (writeCtx p s₁) (writeCtx .p s₂) = determinismS s₁ s₂
determinismS (writeCtx p (Pure ())) (write .p q r)
determinismS (write p q r) (writeCtx .p (Pure ()))
determinismS {s₁ = s} (write p q₁ r₁) (write .p q₂ r₂) rewrite store-unique s q₁ q₂ | index-unique r₁ r₂ = refl
determinismS (writeEx p q₁ r₁) (writeEx .p q₂ r₂) = refl
determinismS (writeEx p q r) (writeCtx .p (Pure ()))
determinismS (writeCtx p (Pure ())) (writeEx .p q r)
determinismS (readCtx p s₁) (readCtx .p s₂) = determinismS s₁ s₂
determinismS (readCtx p (Pure ())) (read .p q r)
determinismS (read p q r) (readCtx .p (Pure ()))
determinismS (read p q₁ r₁) (read .p q₂ r₂) = refl
determinismS (readEx p) (readEx .p) = refl
determinismS (readEx p) (readCtx .p (Pure ()))
determinismS (readCtx p (Pure ())) (readEx .p)

-- The general statement of determinism.
determinism :  ∀ {τ ls} {p₁ p₂ p₃ : Program τ ls} ->
                 p₁ ⟼ p₂ -> p₁ ⟼ p₃ -> p₂ ≡ p₃
determinism {p₁ = ⟨ s₁ ∥ c₁ ⟩} {⟨ s₂ ∥ c₂ ⟩} {⟨ s₃ ∥ c₃ ⟩} st₁ st₂
  rewrite determinismS st₁ st₂ | determinismC st₁ st₂ = refl 

preservation : ∀ {ls} {s₁ s₂ : Store ls} {τ : Ty} {c₁ c₂ : CTerm τ} -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> τ ≡ τ
preservation s = refl
