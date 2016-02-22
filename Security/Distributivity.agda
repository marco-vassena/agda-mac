module Security.Distributivity where


open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Data.Product
open import Data.List as L hiding (drop ; _∷ʳ_ ; [_])

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ p₁ p₂ lₐ . if p₁ ⟼ p₂ then (εᵖ lₐ p₁) ⟼ (εᵖ lₐ p₂)

-- The program erasure function distributes over the small step semantics.
εᵖ-dist : ∀ {τ ls} {p₁ : Program ls τ} {p₂ : Program ls τ} ->
            (lₐ : Label) -> p₁ ⟼ p₂ -> εᵖ lₐ p₁ ⟼ εᵖ lₐ p₂

--------------------------------------------------------------------------------

-- The erasure function distributes over the pure term reduction.
ε-dist⇝ : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⇝ c₂ -> ε lₐ c₁ ⇝ ε lₐ c₂

-- The erasure function distributes over the pure term reduction of Mac computations.
ε-Mac-dist⇝ : ∀ {τ lᵈ} {c₁ c₂ : CTerm (Mac lᵈ τ)} (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) -> c₁ ⇝ c₂ -> ε-Mac lₐ x c₁ ⇝ ε-Mac lₐ x c₂
ε-Mac-dist⇝ lₐ (yes p) (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-Mac-dist⇝ {c₁ = App (Abs t) x} lₐ (yes p) Beta rewrite sym (ε-Mac-subst lₐ (yes p) x t) = Beta
ε-Mac-dist⇝ lₐ (yes p) (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-Mac-dist⇝ lₐ (yes p) IfTrue = IfTrue
ε-Mac-dist⇝ lₐ (yes p) IfFalse = IfFalse
ε-Mac-dist⇝ lₐ (yes p) Return = Return
ε-Mac-dist⇝ lₐ (yes p) Throw = Throw
ε-Mac-dist⇝ lₐ (yes p) Bind = Bind
ε-Mac-dist⇝ lₐ (yes p) BindEx = BindEx
ε-Mac-dist⇝ lₐ (yes p) Catch = Catch
ε-Mac-dist⇝ lₐ (yes p) CatchEx = CatchEx
ε-Mac-dist⇝ lₐ (yes p) (label {h = lʰ} p₁) with lʰ ⊑? lₐ
ε-Mac-dist⇝ lₐ (yes p₁) (label p₂) | yes p = label p₂
ε-Mac-dist⇝ lₐ (yes p) (label p₁) | no ¬p = label p₁
ε-Mac-dist⇝ lₐ (yes p) (unlabel {l = l} p₁) with l ⊑? lₐ
ε-Mac-dist⇝ lₐ (yes p₁) (unlabel p₂) | yes p = unlabel p₂
ε-Mac-dist⇝ lₐ (yes d⊑a) (unlabel l⊑d) | no ¬l⊑a = ⊥-elim (¬l⊑a (trans-⊑ l⊑d d⊑a))
ε-Mac-dist⇝ lₐ (yes d⊑a) (unlabelEx {l = l} l⊑d) with l ⊑? lₐ
ε-Mac-dist⇝ lₐ (yes d⊑a) (unlabelEx l⊑d) | yes p = unlabelEx l⊑d
ε-Mac-dist⇝ lₐ (yes d⊑a) (unlabelEx l⊑d) | no ¬l⊑a = ⊥-elim (¬l⊑a (trans-⊑ l⊑d d⊑a))
ε-Mac-dist⇝ lₐ (yes p) Hole = Hole
ε-Mac-dist⇝ {c₁ = c₁} {c₂} lₐ (no ¬p) s rewrite ε-Mac-CTerm≡∙ lₐ c₁ ¬p | ε-Mac-CTerm≡∙ lₐ c₂ ¬p = Hole

-- This proof is repetitive because, even though the erasure
-- function is defined with a default case for all non Mac lᵈ τ types
-- reasoning requires to explicitly pattern match on each of them.
ε-dist⇝ {Mac lᵈ τ} lₐ s = ε-Mac-dist⇝ lₐ (lᵈ ⊑? lₐ) s
ε-dist⇝ {（）} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {（）} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {（）} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {（）} lₐ IfTrue = IfTrue
ε-dist⇝ {（）} lₐ IfFalse = IfFalse
ε-dist⇝ {（）} lₐ Hole = Hole
ε-dist⇝ {Bool} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Bool} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Bool} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Bool} lₐ IfTrue = IfTrue
ε-dist⇝ {Bool} lₐ IfFalse = IfFalse
ε-dist⇝ {Bool} lₐ Hole = Hole
ε-dist⇝ {τ => τ₁} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {τ => τ₁} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {τ => τ₁} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {τ => τ₁} lₐ IfTrue = IfTrue
ε-dist⇝ {τ => τ₁} lₐ IfFalse = IfFalse
ε-dist⇝ {τ => τ₁} lₐ Hole = Hole
ε-dist⇝ {Res lᵈ τ} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Res lᵈ τ} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ IfTrue = IfTrue
ε-dist⇝ {Res lᵈ τ} lₐ IfFalse = IfFalse
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | yes p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | yes p₁ | yes p = fmapCtx₁ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | yes p | no ¬p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | no ¬p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | no ¬p | yes p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁ s) | no ¬p₁ | no ¬p = fmapCtx₁∙ (ε-dist⇝ lₐ s) 
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | yes p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | yes p₁ | yes p = fmapCtx₂ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | yes p | no ¬p = ⊥-elim (¬p p) 
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | no ¬p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | no ¬p | yes p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂ s) | no ¬p₁ | no ¬p = fmapCtx₂∙ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ fmap with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmap | yes p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmap {t = t} {x = x}) | yes p₁ | yes p rewrite sym (ε-subst lₐ x t) = fmap
ε-dist⇝ {Res lᵈ τ} lₐ fmap | yes p | no ¬p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ fmap | no ¬p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmap | no ¬p | yes p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ fmap | no ¬p₁ | no ¬p = fmap∙
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx  with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | yes p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | yes p₁ | yes p = fmapEx
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | yes p | no ¬p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | no ¬p with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | no ¬p | yes p = ⊥-elim (¬p p)
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx | no ¬p₁ | no ¬p = fmap∙
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₁∙ s) = fmapCtx₁∙ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂∙ s) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂∙ s) | yes p = fmapCtx₂∙ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (fmapCtx₂∙ s) | no ¬p = fmapCtx₂∙ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ fmap∙ with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmap∙ | yes p rewrite ε∙≡∙ {τ} {[]} lₐ = fmap∙
ε-dist⇝ {Res lᵈ τ} lₐ fmap∙ | no ¬p = fmap∙
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx∙ with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx∙ | yes p rewrite ε∙≡∙ {τ} {[]} lₐ = fmapEx∙
ε-dist⇝ {Res lᵈ τ} lₐ fmapEx∙ | no ¬p = fmap∙
ε-dist⇝ {Res lᵈ τ} lₐ (relabelCtx p s) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabelCtx p₁ s) | yes p = relabelCtx p₁ (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (relabelCtx p s) | no ¬p = relabelCtx∙ p (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (relabel {l = l} p) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel {l = l} p₁) | yes p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel p₂) | yes p₁ | yes p = relabel p₂
ε-dist⇝ {Res lᵈ τ} lₐ (relabel p₁) | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ p))
ε-dist⇝ {Res lᵈ τ} lₐ (relabel {l = l} p) | no ¬p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel p₁) | no ¬p | yes p = relabel∙ p₁
ε-dist⇝ {Res lᵈ τ} lₐ (relabel p) | no ¬p₁ | no ¬p = relabel∙ p
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx p) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx {l = l} p₁) | yes p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx p₂) | yes p₁ | yes p = relabelEx p₂
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx p₁) | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ p))
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx {l = l} p) | no ¬p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx p₁) | no ¬p | yes p = relabelEx∙ p₁
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx p) | no ¬p₁ | no ¬p = relabel∙ p
ε-dist⇝ {Res lᵈ τ} lₐ (relabelCtx∙ p s) = relabelCtx∙ p (ε-dist⇝ lₐ s)
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ p) with lᵈ ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ {l = l} p₁) | yes p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ p₂) | yes p₁ | yes p rewrite ε∙≡∙ {τ} {[]} lₐ = relabel∙ p₂
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ p₁) | yes p | no ¬p rewrite ε∙≡∙ {τ} {[]} lₐ = relabel∙ p₁
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ {l = l} p) | no ¬p with l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ p₁) | no ¬p | yes p = relabel∙ p₁
ε-dist⇝ {Res lᵈ τ} lₐ (relabel∙ p) | no ¬p₁ | no ¬p = relabel∙ p
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx∙ {l = l} p) with lᵈ ⊑? lₐ | l ⊑? lₐ
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx∙ p₂) | yes p | yes p₁ rewrite ε∙≡∙ {τ} {[]} lₐ = relabelEx∙ p₂
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx∙ p₁) | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ p))
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx∙ p₁) | no ¬p | yes p = relabelEx∙ p₁
ε-dist⇝ {Res lᵈ τ} lₐ (relabelEx∙ p) | no ¬p | no ¬p₁ = relabel∙ p
ε-dist⇝ {Res lᵈ τ} lₐ Hole = Hole
ε-dist⇝ {Exception} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Exception} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Exception} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Exception} lₐ IfTrue = IfTrue
ε-dist⇝ {Exception} lₐ IfFalse = IfFalse
ε-dist⇝ {Exception} lₐ Hole = Hole
ε-dist⇝ {Nat} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Nat} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Nat} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Nat} lₐ IfTrue = IfTrue
ε-dist⇝ {Nat} lₐ IfFalse = IfFalse
ε-dist⇝ {Nat} lₐ Hole = Hole

--------------------------------------------------------------------------------

ε-Mac-dist : ∀ {lᵈ τ ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm (Mac lᵈ τ)} (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) ->
                ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> ⟨ (εˢ lₐ s₁) ∥ ε-Mac lₐ x c₁ ⟩ ⟼ ⟨ εˢ lₐ s₂ ∥ ε-Mac lₐ x c₂ ⟩

ε-Mac-distₓ⋆ : ∀ {lᵈ τ ls} {s₁ s₂ : Store ls} {c₁ : CTerm (Mac lᵈ τ)} {e : CTerm Exception} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
              ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ (Macₓ e) ⟩ ->
              ⟨ εˢ lₐ s₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⟼⋆ ⟨ εˢ lₐ s₂ ∥ Macₓ (ε lₐ e) ⟩
ε-Mac-distₓ⋆ lₐ p [] = []
ε-Mac-distₓ⋆ lₐ p (s ∷ ss) = (ε-Mac-dist lₐ (yes p) s) ∷ (ε-Mac-distₓ⋆ lₐ p ss)

ε-Mac-distₓ⇓ : ∀ {lᵈ τ ls} {s₁ s₂ : Store ls} {c₁ : CTerm (Mac lᵈ τ)} {e : CTerm Exception} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
             ⟨ s₁ ∥ c₁ ⟩ ⇓ ⟨ s₂ ∥ Macₓ e ⟩ ->
             ⟨ εˢ lₐ  s₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⇓ ⟨ εˢ lₐ s₂ ∥ Macₓ (ε lₐ e) ⟩
ε-Mac-distₓ⇓ lₐ p (BigStep (Macₓ e) ss) = BigStep (Macₓ (ε lₐ e)) (ε-Mac-distₓ⋆ lₐ p ss)


ε-Mac-dist⋆ : ∀ {lᵈ τ ls} {s₁ s₂ : Store ls} {c₁ : CTerm (Mac lᵈ τ)} {c₂ : CTerm τ} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
              ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ (Mac c₂) ⟩ ->
              ⟨ εˢ lₐ s₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⟼⋆ ⟨ εˢ lₐ s₂ ∥ Mac (ε lₐ c₂) ⟩
ε-Mac-dist⋆ lₐ p [] = []
ε-Mac-dist⋆ lₐ p (s ∷ ss) = (ε-Mac-dist lₐ (yes p) s) ∷ (ε-Mac-dist⋆ lₐ p ss)


ε-Mac-dist⇓ : ∀ {lᵈ τ ls} {s₁ s₂ : Store ls} {c₁ : CTerm (Mac lᵈ τ)} {c₂ : CTerm τ} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
             ⟨ s₁ ∥ c₁ ⟩ ⇓ ⟨ s₂ ∥ Mac c₂ ⟩ ->
             ⟨ εˢ lₐ  s₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⇓ ⟨ εˢ lₐ s₂ ∥ Mac (ε lₐ c₂) ⟩
ε-Mac-dist⇓ lₐ p (BigStep (Mac c₂) ss) = BigStep (Mac (ε lₐ c₂)) (ε-Mac-dist⋆ lₐ p ss)

--------------------------------------------------------------------------------

εᵐ-new-≡ : ∀ {l lₐ τ} -> ¬ l ⊑ lₐ -> (m : Memory l) (c : CTerm τ) -> εᵐ lₐ (l ⊑? lₐ) m ≡ εᵐ lₐ (l ⊑? lₐ) (m ∷ʳ c)
εᵐ-new-≡ {l} {lₐ} ¬p m c with l ⊑? lₐ
εᵐ-new-≡ ¬p m c | yes p = ⊥-elim (¬p p)
εᵐ-new-≡ ¬p₁ m c | no ¬p = refl

εᵐ-write-≡ :  ∀ {l lₐ τ n} -> ¬ l ⊑ lₐ -> (m : Memory l) (r : TypedIx τ n m) (c : CTerm τ) -> εᵐ lₐ (l ⊑? lₐ) m ≡ εᵐ lₐ (l ⊑? lₐ) (m [ r ]≔ c)
εᵐ-write-≡ {l} {lₐ} ¬p m r c with l ⊑? lₐ
εᵐ-write-≡ ¬p m r c | yes p = ⊥-elim (¬p p)
εᵐ-write-≡ ¬p₁ m r c | no ¬p = refl 

--- Allocations to high, non-visible memories are canceled by the earsure function, because
--- high memory are collapsed to ∙.
εˢ-new-≡ : ∀ {l lₐ ls τ} -> ¬ (l ⊑ lₐ) -> (s : Store ls) (q : l ∈ ls) (c : CTerm τ) ->
               εˢ lₐ s ≡ εˢ lₐ (newˢ q s c)
εˢ-new-≡ ¬p [] () c
εˢ-new-≡ ¬p (m ∷ s) Here c rewrite εᵐ-new-≡ ¬p m c = refl
εˢ-new-≡ ¬p (x ∷ s) (There q) c rewrite εˢ-new-≡ ¬p s q c = refl

εˢ-write-≡ : ∀ {l lₐ ls n τ} -> ¬ (l ⊑ lₐ) -> (s : Store ls) (q : l ∈ ls) (r : TypedIx τ n (getMemory q s)) (c : CTerm τ) ->
               εˢ lₐ s ≡ εˢ lₐ (s [ q ][ r ]≔ c)
εˢ-write-≡ ¬p [] () r c
εˢ-write-≡ ¬p (m ∷ s) Here r c rewrite εᵐ-write-≡ ¬p m r c = refl
εˢ-write-≡ ¬p (x ∷ s) (There q) r c rewrite εˢ-write-≡ ¬p s q r c = refl               

-- TODO move to types.
-- TODO better name
lemma : ∀ {a b c} -> a ⊑ b -> ¬ (a ⊑ c) -> ¬ (b ⊑ c)
lemma a⊑b ¬a⊑c b⊑c = ⊥-elim (¬a⊑c (trans-⊑ a⊑b b⊑c))

-- A sensitive, non-visible computation can only affect high memories of the store, which
-- are collapsed when erased. Hence the erased memory are low-equivalent, i.e. their erasures
-- are equivalent.
εˢ-≡ : ∀ {τ h ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm (Mac h τ)} -> (lₐ : Label) -> ¬ (h ⊑ lₐ) ->
            ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> εˢ lₐ s₁ ≡ εˢ lₐ s₂

-- The same conclusion can be derived for multiple steps, applying the single-step lemma multiple times.
εˢ-≡⋆ : ∀ {τ h ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm (Mac h τ)} -> (lₐ : Label) -> ¬ (h ⊑ lₐ) ->
            ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ c₂ ⟩ -> εˢ lₐ s₁ ≡ εˢ lₐ s₂
εˢ-≡⋆ lₐ ¬p [] = refl
εˢ-≡⋆ lₐ ¬p (s ∷ ss) rewrite εˢ-≡ lₐ ¬p s | εˢ-≡⋆ lₐ ¬p ss =  refl

εˢ-≡ lₐ ¬p (Pure x) = refl
εˢ-≡ lₐ ¬p (BindCtx s) = εˢ-≡ lₐ ¬p s
εˢ-≡ lₐ ¬p (CatchCtx s) = εˢ-≡ lₐ ¬p s
εˢ-≡ lₐ ¬p (unlabelCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (join p (BigStep x ss)) rewrite εˢ-≡⋆ lₐ (lemma p ¬p) ss = refl
εˢ-≡ lₐ ¬p (joinEx p (BigStep x ss)) rewrite εˢ-≡⋆ lₐ (lemma p ¬p) ss = refl
εˢ-≡ lₐ ¬p (new {s = s} p q) = εˢ-new-≡ (lemma p ¬p) s q _
εˢ-≡ lₐ ¬p (writeCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (write {s = s} p q r) = εˢ-write-≡ (lemma p ¬p) s q r _ 
εˢ-≡ lₐ ¬p (writeEx p q r) = refl
εˢ-≡ lₐ ¬p (readCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (read p q r) = refl
εˢ-≡ lₐ ¬p (readEx p) = refl

--------------------------------------------------------------------------------
-- Reference proof erasure
--------------------------------------------------------------------------------

εᵐ-TypedIx : ∀ {l lₐ τ n} -> (p : l ⊑ lₐ) -> (m : Memory l) -> TypedIx τ n m -> TypedIx τ (ε lₐ n) (εᵐ lₐ (yes p) m)
εᵐ-TypedIx p ._ Here = Here
εᵐ-TypedIx p ._ (There r) = There (εᵐ-TypedIx p _ r)
εᵐ-TypedIx p .∙ ∙ = ∙

ε-TypedIx : ∀ {l lₐ τ n ls} -> l ⊑ lₐ -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ n (getMemory q s) -> TypedIx τ (ε lₐ n) (getMemory q (εˢ lₐ s))
ε-TypedIx p [] () r
ε-TypedIx {l} {lₐ} p (x ∷ s) Here r with l ⊑? lₐ
ε-TypedIx p₁ (x ∷ s) Here r | yes p = εᵐ-TypedIx p x r
ε-TypedIx p (x ∷ s) Here r | no ¬p = ⊥-elim (¬p p)
ε-TypedIx p (x ∷ s) (There q) r = ε-TypedIx p s q r

ε-TypedIx∙  : ∀ {l lₐ τ n ls} -> ¬ l ⊑ lₐ -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ n (getMemory q s) -> TypedIx τ ∙ (getMemory q (εˢ lₐ s))
ε-TypedIx∙ ¬p [] () r
ε-TypedIx∙ {l} {lₐ} ¬p (x ∷ s) Here r with l ⊑? lₐ
ε-TypedIx∙ ¬p (x ∷ s) Here r | yes p = ⊥-elim (¬p p)
ε-TypedIx∙ ¬p₁ (x ∷ s) Here r | no ¬p = ∙
ε-TypedIx∙ ¬p (x ∷ s) (There q) r = ε-TypedIx∙ ¬p s q r

--------------------------------------------------------------------------------
-- New lemmas
--------------------------------------------------------------------------------

-- Allocating a term in  memory and then erasing the result is the same as allocating the erased term in the erased memory.
newᵐ-≡ : ∀ {l lₐ τ} (x : Dec (l ⊑ lₐ)) (m : Memory l) (t : CTerm τ) -> εᵐ lₐ x m ∷ʳ (ε lₐ t) ≡ εᵐ lₐ x (m ∷ʳ t)
newᵐ-≡ (yes p) ∙ t = refl
newᵐ-≡ (yes p) [] t = refl
newᵐ-≡ (yes p) (x ∷ m) t rewrite newᵐ-≡ (yes p) m t = refl
newᵐ-≡ (no ¬p) m t = refl

countᵐ-≡ : ∀ {l lₐ} -> l ⊑ lₐ -> (x : Dec (l ⊑ lₐ)) -> (m : Memory l) -> ε lₐ (count m) ≡ count (εᵐ lₐ x m)
countᵐ-≡ p (yes p₁) ∙ = refl
countᵐ-≡ p (yes p₁) [] = refl
countᵐ-≡ p (yes p₁) (x ∷ m) rewrite countᵐ-≡ p (yes p₁) m = refl
countᵐ-≡ p (no ¬p) m = ⊥-elim (¬p p)

getMemory≡∙ : ∀ {l lₐ ls} -> ¬ (l ⊑ lₐ) -> (q : l ∈ ls) (s : Store ls) -> getMemory q (εˢ lₐ s) ≡ ∙
getMemory≡∙ {l} {lₐ} ¬p Here (x ∷ s) with l ⊑? lₐ
getMemory≡∙ ¬p Here (x ∷ s) | yes p = ⊥-elim (¬p p)
getMemory≡∙ ¬p₁ Here (x ∷ s) | no ¬p = refl
getMemory≡∙ ¬p (There q) (x ∷ s) = getMemory≡∙ ¬p q s

getMemory-εˢ : ∀ {l ls} -> (lₐ : Label) (s : Store ls) (q : l ∈ ls) -> getMemory q (εˢ lₐ s) ≡ εᵐ lₐ (l ⊑? lₐ) (getMemory q s)
getMemory-εˢ lₐ [] ()
getMemory-εˢ lₐ (x ∷ s) Here = refl
getMemory-εˢ lₐ (x ∷ s) (There q) = getMemory-εˢ lₐ s q

count≡∙ : ∀ {l lₐ ls} -> ¬ l ⊑ lₐ -> (q : l ∈ ls) (s : Store ls) ->
          let m = getMemory q (εˢ lₐ s) in ∙ ≡ count m
count≡∙ ¬p q s rewrite getMemory≡∙ ¬p q s = refl          

count-≡ : ∀ {l lₐ ls} -> l ⊑ lₐ -> (q : l ∈ ls) (s : Store ls) -> ε lₐ (count (getMemory q s)) ≡ count (getMemory q (εˢ lₐ s))
count-≡ {l} {lₐ} p q s rewrite getMemory-εˢ lₐ s q = countᵐ-≡ p (l ⊑? lₐ) (getMemory q s)

newˢ-≡ : ∀ {l ls τ} -> (lₐ : Label) (q : l ∈ ls) (s : Store ls) (t : CTerm τ) -> εˢ lₐ (newˢ q s t) ≡ newˢ q (εˢ lₐ s) (ε lₐ t)
newˢ-≡ {l} lₐ Here (x ∷ s) t rewrite newᵐ-≡ (l ⊑? lₐ) x t = refl
newˢ-≡ lₐ (There q) (x ∷ s) t rewrite newˢ-≡ lₐ q s t = refl

--------------------------------------------------------------------------------
-- Read lemmas
--------------------------------------------------------------------------------

readᵐ-≡ : ∀ {l lₐ τ n} -> (p : l ⊑ lₐ) (m : Memory l) (r : TypedIx τ n m) -> ε lₐ ( m [ r ]) ≡ εᵐ lₐ (yes p) m [ εᵐ-TypedIx p m r ]
readᵐ-≡ {l} {lₐ} p ∙ ∙ with l ⊑? lₐ
readᵐ-≡ {lₐ = lₐ} {τ = τ} p₁ ∙ ∙ | yes p rewrite ε∙≡∙ {τ} {[]} lₐ =  refl
readᵐ-≡ p ∙ ∙ | no ¬p = refl
readᵐ-≡ p [] ()
readᵐ-≡ {l} {lₐ} p (x ∷ m) Here with l ⊑? lₐ
readᵐ-≡ p₁ (x ∷ m) Here | yes p = refl
readᵐ-≡ p (x ∷ m) Here | no ¬p = ⊥-elim (¬p p)
readᵐ-≡ p (x ∷ m) (There r) = readᵐ-≡ p m r

readᵐ-≡∙ : ∀ {l lₐ τ n} -> (¬p : ¬ l ⊑ lₐ) (m : Memory l) (r : TypedIx τ n m) -> ε lₐ ( m [ r ]) ≡ Res ∙
readᵐ-≡∙ {l} {lₐ} ¬p ._ Here with l ⊑? lₐ
readᵐ-≡∙ ¬p ._ Here | yes p = ⊥-elim (¬p p)
readᵐ-≡∙ ¬p₁ ._ Here | no ¬p = refl
readᵐ-≡∙ ¬p ._ (There r) = readᵐ-≡∙ ¬p _ r
readᵐ-≡∙ {l} {lₐ} ¬p .∙ ∙ with l ⊑? lₐ
readᵐ-≡∙ ¬p .∙ ∙ | yes p = ⊥-elim (¬p p)
readᵐ-≡∙ ¬p₁ .∙ ∙ | no ¬p = refl

readˢ-≡ : ∀ {l lₐ ls τ n} -> (p : l ⊑ lₐ) (s : Store ls) (q : l ∈ ls) (r : TypedIx τ n (getMemory q s)) ->
            ε lₐ (s [ q ][ r ]) ≡ (εˢ lₐ s) [ q ][ ε-TypedIx p s q r ]
readˢ-≡ p [] () r
readˢ-≡ {l} {lₐ} p (x ∷ s) Here r with l ⊑? lₐ
readˢ-≡ {l} {lₐ} p₁ (x ∷ s) Here r | yes p = readᵐ-≡ p x r
readˢ-≡ p (x ∷ s) Here r | no ¬p = ⊥-elim (¬p p)
readˢ-≡ p (x ∷ s) (There q) r = readˢ-≡ p s q r

readˢ-≡∙ : ∀ {l lₐ ls τ n} -> (¬p : ¬ (l ⊑ lₐ)) (s : Store ls) (q : l ∈ ls) (r : TypedIx τ n (getMemory q s)) ->
            ε lₐ (s [ q ][ r ]) ≡ (εˢ lₐ s) [ q ][ ε-TypedIx∙ ¬p s q r ]
readˢ-≡∙ ¬p [] () r
readˢ-≡∙ {l} {lₐ} ¬p (x ∷ s) Here r with l ⊑? lₐ
readˢ-≡∙ ¬p (m ∷ s) Here r | yes p = ⊥-elim (¬p p)
readˢ-≡∙ ¬p₁ (m ∷ s) Here r | no ¬p = readᵐ-≡∙ ¬p₁ m r
readˢ-≡∙ ¬p (x ∷ s) (There q) r = readˢ-≡∙ ¬p s q r

--------------------------------------------------------------------------------
-- Write lemmas
--------------------------------------------------------------------------------

writeᵐ-≡ : ∀ {l lₐ τ n} -> (c : CTerm τ) (p : l ⊑ lₐ) (m : Memory l) (r : TypedIx τ n m) -> (εᵐ lₐ (yes p) m [ εᵐ-TypedIx p m r ]≔ ε lₐ c) ≡ εᵐ lₐ (yes p) (m [ r ]≔ c) 
writeᵐ-≡ c p ._ Here = refl
writeᵐ-≡ c p ._ (There r) rewrite writeᵐ-≡ c p _ r = refl
writeᵐ-≡ c p .∙ ∙ = refl

writeˢ-≡ : ∀ {l lₐ ls τ n} -> (c : CTerm τ) (p : l ⊑ lₐ) (q : l ∈ ls) (s : Store ls) (r : TypedIx τ n (getMemory q s)) ->
           εˢ lₐ (s [ q ][ r ]≔ c) ≡ εˢ lₐ s [ q ][ ε-TypedIx p s q r ]≔ ε lₐ c
writeˢ-≡ {l} {lₐ}  c p Here (x ∷ s) r with l ⊑? lₐ
writeˢ-≡ c p₁ Here (m ∷ s) r | yes p rewrite writeᵐ-≡ c p m r = refl
writeˢ-≡ c p Here (x ∷ s) r | no ¬p = ⊥-elim (¬p p)
writeˢ-≡ c p (There q) (x ∷ s) r rewrite writeˢ-≡ c p q s r = refl

writeˢ-≡∙ : ∀ {l lₐ ls τ n} -> (c : CTerm τ) (¬p : ¬ l ⊑ lₐ) (q : l ∈ ls) (s : Store ls) (r : TypedIx τ n (getMemory q s)) ->
           εˢ lₐ (s [ q ][ r ]≔ c) ≡ εˢ lₐ s [ q ][ ε-TypedIx∙ ¬p s q r ]≔ ε lₐ c
writeˢ-≡∙ {l} {lₐ} c ¬p Here (m ∷ s) r with l ⊑? lₐ
writeˢ-≡∙ c ¬p Here (m ∷ s) r | yes p = ⊥-elim (¬p p)
writeˢ-≡∙ c ¬p₁ Here (m ∷ s) r | no ¬p = refl
writeˢ-≡∙ c ¬p (There q) (x ∷ s) r rewrite writeˢ-≡∙ c ¬p q s r = refl

writeExˢ-≡∙ : ∀ {l lₐ ls τ n} -> (c : CTerm τ) (¬p : ¬ l ⊑ lₐ) (q : l ∈ ls) (s : Store ls) (r : TypedIx τ n (getMemory q s)) ->
              (εˢ lₐ s) [ q ][ ε-TypedIx∙ ¬p s q r ]≔ ε lₐ c ≡ (εˢ lₐ s)
writeExˢ-≡∙ {l} {lₐ} c ¬p Here (x ∷ s) r with l ⊑? lₐ
writeExˢ-≡∙ c ¬p Here (x ∷ s) r | yes p = ⊥-elim (¬p p)
writeExˢ-≡∙ c ¬p₁ Here (x ∷ s) r | no ¬p = refl
writeExˢ-≡∙ {lₐ = lₐ} c ¬p (There q) (_∷_ {l = l'} x s) r = cong (_∷_ (εᵐ lₐ (l' ⊑? lₐ) x)) (writeExˢ-≡∙ c ¬p q s r)


-- We need to be careful with the rewriting or Agda starts going crazy.
-- It seems that if we introduce enough indirections everything works fine! :)
writeEx' :  ∀ {l h lₐ ls τ n} -> (c : CTerm τ) (p : l ⊑ h) (¬p : ¬ h ⊑ lₐ) (q : h ∈ ls) (s : Store ls) (r : TypedIx τ n (getMemory q s)) ->             
              ⟨ εˢ lₐ s ∥ write p (Res ∙) (ε lₐ c) ⟩ ⟼ ⟨ (εˢ lₐ s) ∥ Return （） ⟩ 
writeEx' {lₐ = lₐ} c p ¬p q s r = aux (write p q (ε-TypedIx∙ ¬p s q r))
  where
        aux : ⟨ εˢ lₐ s ∥ write p (Res ∙) (ε lₐ c) ⟩ ⟼ ⟨ (εˢ lₐ s) [ q ][ ε-TypedIx∙ ¬p s q r ]≔ ε lₐ c ∥ Return （） ⟩ ->
              ⟨ εˢ lₐ s ∥ write p (Res ∙) (ε lₐ c) ⟩ ⟼ ⟨ (εˢ lₐ s) ∥ Return （） ⟩ 
        aux step rewrite writeExˢ-≡∙ c ¬p q s r = step
        
--------------------------------------------------------------------------------

ε-Mac-dist lₐ (yes p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (yes p) x)
ε-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (unlabelCtx p₁ s) = unlabelCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p) (join {h = lʰ} p₁ bs) with lʰ ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (join p₂ bs) | yes p = join p₂ (ε-Mac-dist⇓ lₐ p bs)
ε-Mac-dist lₐ (yes p) (join p₁ (BigStep isV ss) ) | no ¬p rewrite εˢ-≡⋆ lₐ ¬p ss = join p₁ (BigStep (Mac ∙) [])
ε-Mac-dist lₐ (yes p) (joinEx {h = lʰ} p₁ bs) with lʰ ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (joinEx p₂ bs) | yes p = joinEx p₂ (ε-Mac-distₓ⇓ lₐ p bs)
ε-Mac-dist lₐ (yes p) (joinEx p₁ (BigStep x ss)) | no ¬p rewrite εˢ-≡⋆ lₐ ¬p ss = join p₁ (BigStep (Mac ∙) [])
ε-Mac-dist lₐ (yes p₁) (new {h = h} {s = s} {t = t} p q) with h ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (new {s = s} {t = t} p₂ q) | yes p rewrite newˢ-≡ lₐ q s t | count-≡ p q s = new p₂ q
ε-Mac-dist lₐ (yes p₁) (new {s = s} {t = t} p q) | no ¬p rewrite newˢ-≡ lₐ q s t | count≡∙ ¬p q s = new p q
ε-Mac-dist lₐ (yes p) (readCtx {l = l} p₁ s) with l ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (readCtx p₂ s) | yes p = readCtx p₂ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p) (readCtx p₁ s) | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ p))
ε-Mac-dist {ls = ls} lₐ (yes p') (read {l = l} {s = s} p q r) with l ⊑? lₐ
ε-Mac-dist lₐ (yes p') (read {s = s} {m = m} p₁ q r) | yes p rewrite readˢ-≡ p s q r = read {m = εᵐ lₐ (yes p) m} p₁ q (ε-TypedIx p s q r)
ε-Mac-dist lₐ (yes p') (read {s = s} p q r) | no ¬p rewrite readˢ-≡∙ ¬p s q r = read {m = ∙} p q (ε-TypedIx∙ ¬p s q r)
ε-Mac-dist lₐ (yes p₁) (readEx {l = l} {h = h} p) with l ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (readEx p₂) | yes p = readEx p₂
ε-Mac-dist lₐ (yes p₁) (readEx p) | no ¬p = ⊥-elim (¬p (trans-⊑ p p₁))
ε-Mac-dist lₐ (yes p₁) (writeCtx {h = h} p s) with h ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (writeCtx p₂ s) | yes p = writeCtx p₂ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p₁) (writeCtx p s) | no ¬p = writeCtx p (εᵖ-dist lₐ s) 
ε-Mac-dist lₐ (yes p₁) (write {h = h} {s = s} {c = c} p q r) with h ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (write {s = s} {c = c} p₂ q r) | yes p rewrite writeˢ-≡ c p q s r = write p₂ q (ε-TypedIx p s q r)
ε-Mac-dist lₐ (yes p₁) (write {s = s} {c = c} p q r) | no ¬p rewrite writeˢ-≡∙ c ¬p q s r = write p q (ε-TypedIx∙ ¬p s q r)
ε-Mac-dist lₐ (yes p₁) (writeEx {h = h} {s = s} p q r) with h ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (writeEx {s = s} p₂ q r) | yes p = writeEx p₂ q (ε-TypedIx p s q r)
ε-Mac-dist lₐ (yes p₁) (writeEx {s = s} {c = c} p q r) | no ¬p = writeEx' c p ¬p q s r
ε-Mac-dist {c₁ = c₁} {c₂ = c₂} lₐ (no ¬p) s
  rewrite ε-Mac-CTerm≡∙ lₐ c₁ ¬p | ε-Mac-CTerm≡∙ lₐ c₂ ¬p | εˢ-≡ lₐ ¬p s = Pure Hole

εᵖ-dist {（）} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Bool} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {τ => τ₁} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Mac lᵈ τ} {p₁ = ⟨ s₁ ∥ c₁ ⟩} {p₂ = ⟨ s₂ ∥ c₂ ⟩} lₐ s = ε-Mac-dist lₐ (lᵈ ⊑? lₐ) s
εᵖ-dist {Res l τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Exception} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s) 
εᵖ-dist {Nat} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
