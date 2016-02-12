{-# OPTIONS --rewriting #-}

module Security.Distributivity where


open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Product
open import Data.List as L hiding (drop ; _∷ʳ_)

-- TODO rename εᶜ-dist with εᵖ-dist ?

-- The closed term erasure function distributes over the small step semantics.
εᵖ-dist : ∀ {τ ls} {p₁ : Program ls τ} {p₂ : Program ls τ} ->
            (lₐ : Label) -> p₁ ⟼ p₂ -> εᵖ lₐ p₁ ⟼ εᵖ lₐ p₂

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ c₁ c₂ lₐ . if c₁ ⟼ c₂ then (εᶜ lₐ c₁) ⟼ (εᶜ lₐ c₂)
--------------------------------------------------------------------------------

ε-dist⇝ : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⇝ c₂ -> ε lₐ c₁ ⇝ ε lₐ c₂

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
ε-dist⇝ {Labeled lᵈ τ} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Labeled lᵈ τ} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Labeled lᵈ τ} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Labeled lᵈ τ} lₐ IfTrue = IfTrue
ε-dist⇝ {Labeled lᵈ τ} lₐ IfFalse = IfFalse
ε-dist⇝ {Labeled lᵈ τ} lₐ Hole = Hole
ε-dist⇝ {Exception} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Exception} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Exception} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Exception} lₐ IfTrue = IfTrue
ε-dist⇝ {Exception} lₐ IfFalse = IfFalse
ε-dist⇝ {Exception} lₐ Hole = Hole
ε-dist⇝ {Ref lᵈ τ} lₐ (AppL s) = AppL (ε-dist⇝ lₐ s)
ε-dist⇝ {Ref lᵈ τ} {c₁ = App (Abs t) x} lₐ Beta rewrite sym (ε-subst lₐ x t) = Beta
ε-dist⇝ {Ref lᵈ τ} lₐ (IfCond s) = IfCond (ε-dist⇝ lₐ s)
ε-dist⇝ {Ref lᵈ τ} lₐ IfTrue = IfTrue
ε-dist⇝ {Ref lᵈ τ} lₐ IfFalse = IfFalse
ε-dist⇝ {Ref lᵈ τ} lₐ Hole = Hole

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

εˢ-write-≡ : ∀ {lₐ lᵈ ls τ} {c : CTerm τ} -> ¬ (lᵈ ⊑ lₐ) -> (s : Store ls) (q : ⟨ τ , lᵈ ⟩∈ˢ s) ->
               εˢ lₐ s ≡ εˢ lₐ (writeˢ c s q) -- (writeˢ q s)
εˢ-write-≡ {lₐ} {lᵈ} ¬p (m ∷ s) (Here x) with lᵈ ⊑? lₐ
εˢ-write-≡ ¬p (m ∷ s) (Here x) | yes p = ⊥-elim (¬p p)
εˢ-write-≡ ¬p₁ (m ∷ s) (Here x) | no ¬p = refl
εˢ-write-≡ {lₐ} ¬p (_∷_ {l = l} _ s) (There q) with l ⊑? lₐ
εˢ-write-≡ ¬p (x ∷ s) (There q) | yes p rewrite εˢ-write-≡ ¬p s q = refl
εˢ-write-≡ ¬p (x ∷ s) (There q) | no ¬p' rewrite εˢ-write-≡ ¬p s q = refl

εˢ-new-≡ : ∀ {lₐ lᵈ ls τ} {c : CTerm τ} -> ¬ (lᵈ ⊑ lₐ) -> (s : Store ls) (q : ⟨ τ , lᵈ ⟩∈ˢ s) ->
               εˢ lₐ s ≡ εˢ lₐ (newˢ s q c)
εˢ-new-≡ {lₐ} {lᵈ} ¬p (m ∷ s) (Here x) with lᵈ ⊑? lₐ
εˢ-new-≡ ¬p (m ∷ s) (Here x) | yes p = ⊥-elim (¬p p)
εˢ-new-≡ ¬p₁ (m ∷ s) (Here x) | no ¬p = refl
εˢ-new-≡ {lₐ} ¬p (_∷_ {l = l} x s) (There q) with l ⊑? lₐ
εˢ-new-≡ ¬p (x ∷ s) (There q) | yes p rewrite εˢ-new-≡ ¬p s q = refl
εˢ-new-≡ ¬p (x ∷ s) (There q) | no ¬p₁ rewrite εˢ-new-≡ ¬p s q = refl 

lemma : ∀ {a b c} -> a ⊑ b -> ¬ (a ⊑ c) -> ¬ (b ⊑ c)
lemma a⊑b ¬a⊑c b⊑c = ⊥-elim (¬a⊑c (trans-⊑ a⊑b b⊑c)) 

εˢ-≡ : ∀ {τ h ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm (Mac h τ)} -> (lₐ : Label) -> ¬ (h ⊑ lₐ) ->
            ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> εˢ lₐ s₁ ≡ εˢ lₐ s₂
εˢ-≡ lₐ ¬p (Pure x) = refl
εˢ-≡ lₐ ¬p (BindCtx s) = εˢ-≡ lₐ ¬p s
εˢ-≡ lₐ ¬p (CatchCtx s) = εˢ-≡ lₐ ¬p s
εˢ-≡ lₐ ¬p (unlabelCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (join p x) = {!!}
εˢ-≡ lₐ ¬p (joinEx p x) = {!!}
εˢ-≡ lₐ ¬p (new {s = s} p q) = εˢ-new-≡ (lemma p ¬p) s q
εˢ-≡ lₐ ¬p (writeCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (write {s = s} p q) = εˢ-write-≡ (lemma p ¬p) s q
εˢ-≡ lₐ ¬p (readCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (read p q) = refl

readᵐ-≡ : ∀ {l lₐ τ} -> l ⊑ lₐ -> (m : Memory l) (x : τ ∈ᵐ m)  -> _[_] (εᵐ lₐ m) (ε-∈ᵐ lₐ x) ≡ ε lₐ (_[_] m x)
readᵐ-≡ {l} {lₐ} p ._ Here with l ⊑? lₐ
readᵐ-≡ p₁ ._ Here | yes p = refl
readᵐ-≡ p ._ Here | no ¬p = ⊥-elim (¬p p)
readᵐ-≡ p ._ (There x) = readᵐ-≡ p _ x
readᵐ-≡ {l = l} {lₐ} p  .∙ ∙ with l ⊑? lₐ
readᵐ-≡ {lₐ = lₐ} {τ = τ} p .∙ ∙ | yes _ rewrite ε∙≡∙ {τ = τ} {[]} lₐ = refl
readᵐ-≡ {lₐ = lₐ} {τ = τ} p .∙ ∙ | no ¬p rewrite ε∙≡∙ {τ = τ} {[]} lₐ = refl

readᵐ-≡∙ : ∀ {l lₐ τ} -> ¬ (l ⊑ lₐ) -> (m : Memory l) (x : τ ∈ᵐ m) -> Res ∙ ≡ ε lₐ (_[_] m x)
readᵐ-≡∙ {l} {lₐ} ¬p ._ Here with l ⊑? lₐ
readᵐ-≡∙ ¬p ._ Here | yes p = ⊥-elim (¬p p)
readᵐ-≡∙ ¬p₁ ._ Here | no ¬p = refl
readᵐ-≡∙ ¬p ._ (There x) = readᵐ-≡∙ ¬p _ x
readᵐ-≡∙ {l} {lₐ} ¬p .∙ ∙ with l ⊑? lₐ
readᵐ-≡∙ {lₐ = lₐ} {τ = τ} ¬p .∙ ∙ | yes p rewrite ε∙≡∙ {τ = τ} {[]} lₐ = refl
readᵐ-≡∙ ¬p₁ .∙ ∙ | no ¬p = refl

readˢ-≡ : ∀ {l ls τ} (lₐ : Label) (s : Store ls) (q : ⟨ τ , l ⟩∈ˢ s ) -> readˢ (εˢ lₐ s) (ε-∈ˢ lₐ q) ≡ ε lₐ (readˢ s q)
readˢ-≡ {l} lₐ (m ∷ s) (Here x)  with l ⊑? lₐ
readˢ-≡ lₐ (m ∷ s) (Here x) | yes p = readᵐ-≡ p _ x
readˢ-≡ lₐ (m ∷ s) (Here x) | no ¬p = readᵐ-≡∙ ¬p m x
readˢ-≡ lₐ (m ∷ s) (There {l' = l} q) with l ⊑? lₐ
readˢ-≡ lₐ (m ∷ s) (There q) | yes p rewrite readˢ-≡ lₐ s q = refl
readˢ-≡ lₐ (m ∷ s) (There q) | no ¬p = readˢ-≡ lₐ s q 

writeᵐ-≡ : ∀ {l lₐ τ} {m : Memory l} (c : CTerm τ)  -> l ⊑ lₐ -> (x : τ ∈ᵐ m) ->
             let mᵉ = (εᵐ lₐ m) [ (ε-∈ᵐ lₐ x) ]≔ (ε lₐ c)
                 mᵉ' = εᵐ lₐ (m [ x ]≔ c) in mᵉ ≡ mᵉ'
writeᵐ-≡ c p Here = refl
writeᵐ-≡ c p (There x) rewrite writeᵐ-≡ c p x = refl
writeᵐ-≡ c p ∙ = refl

writeˢ-≡ : ∀ {l ls τ} {s : Store ls} (lₐ : Label) (t : CTerm τ) (q : ⟨ τ , l ⟩∈ˢ s )
             -> εˢ lₐ (writeˢ t s q) ≡ writeˢ (ε lₐ t) (εˢ lₐ s) (ε-∈ˢ lₐ q)
writeˢ-≡ {l} lₐ c (Here x) with l ⊑? lₐ
writeˢ-≡ lₐ c (Here x) | yes p rewrite writeᵐ-≡ c p x =  refl
writeˢ-≡ lₐ c (Here x) | no ¬p = refl
writeˢ-≡ lₐ c (There {l' = l} q) with l ⊑? lₐ
writeˢ-≡ lₐ c (There q) | yes p rewrite writeˢ-≡ lₐ c q = refl
writeˢ-≡ lₐ c (There q) | no ¬p rewrite writeˢ-≡ lₐ c q = refl

newᵐ-≡ : ∀ {l τ} (lₐ : Label) (m : Memory l) (t : CTerm τ) -> εᵐ lₐ (m ∷ʳ t) ≡ εᵐ lₐ m ∷ʳ (ε lₐ t)
newᵐ-≡ lₐ ∙ x = refl
newᵐ-≡ lₐ [] x = refl
newᵐ-≡ lₐ (x ∷ m) x₁ rewrite newᵐ-≡ lₐ m x₁ = refl

newˢ-≡ : ∀ {l ls τ} (lₐ : Label) (t : CTerm τ) (s : Store ls) (q : ⟨ τ , l ⟩∈ˢ s) ->
            εˢ lₐ (newˢ s q t) ≡ newˢ  (εˢ lₐ s) (ε-∈ˢ lₐ q) (ε lₐ t) 
newˢ-≡ lₐ t [] ()
newˢ-≡ {l = l} lₐ t (m ∷ s) (Here x) with l ⊑? lₐ
newˢ-≡ lₐ t (m ∷ s) (Here x) | yes p rewrite newᵐ-≡ lₐ m t = refl
newˢ-≡ lₐ t (m ∷ s) (Here x) | no ¬p = refl
newˢ-≡ lₐ t (_∷_ {l = l} m s) (There q) with l ⊑? lₐ
newˢ-≡ lₐ t (m ∷ s) (There q) | yes p rewrite newˢ-≡ lₐ t s q = refl
newˢ-≡ lₐ t (m ∷ s) (There q) | no ¬p rewrite newˢ-≡ lₐ t s q = refl

ε-Mac-dist lₐ (yes p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (yes p) x)
ε-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (unlabelCtx p₁ s) = unlabelCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p) (join {h = lʰ} p₁ bs) = {!!}
ε-Mac-dist lₐ (yes p) (joinEx {h = lʰ} p₁ bs) = {!!}
ε-Mac-dist lₐ (yes p₁) (new {h = h} {s = s} {t = t} p q) rewrite newˢ-≡ lₐ t s q = new p (ε-∈ˢ lₐ q)
ε-Mac-dist lₐ (yes p) (readCtx p₁ s) = readCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist {ls = ls} lₐ (yes p') (read {l = l} {s = s} p q) rewrite sym (readˢ-≡ lₐ s q) = read p (ε-∈ˢ lₐ q)
ε-Mac-dist lₐ (yes p₁) (writeCtx {h = h} p s) with h ⊑? lₐ
ε-Mac-dist lₐ (yes p₁) (writeCtx p₂ s) | yes p = writeCtx p₂ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p₁) (writeCtx p s) | no ¬p = writeCtx p (εᵖ-dist lₐ s) 
ε-Mac-dist lₐ (yes p₁) (write {h = h} {c = t} p q) rewrite writeˢ-≡ lₐ t q = write p (ε-∈ˢ lₐ q)
-- with h ⊑? lₐ
-- ε-Mac-dist lₐ (yes p₁) (write {h = h} {c = t} p₂ q) | yes p rewrite writeˢ-≡ lₐ t q with h ⊑? lₐ
-- ε-Mac-dist lₐ (yes p₂) (write p₃ q) | yes p₁ | yes p = write p₃ (ε-∈ˢ lₐ q)
-- ε-Mac-dist lₐ (yes p₁) (write p₂ q) | yes p | no ¬p = ⊥-elim (¬p p)
-- ε-Mac-dist lₐ (yes p₁) (write {h = h} {c = t} p q) | no ¬p rewrite writeˢ-≡ lₐ t q with h ⊑? lₐ
-- ε-Mac-dist lₐ (yes p₁) (write p₂ q) | no ¬p | yes p = ⊥-elim (¬p p)
-- ε-Mac-dist lₐ (yes p₁) (write p q) | no ¬p₁ | no ¬p = {! write p (ε-∈ˢ lₐ q)!} 
ε-Mac-dist {c₁ = c₁} {c₂ = c₂} lₐ (no ¬p) s
  rewrite ε-Mac-CTerm≡∙ lₐ c₁ ¬p | ε-Mac-CTerm≡∙ lₐ c₂ ¬p | εˢ-≡ lₐ ¬p s = Pure Hole

εᵖ-dist {（）} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Bool} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {τ => τ₁} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Mac lᵈ τ} {p₁ = ⟨ s₁ ∥ c₁ ⟩} {p₂ = ⟨ s₂ ∥ c₂ ⟩} lₐ s = ε-Mac-dist lₐ (lᵈ ⊑? lₐ) s
εᵖ-dist {Labeled l τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Exception} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s) 
εᵖ-dist {Ref lᵈ τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
