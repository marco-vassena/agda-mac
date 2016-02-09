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

εᵐ-new : ∀ {τ lᵈ} (lₐ : Label) (m : Memory lᵈ) (t : CTerm (Labeled lᵈ τ)) -> εᵐ lₐ (m ∷ʳ t) ≡ (εᵐ lₐ m ∷ʳ ε lₐ t)
εᵐ-new lₐ [] t = refl
εᵐ-new lₐ (x ∷ m) t rewrite εᵐ-new lₐ m t = refl
εᵐ-new lₐ ∙ t = refl

εˢ-lemma : ∀ {l ls} (lₐ : Label) (s : Store ls) (q : l ∈ ls) ->
             let sᵉ = εˢ lₐ s
                 m = getMemory q s
                 mᵉ = getMemory q sᵉ in updateMemory mᵉ q sᵉ ≡ εˢ lₐ (updateMemory m q s)
εˢ-lemma lₐ (_∷_ {l = l} m s) Here with l ⊑? lₐ
εˢ-lemma lₐ (m ∷ s) Here | yes p = refl
εˢ-lemma lₐ (m ∷ s) Here | no ¬p = refl
εˢ-lemma lₐ (_∷_ {l = l} x s) (There q) with l ⊑? lₐ
εˢ-lemma lₐ (x ∷ s) (There q) | yes p rewrite εˢ-lemma lₐ s q = refl
εˢ-lemma lₐ (x ∷ s) (There q) | no ¬p rewrite εˢ-lemma lₐ s q = refl

εˢ-getMemory : ∀ {l ls} (lₐ : Label) (s : Store ls) (q : l ∈ ls) ->
             let sᵉ = εˢ lₐ s
                 m = getMemory q s 
                 mᵉ = getMemory q sᵉ in εᵐ lₐ m ≡ mᵉ
εˢ-getMemory {l} lₐ (x ∷ s) Here with l ⊑? lₐ
εˢ-getMemory lₐ (x ∷ s) Here | yes p = refl
εˢ-getMemory lₐ (x ∷ s) Here | no ¬p = {!!} -- This does not work at the moment ... can we ?
εˢ-getMemory lₐ (_∷_ {l = l} x s) (There q) with l ⊑? lₐ
εˢ-getMemory lₐ (x ∷ s) (There q) | yes p = εˢ-getMemory lₐ s q
εˢ-getMemory lₐ (x ∷ s) (There q) | no ¬p = εˢ-getMemory lₐ s q

εˢ-new : ∀ {l ls τ} {t : CTerm τ} (lₐ : Label) (s : Store ls) (q : l ∈ ls) ->
              let sᵉ = εˢ lₐ s
                  m = getMemory q s
                  mᵉ = getMemory q sᵉ in
                     updateMemory (mᵉ ∷ʳ Res (ε lₐ t)) q sᵉ ≡ εˢ lₐ (updateMemory (m ∷ʳ Res t) q s) 
εˢ-new lₐ s q = {!!}

εᵐ-write : ∀ {τ l n} (lₐ : Label) (m : Memory l) (c : CTerm (Labeled l τ)) (i : TypedIx τ n m) -> εᵐ lₐ (m [ i ]≔ c) ≡ ((εᵐ lₐ m) [ {!!} ]≔ ε lₐ c)
εᵐ-write lₐ m c q = {!!}
-- lₐ (x ∷ m) c Here = refl
-- εᵐ-write lₐ ∙ c Here = refl
-- εᵐ-write lₐ (x ∷ m) c (There i) rewrite εᵐ-write lₐ m c i = refl
-- εᵐ-write lₐ ∙ c (There i) = refl

εᵐ-read : ∀ {τ l Δᵐ n} -> (lₐ : Label) (m : Memory l) (i : TypedIx τ n m) -> _[_] (εᵐ lₐ m) {!!}  ≡ ε lₐ (_[_] m i)
εᵐ-read lₐ m q = {!!}
-- (x ∷ m) Here = refl
-- εᵐ-read {τ} {l} {.(l , τ)  ∷ Δᵐ} lₐ ∙ Here rewrite ε∙≡∙ {τ} {[]} lₐ =  refl
-- εᵐ-read lₐ (x ∷ m) (There i) rewrite εᵐ-read lₐ m i = refl
-- εᵐ-read {τ} lₐ ∙ (There i) rewrite ε∙≡∙ {τ} {[]} lₐ = refl

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

εˢ-write-≡ : ∀ {lₐ lᵈ n ls τ} {c : CTerm (Labeled lᵈ τ)} -> ¬ (lᵈ ⊑ lₐ) -> (s : Store ls) (q : lᵈ ∈ ls) ->
               let m = getMemory q s in (i : TypedIx τ n m) -> εˢ lₐ s ≡ εˢ lₐ (updateMemory (m [ i ]≔ c) q s)
εˢ-write-≡ {lₐ} {lᵈ} ¬p (m ∷ s) Here i with lᵈ ⊑? lₐ
εˢ-write-≡ ¬p (m ∷ s) Here i | yes p = ⊥-elim (¬p p)
εˢ-write-≡ ¬p₁ (m ∷ s) Here i | no ¬p = refl
εˢ-write-≡ {lₐ} ¬p (_∷_ {l = l} _ s) (There q) i with l ⊑? lₐ
εˢ-write-≡ ¬p (x ∷ s) (There q) i | yes p rewrite εˢ-write-≡ ¬p s q i = refl
εˢ-write-≡ ¬p (x ∷ s) (There q) i | no ¬p' rewrite εˢ-write-≡ ¬p s q i = refl

εˢ-new-≡ : ∀ {lₐ lᵈ ls τ} {c : CTerm (Labeled lᵈ τ)} -> ¬ (lᵈ ⊑ lₐ) -> (s : Store ls) (q : lᵈ ∈ ls) ->
               let m = getMemory q s in εˢ lₐ s ≡ εˢ lₐ (updateMemory (m ∷ʳ c) q s)
εˢ-new-≡ {lₐ} {lᵈ} ¬p (m ∷ s) Here with lᵈ ⊑? lₐ
εˢ-new-≡ ¬p (m ∷ s) Here | yes p = ⊥-elim (¬p p)
εˢ-new-≡ ¬p₁ (m ∷ s) Here | no ¬p = refl
εˢ-new-≡ {lₐ} ¬p (_∷_ {l = l} c s) (There q) with l ⊑? lₐ
εˢ-new-≡ ¬p (c₁ ∷ s) (There q) | yes p rewrite εˢ-new-≡ ¬p s q = refl
εˢ-new-≡ ¬p (c₁ ∷ s) (There q) | no ¬p' rewrite εˢ-new-≡ ¬p s q = refl

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
εˢ-≡ lₐ ¬p (write {s = s} p q i) = εˢ-write-≡ (lemma p ¬p) s q i
εˢ-≡ lₐ ¬p (readCtx p (Pure x)) = refl
εˢ-≡ lₐ ¬p (read p q i) = refl       

-- No! This does
lengthᵐ-lemma : ∀ {l ls} (lₐ : Label) (s : Store ls) (q : l ∈ ls) ->
                  let sᵉ = εˢ lₐ s
                      m = getMemory q s
                      mᵉ = getMemory q sᵉ in lengthᵐ m ≡ lengthᵐ mᵉ
lengthᵐ-lemma {l} lₐ (x ∷ s) Here with l ⊑? lₐ
lengthᵐ-lemma lₐ (x ∷ s) Here | yes p = {!!}
lengthᵐ-lemma lₐ (x ∷ s) Here | no ¬p = {!!}
lengthᵐ-lemma lₐ s (There q) = {!!}

ε-TypedIx : ∀ {τ n l} (lₐ : Label) -> (m : Memory l) -> TypedIx τ n m -> TypedIx τ n (εᵐ lₐ m)
ε-TypedIx lₐ ._ Here = Here
ε-TypedIx lₐ ._ (There i) = There (ε-TypedIx lₐ _ i)
ε-TypedIx lₐ .∙ Hole = Hole

εˢ-TypedIx : ∀ {τ n l ls} (lₐ : Label) (q : l ∈ ls) (s : Store ls) ->
              let m = getMemory q s
                  mᵉ = getMemory q (εˢ lₐ s) in TypedIx τ n m -> TypedIx τ n mᵉ
εˢ-TypedIx {l = l} lₐ Here (x ∷ s) i with l ⊑? lₐ
εˢ-TypedIx lₐ Here (x ∷ s) i | yes p = ε-TypedIx lₐ x i
εˢ-TypedIx lₐ Here (x ∷ s) i | no ¬p = Hole
εˢ-TypedIx lₐ (There q) (_∷_ {l = l} x s) i with l ⊑? lₐ
εˢ-TypedIx lₐ (There q) (x ∷ s) i | yes p = εˢ-TypedIx lₐ q s i
εˢ-TypedIx lₐ (There q) (x ∷ s) i | no ¬p = εˢ-TypedIx lₐ q s i                  

εˢ-read : ∀ {l τ n ls} (lₐ : Label) (s : Store ls) (q : l ∈ ls) ->
          let m = getMemory q s in (i : TypedIx τ n m) -> (ε lₐ (_[_] m i )) ≡ (_[_] (εᵐ lₐ m) (ε-TypedIx lₐ m i))
εˢ-read lₐ s q = {!!}

-- 1) Reference part of Term language
-- 2) Erase pointers in references
-- 3) Erase proof objects as well.
-- 4) Simplify getMemory / updateMemory

ε-Mac-dist lₐ (yes p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (yes p) x)
ε-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (ε-Mac-dist lₐ (yes p) s)
ε-Mac-dist lₐ (yes p) (unlabelCtx p₁ s) = unlabelCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p) (join {h = lʰ} p₁ bs) = {!!}
ε-Mac-dist lₐ (yes p) (joinEx {h = lʰ} p₁ bs) = {!!}
ε-Mac-dist lₐ (yes p₁) (new {s = s} {t = t} p q) = {!!} -- rewrite sym (εˢ-new {t = t} lₐ s q) | lengthᵐ-lemma lₐ s q = new {s = εˢ lₐ s} {t = ε lₐ t} p q
ε-Mac-dist lₐ (yes p) (writeCtx {h = lʰ} p₁ s) = writeCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist lₐ (yes p') (write p q i) = {!write p q i!}
ε-Mac-dist lₐ (yes p) (readCtx p₁ s) = readCtx p₁ (εᵖ-dist lₐ s)
ε-Mac-dist {ls = ls} lₐ (yes p') (read {l} {h} {α = α} {n = n} {s = s} p q i)
  rewrite εˢ-getMemory lₐ s q | εˢ-read lₐ s q i = {!read p q (εˢ-TypedIx lₐ q s i)!} --  -- read {ls} {l} {h} {α = α} {n = n} p q (ε-TypedIx {α} {n} lₐ q s i)
ε-Mac-dist {c₁ = c₁} {c₂ = c₂} lₐ (no ¬p) s
  rewrite ε-Mac-CTerm≡∙ lₐ c₁ ¬p | ε-Mac-CTerm≡∙ lₐ c₂ ¬p | εˢ-≡ lₐ ¬p s = Pure Hole

εᵖ-dist {（）} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Bool} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {τ => τ₁} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Mac lᵈ τ} {p₁ = ⟨ s₁ ∥ c₁ ⟩} {p₂ = ⟨ s₂ ∥ c₂ ⟩} lₐ s = ε-Mac-dist lₐ (lᵈ ⊑? lₐ) s
εᵖ-dist {Labeled l τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Exception} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s) 
εᵖ-dist {Ref lᵈ τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
