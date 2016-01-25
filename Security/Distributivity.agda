module Security.Distributivity where


open import Security.Base public
open import Typed.Semantics
open import Typed.Valid
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Product
open import Data.List as L hiding (drop ; _∷ʳ_)

-- TODO rename εᶜ-dist with εᵖ-dist ?

-- The closed term erasure function distributes over the small step semantics.
εᵖ-dist : ∀ {τ Δ₁ Δ₂} {p₁ : Program Δ₁ τ} {p₂ : Program Δ₂ τ} ->
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

εᵐ-new : ∀ {τ Δᵐ} (lₐ : Label) (m : Memory Δᵐ) (t : CTerm τ) -> εᵐ lₐ (m ∷ʳ t) ≡ (εᵐ lₐ m ∷ʳ ε lₐ t)
εᵐ-new lₐ [] t = refl
εᵐ-new lₐ (x ∷ m) t rewrite εᵐ-new lₐ m t = refl
εᵐ-new lₐ ∙ t = refl

εᵐ-write : ∀ {τ n Δᵐ} (lₐ : Label) (m : Memory Δᵐ) (c : CTerm τ) (i : TypedIx τ n Δᵐ) -> εᵐ lₐ (m [ # i ]≔ c) ≡ ((εᵐ lₐ m) [ # i ]≔ ε lₐ c)
εᵐ-write lₐ (x ∷ m) c Here = refl
εᵐ-write lₐ ∙ c Here = refl
εᵐ-write lₐ (x ∷ m) c (There i) rewrite εᵐ-write lₐ m c i = refl
εᵐ-write lₐ ∙ c (There i) = refl

εᵐ-read : ∀ {τ Δᵐ n} -> (lₐ : Label) (m : Memory Δᵐ) (i : TypedIx τ n Δᵐ) -> _[_] (εᵐ lₐ m) (# i)  ≡ ε lₐ (_[_] m (# i))
εᵐ-read lₐ (x ∷ m) Here = refl
εᵐ-read {τ} {.τ ∷ Δᵐ} lₐ ∙ Here rewrite ε∙≡∙ {τ} {[]} lₐ =  refl
εᵐ-read lₐ (x ∷ m) (There i) rewrite εᵐ-read lₐ m i = refl
εᵐ-read {τ} lₐ ∙ (There i) rewrite ε∙≡∙ {τ} {[]} lₐ = refl

εᵖ-Mac-dist : ∀ {lᵈ τ Δ₁ Δ₂} {p₁ : Program Δ₁ (Mac lᵈ τ)} {p₂ : Program Δ₂ (Mac lᵈ τ)}  (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) ->
            p₁ ⟼ p₂ -> εᵖ-Mac lₐ x p₁ ⟼ εᵖ-Mac lₐ x p₂


εᵖ-Mac-distₓ⋆ : ∀ {lᵈ τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {c₁ : CTerm (Mac lᵈ τ)} {m₂ : Memory  Δ₂} {e : CTerm Exception} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼⋆ ⟨ m₂ ∥ (Macₓ e) ⟩ ->
              ⟨ εᵐ lₐ m₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⟼⋆ ⟨ εᵐ lₐ m₂ ∥ Macₓ (ε lₐ e) ⟩
εᵖ-Mac-distₓ⋆ lₐ p [] = []
εᵖ-Mac-distₓ⋆ lₐ p (s ∷ ss) = (εᵖ-Mac-dist lₐ (yes p) s) ∷ (εᵖ-Mac-distₓ⋆ lₐ p ss)

εᵖ-Mac-distₓ⇓ : ∀ {lᵈ τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {c₁ : CTerm (Mac lᵈ τ)} {m₂ : Memory  Δ₂} {e : CTerm Exception} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
             ⟨ m₁ ∥ c₁ ⟩ ⇓ ⟨ m₂ ∥ Macₓ e ⟩ ->
             ⟨ εᵐ lₐ  m₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⇓ ⟨ εᵐ lₐ m₂ ∥ Macₓ (ε lₐ e) ⟩
εᵖ-Mac-distₓ⇓ lₐ p (BigStep (Macₓ e) ss) = BigStep (Macₓ (ε lₐ e)) (εᵖ-Mac-distₓ⋆ lₐ p ss)


εᵖ-Mac-dist⋆ : ∀ {lᵈ τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {c₁ : CTerm (Mac lᵈ τ)} {m₂ : Memory  Δ₂} {c₂ : CTerm τ} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼⋆ ⟨ m₂ ∥ (Mac c₂) ⟩ ->
              ⟨ εᵐ lₐ m₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⟼⋆ ⟨ εᵐ lₐ m₂ ∥ Mac (ε lₐ c₂) ⟩
εᵖ-Mac-dist⋆ lₐ p [] = []
εᵖ-Mac-dist⋆ lₐ p (s ∷ ss) = (εᵖ-Mac-dist lₐ (yes p) s) ∷ (εᵖ-Mac-dist⋆ lₐ p ss)

εᵖ-Mac-dist⇓ : ∀ {lᵈ τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {c₁ : CTerm (Mac lᵈ τ)} {m₂ : Memory  Δ₂} {c₂ : CTerm τ} -> (lₐ : Label) (p : lᵈ ⊑ lₐ) ->
             ⟨ m₁ ∥ c₁ ⟩ ⇓ ⟨ m₂ ∥ Mac c₂ ⟩ ->
             ⟨ εᵐ lₐ  m₁ ∥ ε-Mac lₐ (yes p) c₁ ⟩ ⇓ ⟨ εᵐ lₐ m₂ ∥ Mac (ε lₐ c₂) ⟩
εᵖ-Mac-dist⇓ lₐ p (BigStep (Mac c₂) ss) = BigStep (Mac (ε lₐ c₂)) (εᵖ-Mac-dist⋆ lₐ p ss)

εᵖ-Mac-dist lₐ (yes p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (yes p) x)
εᵖ-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx (εᵖ-Mac-dist lₐ (yes p) s)
εᵖ-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (εᵖ-Mac-dist lₐ (yes p) s)
εᵖ-Mac-dist lₐ (yes p) (unlabelCtx p₁ s) = unlabelCtx p₁ (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p) (join {h = lʰ} p₁ bs) with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (join p₂ bs) | yes p = join p₂ (εᵖ-Mac-dist⇓ lₐ p bs)
εᵖ-Mac-dist lₐ (yes p) (join p₁ bs) | no ¬p = join p₁ (BigStep (Mac ∙) {![]!}) -- m₁ and m₂ must be the same to put [] 
εᵖ-Mac-dist lₐ (yes p) (joinEx {h = lʰ} p₁ bs) with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (joinEx p₂ bs) | yes p = joinEx p₂ (εᵖ-Mac-distₓ⇓ lₐ p bs)
εᵖ-Mac-dist lₐ (yes p) (joinEx p₁ bs) | no ¬p = join p₁ (BigStep (Mac ∙) {!!})
εᵖ-Mac-dist lₐ (yes p) (new {m = m} {t = t} p₁) rewrite εᵐ-new lₐ m t = new p₁
εᵖ-Mac-dist lₐ (yes p) (writeCtx p₁ s) = writeCtx p₁ (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p) (write {m = m} {c = c} p₁ i) rewrite εᵐ-write lₐ m c i = write p₁ i
εᵖ-Mac-dist lₐ (yes p) (readCtx p₁ s) = readCtx p₁ (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p) (read {m = m} p₁ i) rewrite sym (εᵐ-read lₐ m i) = read p₁ i
εᵖ-Mac-dist lₐ (yes p) (Hole x) = Hole x
εᵖ-Mac-dist lₐ (no ¬p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (no ¬p) x)
εᵖ-Mac-dist lₐ (no ¬p) (BindCtx s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (CatchCtx s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (unlabelCtx p s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (join p bs) = Hole (context-⊆⇓ bs)
εᵖ-Mac-dist lₐ (no ¬p) (joinEx p bs) = Hole (context-⊆⇓ bs)
εᵖ-Mac-dist lₐ (no ¬p) (new p) = Hole snoc-⊆
εᵖ-Mac-dist lₐ (no ¬p) (writeCtx p s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (write p i) = Hole refl-⊆
εᵖ-Mac-dist lₐ (no ¬p) (readCtx p s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (read p i) = Hole refl-⊆
εᵖ-Mac-dist lₐ (no ¬p) (Hole x) = Hole x

εᵖ-dist {（）} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {（）} lₐ (Hole x) = Hole x
εᵖ-dist {Bool} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Bool} lₐ (Hole x) = Hole x
εᵖ-dist {τ => τ₁} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {τ => τ₁} lₐ (Hole x) = Hole x
εᵖ-dist {Mac lᵈ τ} lₐ s = εᵖ-Mac-dist lₐ (lᵈ ⊑? lₐ) s
εᵖ-dist {Labeled l τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Labeled lᵈ τ} lₐ (Hole x) = Hole x
εᵖ-dist {Exception} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s) 
εᵖ-dist {Exception} lₐ (Hole x) = Hole x
εᵖ-dist {Ref lᵈ τ} lₐ (Pure s) = Pure (ε-dist⇝ lₐ s)
εᵖ-dist {Ref l τ} lₐ (Hole x) = Hole x
