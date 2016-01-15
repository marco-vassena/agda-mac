module Security.Distributivity where

open import Security.Base public
open import Typed.Semantics
open import Relation.Binary.PropositionalEquality 
open import Data.Product

-- TODO rename εᶜ-dist with εᵖ-dist ?

-- The closed term erasure function distributes over the small step semantics.
εᵖ-dist : ∀ {τ Δ₁ Δ₂} {p₁ : Program Δ₁ τ} {p₂ : Program Δ₂ τ} ->
            (lₐ : Label) -> p₁ ⟼ p₂ -> εᵖ lₐ p₁ ⟼ εᵖ lₐ p₂

εᶜ-dist⇝ : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⇝ c₂ -> εᶜ lₐ c₁ ⇝ εᶜ lₐ c₂

--------------------------------------------------------------------------------
-- Auxliary distributivity lemmas for Mac closed terms
--------------------------------------------------------------------------------

εᶜ-Mac-lookup : ∀ {lᵈ τ Δ} {lₐ : Label} (p : Dec (lᵈ ⊑ lₐ)) (Γ : Env Δ) (x : Mac lᵈ τ ∈ Δ)
                -> εᶜ-Mac lₐ p (x !! Γ) ≡ x !! εᶜ-env lₐ Γ
εᶜ-Mac-lookup {lᵈ} {lₐ = lₐ} p (c ∷ Γ) Here rewrite εᶜ-Mac-extensional p (lᵈ ⊑? lₐ) c = refl
εᶜ-Mac-lookup p (_ ∷ Γ) (There x) rewrite εᶜ-Mac-lookup p Γ x = refl

aux : ∀ {Δ Δ₁ Δ₂ τ lᵈ lʰ} {Γ : Env Δ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c : CTerm (Mac lʰ τ)} {v : Term Δ (Mac lʰ τ)} ->
        (lₐ : Label) -> IsValue (Γ , v) -> ⟨ m₁ ∥ c ⟩ ⟼⋆ ⟨ m₂ ∥ (Γ , v)⟩ ->
        let p₁ᵉ = ⟨ εᵐ lₐ (Mac lᵈ (Labeled lʰ τ)) m₁ ∥ εᶜ-keep lₐ c ⟩
            c₂ᵉ = (εᶜ-env lₐ Γ , ε-keep lₐ v)
            p₂ᵉ = ⟨ εᵐ lₐ (Mac lᵈ (Labeled lʰ τ)) m₂ ∥ c₂ᵉ ⟩ in IsValue c₂ᵉ × p₁ᵉ ⟼⋆ p₂ᵉ
aux lₐ (Γ , Mac t) [] = ((εᶜ-env lₐ Γ) , (Mac ∙)) , []
aux lₐ (Γ , Macₓ e) [] = ((εᶜ-env lₐ Γ) , (Macₓ ∙)) , []
aux lₐ v₁ (x ∷ ss) with aux lₐ v₁ ss
aux lₐ v₁ (x ∷ ss) | v₁ᵉ , ssᵉ = v₁ᵉ , ({!!} ∷ ssᵉ)



keep-∙ : ∀ {Δ₁ Δ₂ τ lʰ lₐ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Mac lʰ τ)} -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> 
         ⟨ ∙ {{Δ₁}} ∥ εᶜ-keep lₐ c₁ ⟩ ⟼ ⟨ ∙ {{Δ₂}} ∥ εᶜ-keep lₐ c₂ ⟩
keep-∙ (Pure x) = {!!}
keep-∙ Return = {!!}
keep-∙ Dist->>= = {!!}
keep-∙ (BindCtx s) = {!!}
keep-∙ Bind = Hole
keep-∙ BindEx = Hole
keep-∙ Throw = {!!}
keep-∙ Dist-Catch = {!!}
keep-∙ (CatchCtx s) = {!!}
keep-∙ Catch = {!!}
keep-∙ CatchEx = {!!}
keep-∙ (label p) = {!!}
keep-∙ (Dist-unlabel p) = {!!}
keep-∙ (unlabel p) = {!!}
keep-∙ (unlabelEx p) = {!!}
keep-∙ (unlabelCtx p s) = {!!}
keep-∙ (Dist-join p) = {!!}
keep-∙ (join p x) = {!!}
keep-∙ (joinEx p x) = {!!}
keep-∙ (new p) = {!!}
keep-∙ (Dist-write p) = {!!}
keep-∙ (Dist-read p) = {!!}
keep-∙ (writeCtx p s) = {!!}
keep-∙ (write p i) = {!!}
keep-∙ (readCtx p s) = {!!}
keep-∙ (read p i) = {!!}
keep-∙ Hole = {!!}

aux' : ∀ {Δ Δ₁ Δ₂ τ lʰ} {Γ : Env Δ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c : CTerm (Mac lʰ τ)} {v : Term Δ (Mac lʰ τ)} ->
        (lₐ : Label) -> IsValue (Γ , v) -> ⟨ m₁ ∥ c ⟩ ⟼⋆ ⟨ m₂ ∥ (Γ , v)⟩ ->
        let c₁ᵉ = εᶜ-keep lₐ c 
            c₂ᵉ = (εᶜ-env lₐ Γ , ε-keep lₐ v) in IsValue c₂ᵉ × ( ⟨ ∙ {{Δ₁}} ∥ c₁ᵉ ⟩ ⟼⋆ ⟨ ∙ {{Δ₂}} ∥ c₂ᵉ ⟩ )
aux' lₐ (Γ , Mac t) [] = (εᶜ-env lₐ Γ , Mac ∙) , []
aux' lₐ (Γ , Macₓ e) [] = (εᶜ-env lₐ Γ , Macₓ ∙) , []
aux' lₐ v₁ (x ∷ ss) with aux' lₐ v₁ ss
... | vᵉ , ssᵉ = vᵉ , (keep-∙ x ∷ ssᵉ)

keep-dist : ∀ {Δ Δ₁ Δ₂ τ lᵈ lʰ} {Γ : Env Δ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c : CTerm (Mac lʰ τ)} {v : Term Δ (Mac lʰ τ)} ->
            (lₐ : Label) -> ⟨ m₁ ∥ c ⟩ ⇓ ⟨ m₂ ∥ Γ , v ⟩ -> 
            ⟨ εᵐ lₐ (Mac lᵈ (Labeled lʰ τ)) m₁ ∥ εᶜ-keep lₐ c ⟩ ⇓ ⟨ εᵐ lₐ (Mac lᵈ (Labeled lʰ τ)) m₂ ∥ εᶜ-env lₐ Γ , ε-keep lₐ v ⟩ 
keep-dist lₐ (BigStep v ss) with aux lₐ v ss
keep-dist lₐ (BigStep v ss) | vᵉ  , ssᵉ = BigStep vᵉ ssᵉ

keep-dist' : ∀ {Δ Δ₁ Δ₂ τ lʰ} {Γ : Env Δ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c : CTerm (Mac lʰ τ)} {v : Term Δ (Mac lʰ τ)} ->
            (lₐ : Label) -> ⟨ m₁ ∥ c ⟩ ⇓ ⟨ m₂ ∥ Γ , v ⟩ -> 
            ⟨ ∙ {{Δ₁}} ∥ εᶜ-keep lₐ c ⟩ ⇓ ⟨ ∙ {{Δ₂}} ∥ εᶜ-env lₐ Γ , ε-keep lₐ v ⟩ 
keep-dist' lₐ (BigStep v ss) = {!!}
-- with aux lₐ v ss
-- keep-dist lₐ (BigStep v ss) | vᵉ  , ssᵉ = BigStep vᵉ ssᵉ


εᶜ-Mac-dist⇝ : ∀ {lᵈ τ} {c₁ c₂ : CTerm (Mac lᵈ τ)} -> (lₐ : Label) -> (p : Dec (lᵈ ⊑ lₐ)) ->
                 c₁ ⇝ c₂ -> εᶜ-Mac lₐ p c₁ ⇝ εᶜ-Mac lₐ p c₂
εᶜ-Mac-dist⇝ lₐ (yes p) (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) Beta with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) Beta | yes p = Beta
εᶜ-Mac-dist⇝ lₐ (yes p) Beta | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) (Lookup {Γ = Γ} {p = x}) rewrite εᶜ-Mac-lookup (lᵈ ⊑? lₐ) Γ x with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₂) Lookup | yes p = Lookup
εᶜ-Mac-dist⇝ lₐ (yes p₁) Lookup | no ¬p = ⊥-elim (¬p p₁)
εᶜ-Mac-dist⇝ lₐ (yes p) (Dist-$ {x = x}) rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-Mac-dist⇝ lₐ (yes p) Dist-If = Dist-If
εᶜ-Mac-dist⇝ lₐ (yes p) (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) IfTrue with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) (IfTrue {t = t}) | yes p rewrite εᶜ-Mac-extensional (yes p) (yes p₁) t = IfTrue
εᶜ-Mac-dist⇝ lₐ (yes p) IfTrue | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ {lᵈ} lₐ (yes p) IfFalse with lᵈ ⊑? lₐ
εᶜ-Mac-dist⇝ lₐ (yes p₁) (IfFalse {e = e}) | yes p rewrite εᶜ-Mac-extensional (yes p) (yes p₁) e = IfFalse
εᶜ-Mac-dist⇝ lₐ (yes p) IfFalse | no ¬p = ⊥-elim (¬p p)
εᶜ-Mac-dist⇝ lₐ (yes p) Dist-∙ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (yes p) Hole = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) (AppL s) =  Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Beta = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Lookup = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-$ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-If = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) (IfCond s) = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) IfTrue = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) IfFalse = Hole
εᶜ-Mac-dist⇝ lₐ (no ¬p) Dist-∙ = Dist-∙
εᶜ-Mac-dist⇝ lₐ (no ¬p) Hole = Hole

εᵖ-Mac-dist : ∀ {lᵈ τ Δ₁ Δ₂} {p₁ : Program  Δ₁ (Mac lᵈ τ)} {p₂ : Program Δ₂ (Mac lᵈ τ)} -> 
                (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) -> 
                p₁ ⟼ p₂ -> εᵖ-Mac lₐ x p₁ ⟼ εᵖ-Mac lₐ x p₂
εᵖ-Mac-dist lₐ (yes p) (Pure s) = Pure (εᶜ-Mac-dist⇝ lₐ (yes p) s)
εᵖ-Mac-dist {lᵈ} lₐ (yes p) Return with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) Return | yes p = Return
εᵖ-Mac-dist lₐ (yes p) Return | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) Dist->>= = Dist->>=
εᵖ-Mac-dist lₐ (yes p) (BindCtx s) = {!!} -- BindCtx (εᵖ-Mac-dist lₐ (yes p) s)
εᵖ-Mac-dist lₐ (yes p) (Bind {t = t}) rewrite εᶜ-Closure t lₐ = Bind
εᵖ-Mac-dist {lᵈ} lₐ (yes p) (BindEx {e = e}) with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) BindEx | yes p = BindEx
εᵖ-Mac-dist lₐ (yes p) BindEx | no ¬p = ⊥-elim (¬p p) 
εᵖ-Mac-dist {lᵈ} lₐ (yes p) Throw with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) Throw | yes p = Throw
εᵖ-Mac-dist lₐ (yes p) Throw | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) Dist-Catch = Dist-Catch
εᵖ-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (εᵖ-Mac-dist lₐ (yes p) s)
εᵖ-Mac-dist {lᵈ} lₐ (yes p) Catch with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) Catch | yes p = Catch
εᵖ-Mac-dist lₐ (yes p) Catch | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) CatchEx = CatchEx
εᵖ-Mac-dist lₐ (yes p) (label {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᵖ-Mac-dist {lᵈ} lₐ (yes p₁) (label d⊑h) | yes h⊑a with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (label {h = lʰ} d⊑h) | yes h⊑a | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (label d⊑h) | yes h⊑a | yes p₁ | yes p = label d⊑h
εᵖ-Mac-dist lₐ (yes p₁) (label d⊑h) | yes h⊑a | yes p | no ¬p = ⊥-elim (¬p h⊑a)
εᵖ-Mac-dist lₐ (yes p₁) (label d⊑h) | yes h⊑a | no ¬p = ⊥-elim (¬p p₁)
εᵖ-Mac-dist {lᵈ} lₐ (yes p) (label d⊑h) | no ¬h⊑a with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (label {h = lʰ} d⊑h) | no ¬h⊑a | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (label d⊑h) | no ¬h⊑a | yes p₁ | yes p = ⊥-elim (¬h⊑a p)
εᵖ-Mac-dist lₐ (yes p₁) (label d⊑h) | no ¬h⊑a | yes p | no ¬p = label d⊑h
εᵖ-Mac-dist lₐ (yes p) (label d⊑h) | no ¬h⊑a | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) (Dist-unlabel {l = lᵈ} {h = lʰ} d⊑h) = Dist-unlabel d⊑h
εᵖ-Mac-dist lₐ (yes p) (unlabel {l = lᵈ} {h = lʰ} d⊑h) with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (unlabel {h = lʰ} d⊑h) | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (unlabel d⊑h) | yes p₁ | yes p = unlabel d⊑h
εᵖ-Mac-dist lₐ (yes p₁) (unlabel d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᵖ-Mac-dist lₐ (yes p) (unlabel {h = lʰ} d⊑h) | no ¬p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (unlabel d⊑h) | no ¬d⊑a | yes h⊑a = ⊥-elim (¬d⊑a (trans-⊑ d⊑h h⊑a))
εᵖ-Mac-dist lₐ (yes p) (unlabel d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) (unlabelEx {l = lᵈ} d⊑h) with lᵈ ⊑? lₐ
εᵖ-Mac-dist {lʰ} lₐ (yes p₁) (unlabelEx d⊑h) | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (unlabelEx d⊑h) | yes p₁ | yes p = unlabelEx d⊑h
εᵖ-Mac-dist lₐ (yes p₁) (unlabelEx d⊑h) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᵖ-Mac-dist {lʰ} lₐ (yes p) (unlabelEx d⊑h) | no ¬p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (unlabelEx d⊑h) | no ¬p | yes h⊑a = ⊥-elim (¬p (trans-⊑ d⊑h p₁))
εᵖ-Mac-dist lₐ (yes p) (unlabelEx d⊑h) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist {τ = τ} lₐ (yes p) (unlabelCtx d⊑h s) = {!!} --unlabelCtx d⊑h (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p) (Dist-join {h = lʰ} d⊑h) with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (Dist-join d⊑h) | yes p = Dist-join d⊑h
εᵖ-Mac-dist lₐ (yes p) (Dist-join d⊑h) | no ¬p = Dist-join d⊑h
εᵖ-Mac-dist lₐ (yes p) (join {l = lᵈ} {h = lʰ} d⊑h s) with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (join {l = lᵈ} {h = lʰ} d⊑h s) | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (join d⊑h s) | yes p₁ | yes p = join d⊑h {!!}
εᵖ-Mac-dist lₐ (yes p₁) (join d⊑h s) | yes p | no ¬p = join d⊑h {!!}
εᵖ-Mac-dist lₐ (yes p) (join d⊑h s) | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p) (joinEx {l = lᵈ} {h = lʰ} d⊑h s) with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (joinEx {l = lᵈ} d⊑h s) | yes p with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₂) (joinEx {h = lʰ} d⊑h s) | yes p₁ | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₃) (joinEx d⊑h s) | yes p₂ | yes p₁ | yes p = joinEx d⊑h {!!}
εᵖ-Mac-dist lₐ (yes p₂) (joinEx d⊑h s) | yes p₁ | yes p | no ¬p = ⊥-elim (¬p p₁)
εᵖ-Mac-dist lₐ (yes p₁) (joinEx d⊑h s) | yes p | no ¬p = ⊥-elim (¬p p₁)
εᵖ-Mac-dist lₐ (yes p) (joinEx {l = lᵈ} d⊑h s) | no ¬p with lᵈ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes p₁) (joinEx {h = lʰ} d⊑h s) | no ¬p | yes p with lʰ ⊑? lₐ
εᵖ-Mac-dist lₐ (yes d⊑a) (joinEx {l = lᵈ} {h = lʰ} d⊑h s) | no ¬h⊑a | yes d⊑a' | yes h⊑a = (⊥-elim (¬h⊑a h⊑a))
εᵖ-Mac-dist lₐ (yes p₁) (joinEx d⊑h s) | no ¬p₁ | yes p | no ¬p = join d⊑h {!keep-dist ? ?!}
εᵖ-Mac-dist lₐ (yes p) (joinEx d⊑h s) | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
εᵖ-Mac-dist lₐ (yes p') (new p) = {!new p!} -- Auxiliary lemma
εᵖ-Mac-dist {p₁  = ⟨ _ ∥ Γ , write .p r t ⟩} lₐ (yes p') (Dist-write p) 
  rewrite εᶜ-Closure t lₐ = Dist-write p
εᵖ-Mac-dist lₐ (yes p') (Dist-read p) = Dist-read p
εᵖ-Mac-dist lₐ (yes p') (readCtx p s) = {!!} -- readCtx p (εᵖ-dist lₐ s)
εᵖ-Mac-dist {lᵈ} lₐ (yes p') (read p x) with lᵈ ⊑? lₐ
-- Lemma simil closure ?
εᵖ-Mac-dist {lᵈ} {（）} lₐ (yes p') (read p₁ x) | yes p = {!read p₁ x!} -- lemma about reading in memory
εᵖ-Mac-dist {lᵈ} {Bool} lₐ (yes p') (read p₁ x) | yes p = {!read p₁ x!}
εᵖ-Mac-dist {lᵈ} {τ => τ₁} lₐ (yes p') (read p₁ x) | yes p = {!read p₁ x!}
εᵖ-Mac-dist {lᵈ} {Mac x τ} lₐ (yes p') (read p₁ x₁) | yes p = {!read p₁ x₁!}
εᵖ-Mac-dist {lᵈ} {Labeled x τ} lₐ (yes p') (read p₁ x₁) | yes p = {!read p₁ x₁!}
εᵖ-Mac-dist {lᵈ} {Exception} lₐ (yes p') (read p₁ x) | yes p = {!read p₁ x !}
εᵖ-Mac-dist {lᵈ} {Ref x τ} lₐ (yes p') (read p₁ x₁) | yes p = {!read p₁ x₁ !}
εᵖ-Mac-dist lₐ (yes p') (read p x) | no ¬p = ⊥-elim (¬p p')
εᵖ-Mac-dist lₐ (yes p) Hole = {!!} -- Hole
εᵖ-Mac-dist lₐ (yes p') (writeCtx p s) = {!!} -- writeCtx p (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p') (write p x) = {!write p x!} -- Lemma
εᵖ-Mac-dist lₐ (no ¬p) (Pure s) = Pure (εᶜ-Mac-dist⇝ lₐ (no ¬p) s)
εᵖ-Mac-dist lₐ (no ¬p) Return = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) Dist->>= = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (BindCtx s) = {!Pure Hole!} -- Pure Hole does not work because the first ∙ is Memory Δ₁ and the second is Memory Δ₂ 
εᵖ-Mac-dist lₐ (no ¬p) Bind = Hole
εᵖ-Mac-dist lₐ (no ¬p) BindEx = Hole
εᵖ-Mac-dist lₐ (no ¬p) Throw = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) Dist-Catch = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (CatchCtx s) = {!Pure Hole!}
εᵖ-Mac-dist lₐ (no ¬p) Catch = Hole
εᵖ-Mac-dist lₐ (no ¬p) CatchEx = Hole
εᵖ-Mac-dist lₐ (no ¬p) (label p) = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (Dist-unlabel p) = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (unlabel p) = Hole
εᵖ-Mac-dist lₐ (no ¬p) (unlabelEx p) = Hole
εᵖ-Mac-dist lₐ (no ¬p) (unlabelCtx p s) = {!!}
εᵖ-Mac-dist lₐ (no ¬p) (Dist-join p) = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (join p s) = {!Hole!} -- Hole with different Δ₁ Δ₂
εᵖ-Mac-dist lₐ (no ¬p) (joinEx p s) = {!Hole!} -- Hole with different Δ₁ Δ₂
εᵖ-Mac-dist lₐ (no ¬p) (new p) = {!Pure Dist-∙!}
εᵖ-Mac-dist lₐ (no ¬p) (Dist-write p) = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (Dist-read p) = Pure Dist-∙
εᵖ-Mac-dist lₐ (no ¬p) (writeCtx p s) = {!Pure Hole!}
εᵖ-Mac-dist lₐ (no ¬p) (write p i) = Hole
εᵖ-Mac-dist lₐ (no ¬p) (readCtx p s) = {!Pure Hole!}
εᵖ-Mac-dist lₐ (no ¬p) (read p i) = Hole
εᵖ-Mac-dist lₐ (no ¬p) Hole = Hole

--------------------------------------------------------------------------------
-- The main distributivity theorem: 
-- ∀ c₁ c₂ lₐ . if c₁ ⟼ c₂ then (εᶜ lₐ c₁) ⟼ (εᶜ lₐ c₂)
--------------------------------------------------------------------------------

-- This proof is repetitive because, even though the erasure
-- function is defined with a default case for all non Mac lᵈ τ types
-- reasoning requires to explicitly pattern match on each of them.
εᶜ-dist⇝ {Mac lᵈ τ} lₐ s = εᶜ-Mac-dist⇝ lₐ (lᵈ ⊑? lₐ) s
εᶜ-dist⇝ {（）} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {（）} lₐ Beta = Beta
εᶜ-dist⇝ {（）} lₐ (Lookup {Γ = Γ} {p = x}) rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {（）} lₐ (Dist-$ {Γ = Γ} {x = x}) rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {（）} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {（）} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {（）} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {（）} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {（）} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {（）} lₐ Hole = Hole
εᶜ-dist⇝ {Bool} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Bool} lₐ Beta = Beta
εᶜ-dist⇝ {Bool} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Bool} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Bool} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Bool} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Bool} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Bool} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Bool} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Bool} lₐ Hole = Hole
εᶜ-dist⇝ {τ => τ₁} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {τ => τ₁} lₐ Beta = Beta
εᶜ-dist⇝ {τ => τ₁} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {τ => τ₁} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {τ => τ₁} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {τ => τ₁} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {τ => τ₁} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {τ => τ₁} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {τ => τ₁} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {τ => τ₁} lₐ Hole = Hole
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Beta = Beta
εᶜ-dist⇝ {Labeled lᵈ τ} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Labeled lᵈ τ} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Labeled lᵈ τ} lₐ Hole = Hole
εᶜ-dist⇝ {Exception} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Exception} lₐ Beta = Beta
εᶜ-dist⇝ {Exception} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Exception} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Exception} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Exception} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Exception} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Exception} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Exception} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Exception} lₐ Hole = Hole
εᶜ-dist⇝ {Ref lᵈ τ} lₐ (AppL s) = AppL (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Ref lᵈ τ} lₐ Beta = Beta
εᶜ-dist⇝ {Ref lᵈ τ} {c₁ = Γ , Var x} lₐ Lookup rewrite εᶜ-lookup lₐ x Γ = Lookup
εᶜ-dist⇝ {Ref lᵈ τ} {c₁ = Γ , App f x} lₐ Dist-$ rewrite εᶜ-Closure x lₐ = Dist-$
εᶜ-dist⇝ {Ref lᵈ τ} lₐ Dist-If = Dist-If
εᶜ-dist⇝ {Ref lᵈ τ} lₐ (IfCond s) = IfCond (εᶜ-dist⇝ lₐ s)
εᶜ-dist⇝ {Ref lᵈ τ} lₐ IfTrue = IfTrue
εᶜ-dist⇝ {Ref lᵈ τ} lₐ IfFalse = IfFalse
εᶜ-dist⇝ {Ref lᵈ τ} lₐ Dist-∙ = Dist-∙
εᶜ-dist⇝ {Ref lᵈ τ} lₐ Hole = Hole

εᵖ-dist {（）} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᵖ-dist {（）} lₐ Hole = Hole
εᵖ-dist {Bool} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᵖ-dist {Bool} lₐ Hole = Hole
εᵖ-dist {τ => τ₁} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᵖ-dist {τ => τ₁} lₐ Hole = Hole
εᵖ-dist {Mac l τ} lₐ s = εᵖ-Mac-dist lₐ (l ⊑? lₐ) s
εᵖ-dist {Labeled l τ} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᵖ-dist {Labeled x τ} lₐ Hole = Hole
εᵖ-dist {Exception} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s) 
εᵖ-dist {Exception} lₐ Hole = Hole
εᵖ-dist {Ref lᵈ τ} lₐ (Pure s) = Pure (εᶜ-dist⇝ lₐ s)
εᵖ-dist {Ref x τ} lₐ Hole = Hole
