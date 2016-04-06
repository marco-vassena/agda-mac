module Sequential.Security.NonInterference where

open import Sequential.Security.Distributivity hiding (εˢ-≡)
open import Sequential.Determinism

open import Relation.Binary.PropositionalEquality
open import Data.Sum

open Program

--------------------------------------------------------------------------------
-- Store low-equivalnce

data _≈ˢ_ {{lₐ : Label}} {ls : List Label} (Σ₁ Σ₂ : Store ls) : Set where
  εˢ-≡ : εˢ lₐ Σ₁ ≡ εˢ lₐ Σ₂ -> Σ₁ ≈ˢ Σ₂

refl-≈ˢ : ∀ {l ls} {s : Store ls} -> s ≈ˢ s
refl-≈ˢ = εˢ-≡ refl

sym-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ : Store ls} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₁
sym-≈ˢ (εˢ-≡ x) = εˢ-≡ (sym x)

trans-≈ˢ : ∀ {l ls} {Σ₁ Σ₂ s₃ : Store ls} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ s₃ -> Σ₁ ≈ˢ s₃
trans-≈ˢ (εˢ-≡ x) (εˢ-≡ x₁) = εˢ-≡ (trans x x₁)

--------------------------------------------------------------------------------
-- Term low-equivalence

data _≈_ {{lₐ : Label}} {τ : Ty} (t₁ t₂ : CTerm τ) : Set where
  ε-≡ : ε lₐ t₁ ≡ ε lₐ t₂ -> t₁ ≈ t₂

refl-≈ : ∀ {l τ} {c : CTerm τ} -> c ≈ c
refl-≈ = ε-≡ refl

sym-≈ : ∀ {l τ} {c₁ c₂ : CTerm τ} -> c₁ ≈ c₂ -> c₂ ≈ c₁
sym-≈ (ε-≡ x) = ε-≡ (sym x)

trans-≈ : ∀ {l τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ≈ c₂ -> c₂ ≈ c₃ -> c₁ ≈ c₃
trans-≈ (ε-≡ x) (ε-≡ x₁) = ε-≡ (trans x x₁)

_≈-⟨_⟩_ : ∀ {τ}  -> CTerm τ -> Label -> CTerm τ -> Set
c₁ ≈-⟨ lₐ ⟩ c₂ = c₁ ≈ c₂

--------------------------------------------------------------------------------
-- Program Low Equivalence

-- It is convenient for reasoning to define directly the equivalence of two programs as the low-equivalence
-- of their stores and terms. This is still equivalent to εᵖ lₐ p₁ ≡ εᵖ lₐ p₂
data _≈ᵖ_ {{l : Label}} {ls : List Label} {τ : Ty} (p₁ p₂ : Program ls τ) : Set where
  εᵖ-≡ : store p₁ ≈ˢ store p₂ -> term p₁ ≈ term p₂ -> p₁ ≈ᵖ p₂

_≈ᵖ-⟨_⟩_ : ∀ {τ ls} -> Program ls τ -> Label -> Program ls τ -> Set
p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ = p₁ ≈ᵖ p₂

refl-≈ᵖ : ∀ {l τ ls} {p : Program ls τ} -> p ≈ᵖ p
refl-≈ᵖ {p = p} = εᵖ-≡ refl-≈ˢ refl-≈ -- εᵖ-≡ ? ? 

sym-≈ᵖ : ∀ {l τ ls} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₁
sym-≈ᵖ (εᵖ-≡ x y) = εᵖ-≡ (sym-≈ˢ x) (sym-≈ y) --  εᵖ-≡ (sym x)

trans-≈ᵖ : ∀ {l τ ls} {p₁ p₂ p₃ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₂ ≈ᵖ p₃ -> p₁ ≈ᵖ p₃
trans-≈ᵖ (εᵖ-≡ x₁ y₁) (εᵖ-≡ x₂ y₂) = εᵖ-≡ (trans-≈ˢ x₁ x₂) (trans-≈ y₁ y₂)

-- My definition of l-equivalence for programs corresponds to the equivalence of the erasure of two programs 
unlift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂
unlift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} (εᵖ-≡ (εˢ-≡ eq₁) (ε-≡ eq₂)) rewrite eq₁ | eq₂ = refl

lift-≈ᵖ : ∀ {lₐ ls τ} {p₁ p₂ : Program ls τ} -> εᵖ lₐ p₁ ≡ εᵖ  lₐ p₂ -> p₁ ≈ᵖ p₂
lift-≈ᵖ {p₁ = ⟨ x ∥ x₁ ⟩} {⟨ x₂ ∥ x₃ ⟩} eq = εᵖ-≡ (εˢ-≡ (store-≡ eq)) (ε-≡ (term-≡ eq))

--------------------------------------------------------------------------------

-- Single step simulation typed terms:
--
-- p₁ ≈ᵖ p₂ , p₁ ⟼ p₁' , p₂ ⟼ p₂'
-- then
-- p₁' ≈ᵖ p₂' 
--
-- By distributivity of ε the reductions steps are mapped in reductions of the erased terms:
-- p₁ ⟼ p₁'     to      (ε lₐ p₁) ⟼ (ε lₐ p₁')
-- p₂ ⟼ p₂'     to      (ε lₐ p₂) ⟼ (ε lₐ p₂')
-- Since the source terms are equivalent (ε lₐ p₁ ≡ ε lₐ p₂) by definition of low equivalence (p₁ ≈ᵖ p₂)
-- and the semantics is deterministic then the reduced erased terms are equivalent (ε lₐ p₁' ≡ ε lₐ p₂')
-- This implies that p₁' and p₂' are low-equivalent (p₁ ≈ᵖ p₂).
simulation : ∀ {l ls τ} {p₁ p₂ p₁' p₂' : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᵖ p₂'
simulation {l} eq Σ₁ Σ₂ = lift-≈ᵖ (aux (unlift-≈ᵖ eq) (εᵖ-dist l Σ₁) (εᵖ-dist l Σ₂))
  where aux : ∀ {τ ls} {p₁ p₂ p₃ p₄ : Program ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₃ -> p₂ ⟼ p₄ -> p₃ ≡ p₄
        aux refl Σ₁ Σ₂ = determinism Σ₁ Σ₂


-- Given two l-equivalent terms if one is a value then either also the other is a value or it is ∙
inspectValue : ∀ {{lₐ}} {τ} {t v : CTerm τ} -> IsValue v -> t ≈ v ->  IsValue (ε lₐ t) ⊎ ε lₐ t ≡ ∙
inspectValue {{lₐ}} isV (ε-≡ eq) = aux isV eq
  where  aux : ∀ {τ} {t v : CTerm τ} -> IsValue v -> ε lₐ t ≡ ε lₐ v ->  IsValue (ε lₐ t) ⊎ ε lₐ t ≡ ∙  
         aux （） eq rewrite eq = inj₁ （）
         aux True eq rewrite eq = inj₁ True
         aux False eq rewrite eq = inj₁ False
         aux (Abs t₁) eq rewrite eq = inj₁ (Abs _)
         aux ξ eq rewrite eq = inj₁ ξ
         aux {τ = Mac lᵈ τ} (Mac t₁) eq with lᵈ ⊑? lₐ
         aux {Mac lᵈ τ} (Mac t₁) eq | yes p rewrite eq = inj₁ (Mac (ε lₐ t₁))
         aux {Mac lᵈ τ} {t = t} (Mac t₁) eq | no ¬p rewrite eq = inj₂ eq
         aux {τ = Mac lᵈ τ} (Macₓ e) eq with lᵈ ⊑? lₐ
         aux {Mac lᵈ τ} (Macₓ e) eq | yes p rewrite eq = inj₁ (Macₓ (ε lₐ e))
         aux {Mac lᵈ τ} {t = t} (Macₓ e) eq | no ¬p rewrite eq = inj₂ eq 
         aux {Res lᵈ τ} (Res t₁) eq with lᵈ ⊑? lₐ
         aux {Res lᵈ τ} (Res t₁) eq | yes p rewrite eq = inj₁ (Res (ε lₐ t₁))
         aux {Res lᵈ τ} (Res t₁) eq | no ¬p rewrite eq = inj₁ (Res ∙)
         aux {Res lᵈ τ} (Resₓ e) eq with lᵈ ⊑? lₐ
         aux {Res lᵈ τ} (Resₓ e) eq | yes p rewrite eq = inj₁ (Resₓ (ε lₐ e))
         aux {Res lᵈ τ} (Resₓ e) eq | no ¬p rewrite eq = inj₁ (Res ∙)
         aux zero eq rewrite eq = inj₁ zero
         aux (suc n) eq rewrite eq = inj₁ (suc (ε lₐ n))

-- Bullet can only reduce to itself, therefore it will not change the program
∙⟼⋆∙ : ∀ {τ ls} {p₁ p₂ : Program ls τ} -> p₁ ⟼⋆ p₂ -> term p₁ ≡ ∙ -> p₁ ≡ p₂
∙⟼⋆∙ [] eq = refl
∙⟼⋆∙ (Pure Hole ∷ ss) refl = ∙⟼⋆∙ ss refl

-- Multi-step simulation
simulation⋆ : ∀ {lₐ τ ls} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⟼⋆ v₁ -> IsValue (term v₁) -> p₂ ⟼⋆ v₂ -> IsValue (term v₂) -> v₁ ≈ᵖ v₂
simulation⋆ eq [] isV₁ [] isV₂ = eq
simulation⋆ (εᵖ-≡ x y) [] isV₁ (s₄ ∷ ss₂) isV₂ with inspectValue isV₁ (sym-≈ y)
simulation⋆ {lₐ} (εᵖ-≡ x y) [] isV₁ (s ∷ ss) isV₂ | inj₁ isVε = ⊥-elim (valueNotRedex _ isVε (Step (εᵖ-dist lₐ s)))
simulation⋆ {lₐ} {τ} (εᵖ-≡ x y) [] isV₁ (s ∷ ss) isV₂ | inj₂ ε≡∙ = trans-≈ᵖ (εᵖ-≡ x y) (lift-≈ᵖ (∙⟼⋆∙ (εᵖ-dist⋆ lₐ (s ∷ ss)) ε≡∙))
simulation⋆ (εᵖ-≡ x y) (s ∷ ss) isV₁ [] isV₂ with inspectValue isV₂ y
simulation⋆ (εᵖ-≡ x y) (s ∷ ss) isV₁ [] isV₂ | inj₁ isVε = ⊥-elim (valueNotRedex _ isVε (Step (εᵖ-dist _ s)))
simulation⋆ {lₐ} (εᵖ-≡ x y) (s ∷ ss) isV₁ [] isV₂ | inj₂ ε≡∙ = sym-≈ᵖ (trans-≈ᵖ (sym-≈ᵖ (εᵖ-≡ x y)) (lift-≈ᵖ (∙⟼⋆∙ (εᵖ-dist⋆ lₐ (s ∷ ss)) ε≡∙)))
simulation⋆ eq (Σ₁ ∷ ss₁) isV₁ (Σ₂ ∷ ss₂) isV₂ = simulation⋆ (simulation eq Σ₁ Σ₂) ss₁ isV₁ ss₂ isV₂

non-interference  : ∀ {l ls τ} {p₁ p₂ v₁ v₂ : Program ls τ} -> p₁ ≈ᵖ p₂ -> p₁ ⇓ v₁ -> p₂ ⇓ v₂ -> v₁ ≈ᵖ v₂
non-interference eq (BigStep isV₁ ss₁) (BigStep isV₂ ss₂) = simulation⋆ eq ss₁ isV₁ ss₂ isV₂

--------------------------------------------------------------------------------

data IsMacValue {l : Label} {τ : Ty} : CTerm (Mac l τ) -> Set where
  Mac : ∀ {t} -> IsMacValue (Mac t)
  Macₓ : ∀ {t} -> IsMacValue (Macₓ t)
  
mac-is-value : ∀ {τ lₐ l t₁} {t₂ : CTerm (Mac l τ)} (p : l ⊑ lₐ) -> IsMacValue t₁ -> t₁ ≡ ε-Mac lₐ (yes p) t₂ -> IsValue t₂
mac-is-value {t₂ = Var x} p () refl 
mac-is-value {t₂ = App t₂ t₃} p () refl 
mac-is-value {t₂ = If t₂ Then t₃ Else t₄} p () refl 
mac-is-value {t₂ = Return t₂} p () refl 
mac-is-value {t₂ = t₂ >>= t₃} p () refl 
mac-is-value {t₂ = Throw t₂} p () refl 
mac-is-value {t₂ = Catch t₂ t₃} p () refl 
mac-is-value {t₂ = Mac t₂} p Mac refl = Mac t₂
mac-is-value {t₂ = Macₓ t₂} p Macₓ refl = Macₓ t₂
mac-is-value {lₐ = lₐ} {t₂ = label {h = h} x t₂} p isM refl with h ⊑? lₐ
mac-is-value {._} {lₐ} {l} {._} {label x t₂} p₁ () refl | yes p
mac-is-value {._} {lₐ} {l} {._} {label x t₂} p () refl | no ¬p
mac-is-value {t₂ = unlabel x t₂} p () refl 
mac-is-value {lₐ = lₐ} {t₂ = join {h = h} x t₂} p isM refl  with h ⊑? lₐ
mac-is-value {._} {lₐ} {l} {._} {join x t₂} p₁ () refl | yes p
mac-is-value {._} {lₐ} {l} {._} {join x t₂} p () refl | no ¬p 
mac-is-value {t₂ = read x t₂} p () refl 
mac-is-value {t₂ = write x t₂ t₃} p () refl 
mac-is-value {t₂ = new x t₂} p () refl 
mac-is-value {t₂ = fork x t₂} p () refl 
mac-is-value {t₂ = newMVar x} p () refl 
mac-is-value {t₂ = takeMVar t₂} p () refl 
mac-is-value {t₂ = putMVar t₂ t₃} p () refl 
mac-is-value {t₂ = ∙} p () refl 

valueᴸ : ∀ {l lₐ τ} {t₁ t₂ : CTerm (Mac l τ)} -> l ⊑ lₐ -> IsValue t₁ -> t₁ ≈-⟨ lₐ ⟩ t₂ -> IsValue t₂
valueᴸ {l} {lₐ} p (Mac t) (ε-≡ x) with l ⊑? lₐ
valueᴸ {t₂ = t₂} p₁ (Mac t) (ε-≡ x) | yes p = mac-is-value p Mac x
valueᴸ p (Mac t) (ε-≡ x) | no ¬p = ⊥-elim (¬p p)
valueᴸ {l} {lₐ} p (Macₓ e) (ε-≡ x) with l ⊑? lₐ
valueᴸ p₁ (Macₓ e) (ε-≡ x) | yes p = mac-is-value p Macₓ x
valueᴸ p (Macₓ e) (ε-≡ x) | no ¬p = ⊥-elim (¬p p)

--------------------------------------------------------------------------------
-- Hard lemmas to prove right now.
-- It might be easier to prove the following lemmas instead: Σ₁ ≈ Σ₂ ∧ t₁ ≈ t₂ ∧ Redex Σ₁ t₁ ∧ Stuck Σ₂ t₂ => ⊥

-- TODO this seems very tricky to prove, especially with the current non-structural definition of l-equivalence
postulate redexᴸ : ∀ {l τ lₐ ls} {p₁ p₂ p₁' : Program ls (Mac l τ)} -> 
              let ⟨ Σ₁ ∥ t₁ ⟩ = p₁
                  ⟨ Σ₂ ∥ t₂ ⟩ = p₂
                  ⟨ Σ₁' ∥ t₁' ⟩ = p₁' in  (x : l ⊑ lₐ) -> p₁ ⟼ p₂ -> p₁ ≈ᵖ-⟨ lₐ ⟩ p₁' -> Redex Σ₁' t₁'

-- TODO this might be even harder because of the functional representation of negation
postulate stuckᴸ : ∀ {τ l ls lₐ} -> {p p' : Program ls (Mac l τ)} ->
                     let ⟨ Σ ∥ t ⟩ = p
                         ⟨ Σ' ∥ t' ⟩ = p' in l ⊑ lₐ -> p ≈ᵖ-⟨ lₐ ⟩ p' -> Stuck Σ t -> Stuck Σ' t'

--------------------------------------------------------------------------------
