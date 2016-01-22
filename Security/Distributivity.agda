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

ε-wken : ∀ {α Δ₁ Δ₂} -> (lₐ : Label) -> (t : Term Δ₁ α) (p : Δ₁ ⊆ˡ Δ₂) -> ε lₐ (wken t p) ≡ wken (ε lₐ t) p

ε-Mac-wken : ∀ {lᵈ α Δ₁ Δ₂} -> (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) (t : Term Δ₁ (Mac lᵈ α)) (p : Δ₁ ⊆ˡ Δ₂) -> ε-Mac lₐ x (wken t p) ≡ wken (ε-Mac lₐ x t) p
ε-Mac-wken lₐ (yes p) (Var x₁) p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Var x₁) p = refl
ε-Mac-wken lₐ (yes x) (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-Mac-wken lₐ (no x) (App t t₁) p = refl
ε-Mac-wken lₐ (yes p) (If t Then t₁ Else t₂) p₁
  rewrite ε-wken lₐ t p₁ | ε-Mac-wken lₐ (yes p) t₁ p₁ | ε-Mac-wken lₐ (yes p) t₂ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (If t Then t₁ Else t₂) p = refl
ε-Mac-wken lₐ (yes p) (Return t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Return t) p = refl
ε-Mac-wken lₐ (yes p) (t >>= t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (t >>= t₁) p = refl
ε-Mac-wken lₐ (yes p) (Throw t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Throw t) p = refl
ε-Mac-wken lₐ (yes p) (Catch t t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Catch t t₁) p = refl
ε-Mac-wken lₐ (yes p) (Mac t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Mac t) p = refl
ε-Mac-wken lₐ (yes p) (Macₓ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Macₓ t) p = refl
ε-Mac-wken lₐ (yes p) (label {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (label x₁ t) p₂ | yes p rewrite ε-wken lₐ t p₂ = refl
ε-Mac-wken lₐ (yes p) (label x₁ t) p₁ | no ¬p = refl 
ε-Mac-wken lₐ (no ¬p) (label x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (unlabel x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (unlabel x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (join {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (join x₁ t) p₂ | yes p rewrite ε-Mac-wken lₐ (yes p) t p₂ = refl
ε-Mac-wken lₐ (yes p) (join x₁ t) p₁ | no ¬p = refl
ε-Mac-wken lₐ (no ¬p) (join x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (read x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (read x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (write x₁ t t₁) p₁ rewrite ε-wken lₐ t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (write x₁ t t₁) p = refl
ε-Mac-wken lₐ (yes p) (new x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (new x₁ t) p = refl
ε-Mac-wken lₐ (yes p) ∙ p₁ = refl
ε-Mac-wken lₐ (no ¬p) ∙ p = refl

ε-wken {（）} lₐ （） p = refl
ε-wken {（）} lₐ (Var x) p = refl
ε-wken {（）} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {（）} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {（）} lₐ ∙ p = refl
ε-wken {Bool} lₐ True p = refl
ε-wken {Bool} lₐ False p = refl
ε-wken {Bool} lₐ (Var x) p = refl
ε-wken {Bool} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Bool} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Bool} lₐ ∙ p = refl
ε-wken {α => α₁} lₐ (Var x) p = refl
ε-wken {α => α₁} lₐ (Abs t) p
  rewrite ε-wken lₐ t (cons p) = refl
ε-wken {α => α₁} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {α => α₁} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {α => α₁} lₐ ∙ p = refl
ε-wken {Mac lᵈ α} lₐ t p rewrite ε-Mac-wken lₐ (lᵈ ⊑? lₐ) t p = refl
ε-wken {Labeled x α} lₐ (Var x₁) p = refl
ε-wken {Labeled x α} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Labeled x α} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Labeled lᵈ α} lₐ (Res t) p with lᵈ ⊑? lₐ
ε-wken {Labeled lᵈ α} lₐ (Res t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Labeled lᵈ α} lₐ (Res t) p | no ¬p = refl
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p with lᵈ ⊑? lₐ
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Labeled lᵈ α} lₐ (Resₓ t) p | no ¬p = refl
ε-wken {Labeled x α} lₐ ∙ p = refl
ε-wken {Exception} lₐ (Var x) p = refl
ε-wken {Exception} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Exception} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Exception} lₐ ξ p = refl
ε-wken {Exception} lₐ ∙ p = refl
ε-wken {Ref x α} lₐ (Var x₁) p = refl
ε-wken {Ref x α} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Ref x α} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Ref x α} lₐ (Ref x₁) p = refl
ε-wken {Ref x α} lₐ ∙ p = refl

ε-subst : ∀ {Δ α β} (lₐ : Label) (x : Term Δ α) (t : Term (α ∷ Δ) β) -> subst (ε lₐ x) (ε lₐ t) ≡ ε lₐ (subst x t)
ε-subst lₐ x t = ε-tm-subst [] _ x t
  where
        ε-tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ) ->
               tm-subst Δ₁ Δ₂ (ε lₐ x) (ε lₐ t) ≡ ε lₐ (tm-subst Δ₁ Δ₂ x t)

        ε-Mac-tm-subst : ∀ {lᵈ α  τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) (Mac lᵈ τ)) (p : Dec (lᵈ ⊑ lₐ)) ->
                         tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ p t) ≡ ε-Mac lₐ p (tm-subst Δ₁ Δ₂ x t)

        ε-var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) -> (p : β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                      var-subst Δ₁ Δ₂ (ε lₐ x) p ≡ ε lₐ (var-subst Δ₁ Δ₂ x p)
        ε-var-subst [] Δ₂ t₁ Here = refl
        ε-var-subst [] Δ t₁ (There p) rewrite εVar≡Var lₐ p = refl
        ε-var-subst (（） ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Bool ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst ((β => β₁) ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here with lᵈ ⊑? lₐ
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | yes p = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | no ¬p = refl
        ε-var-subst (Labeled x₁ β ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Exception ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Ref x₁ β ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (x₁ ∷ Δ₁) Δ₂ t₁ (There p)
          rewrite ε-var-subst Δ₁ Δ₂ t₁ p | ε-wken lₐ (var-subst Δ₁ Δ₂ t₁ p) (drop {x₁} refl-⊆ˡ) = refl

        ε-Mac-var-subst : ∀ {lᵈ α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (y : Dec (lᵈ ⊑ lₐ)) -> (p : (Mac lᵈ β) ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                          tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ y (Var p)) ≡ ε-Mac lₐ y (var-subst Δ₁ Δ₂ x p)

        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (yes p) Here rewrite ε-Mac-extensional (yes p) (lᵈ ⊑? lₐ) x₁ = refl
        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (no ¬p) Here rewrite ε-Mac-extensional (no ¬p) (lᵈ ⊑? lₐ) x₁ =  refl
        ε-Mac-var-subst [] Δ x₁ (yes p) (There p₁) = refl
        ε-Mac-var-subst [] Δ x₁ (no ¬p) (There p) = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (yes p) Here = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (no ¬p) Here = refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (yes p) (There p₁)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (yes p) p₁ | ε-Mac-wken lₐ (yes p) (var-subst Δ₁ Δ₂ x₂ p₁) (drop {x₁} refl-⊆ˡ) =  refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (no ¬p) (There p)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (no ¬p) p | ε-Mac-wken lₐ (no ¬p) (var-subst Δ₁ Δ₂ x₂ p) (drop {x₁} refl-⊆ˡ) =  refl

        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ （） = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ True = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ False = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Abs t₁)
          rewrite ε-tm-subst (_ ∷ Δ₁) Δ₂ x₁ t₁ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Mac lᵈ τ} Δ₁ Δ₂ x₂ t₁ = ε-Mac-tm-subst Δ₁ Δ₂ x₂ t₁ (lᵈ ⊑? lₐ)
        ε-tm-subst {τ = Labeled x₁ τ} Δ₁ Δ₂ x₂ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₂ x₃ = refl
        ε-tm-subst {τ = Labeled l τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Labeled l τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | no ¬p = refl
        ε-tm-subst {τ = Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Labeled lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | no ¬p = refl
        ε-tm-subst {τ = Labeled x₁ τ} Δ₁ Δ₂ x₂ ∙ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ξ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ∙ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₃ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₁ (Ref x₃) = refl
        ε-tm-subst {τ = Ref l τ} Δ₁ Δ₂ x₂ ∙ = refl

        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Var p) x rewrite ε-Mac-var-subst Δ₁ Δ₂ x₁ x p = refl         
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₂ (yes p) | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₃ (yes p) = refl                        
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p₁) | yes p 
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p) | no ¬p = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p₁) | yes p
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p) | no ¬p = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl 
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (no ¬p) = refl

ε-Mac-subst : ∀ {lᵈ Δ α β} (lₐ : Label) (y : Dec (lᵈ ⊑ lₐ)) (x : Term Δ α) (t : Term (α ∷ Δ) (Mac lᵈ β))
              -> subst (ε lₐ x) (ε-Mac lₐ (lᵈ ⊑? lₐ) t) ≡ (ε-Mac lₐ y (subst x t))
ε-Mac-subst {lᵈ} lₐ y x t rewrite ε-Mac-extensional y (lᵈ ⊑? lₐ) (subst x t) = ε-subst lₐ x t

ε-Mac-CTerm≡∙ : ∀ {lᵈ τ} (lₐ : Label) (c : CTerm (Mac lᵈ τ)) (x : ¬ (lᵈ ⊑ lₐ)) -> ε-Mac lₐ (no x) c ≡ ∙
ε-Mac-CTerm≡∙ lₐ (Var ()) x₁
ε-Mac-CTerm≡∙ lₐ (App c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (If c Then c₁ Else c₂) x = refl
ε-Mac-CTerm≡∙ lₐ (Return c) x = refl
ε-Mac-CTerm≡∙ lₐ (c >>= c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Throw c) x = refl
ε-Mac-CTerm≡∙ lₐ (Catch c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Mac c) x = refl
ε-Mac-CTerm≡∙ lₐ (Macₓ c) x = refl
ε-Mac-CTerm≡∙ lₐ (label x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (unlabel x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (join x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (read x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (write x c c₁) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (new x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ ∙ x = refl

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

εᵐ-read' : ∀ {τ Δᵐ n} -> (lₐ : Label) (m : Memory Δᵐ) (i : TypedIx τ n Δᵐ) -> _[_] (εᵐ lₐ m) (# i)  ≡ ε lₐ (_[_] m (# i))
εᵐ-read' lₐ (x ∷ m) Here = refl
εᵐ-read' {τ} {.τ ∷ Δᵐ} lₐ ∙ Here rewrite ε∙≡∙ {τ} {[]} lₐ =  refl
εᵐ-read' lₐ (x ∷ m) (There i) rewrite εᵐ-read' lₐ m i = refl
εᵐ-read' {τ} lₐ ∙ (There i) rewrite ε∙≡∙ {τ} {[]} lₐ = refl

εᵐ-read : ∀ {τ n Δᵐ} (lₐ : Label) (m : Memory Δᵐ) (i : TypedIx τ n Δᵐ) -> (_[_] (εᵐ-Mac lₐ τ m) (# i)) ≡ ε lₐ (_[_] m  (# i))
εᵐ-read {（）} lₐ m i = εᵐ-read' lₐ m i
εᵐ-read {Bool} lₐ m i = εᵐ-read' lₐ m i
εᵐ-read {τ => τ₁} lₐ m i = εᵐ-read' lₐ m i
εᵐ-read {Mac lᵈ τ} lₐ m i = εᵐ-read' lₐ m i
εᵐ-read {Labeled lᵈ τ} lₐ m i with lᵈ ⊑? lₐ
εᵐ-read {Labeled lᵈ τ} lₐ m i | yes p = εᵐ-read' lₐ m i
εᵐ-read {Labeled lᵈ τ} lₐ (x ∷ m) Here | no ¬p = {!!}
εᵐ-read {Labeled lᵈ τ} lₐ ∙ Here | no ¬p = refl
εᵐ-read {Labeled lᵈ τ} lₐ (x ∷ m) (There i) | no ¬p rewrite εᵐ-read lₐ m i = {!refl!}
εᵐ-read {Labeled lᵈ τ} lₐ ∙ (There i) | no ¬p = refl
εᵐ-read {Exception} lₐ m i = εᵐ-read' lₐ m i
εᵐ-read {Ref x τ} lₐ m i = εᵐ-read' lₐ m i

εᵖ-Mac-dist : ∀ {lᵈ τ Δ₁ Δ₂} {p₁ : Program Δ₁ (Mac lᵈ τ)} {p₂ : Program Δ₂ (Mac lᵈ τ)}  (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) ->
            p₁ ⟼ p₂ -> εᵖ-Mac lₐ x p₁ ⟼ εᵖ-Mac lₐ x p₂
εᵖ-Mac-dist lₐ (yes p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (yes p) x)
εᵖ-Mac-dist lₐ (yes p) (BindCtx s) = BindCtx {!εᵖ-Mac-dist lₐ (yes p) s!} -- Do we need εᵐ-Mac ?
εᵖ-Mac-dist lₐ (yes p) (CatchCtx s) = CatchCtx (εᵖ-Mac-dist lₐ (yes p) s)
εᵖ-Mac-dist lₐ (yes p) (unlabelCtx p₁ s) = unlabelCtx p₁ (εᵖ-dist lₐ {!s!}) -- Do we need εᵐ-Mac ?
εᵖ-Mac-dist lₐ (yes p) (joinCtx p₁ s) = {!!}
εᵖ-Mac-dist lₐ (yes p) (join p₁) = {!!}
εᵖ-Mac-dist lₐ (yes p) (joinEx p₁) = {!!}
εᵖ-Mac-dist lₐ (yes p) (new {m = m} {t = t} p₁) rewrite εᵐ-new lₐ m t = new p₁
εᵖ-Mac-dist lₐ (yes p) (writeCtx p₁ s) = writeCtx p₁ (εᵖ-dist lₐ s)
εᵖ-Mac-dist lₐ (yes p) (write {m = m} {c = c} p₁ i) rewrite εᵐ-write lₐ m c i = write p₁ i
εᵖ-Mac-dist lₐ (yes p) (readCtx p₁ s) = readCtx p₁ (εᵖ-dist lₐ {!s!}) -- Do we need εᵐ-Mac ?
εᵖ-Mac-dist lₐ (yes p) (read p₁ i) = {!read p₁ i!} -- Do we need εᵐ-Mac ?
εᵖ-Mac-dist {τ = τ} {Δ₁} {Δ₂} lₐ (yes p) (Hole x) rewrite εᵐ∙≡∙ {Δ₁} lₐ τ | εᵐ∙≡∙ {Δ₂} lₐ τ = Hole x
εᵖ-Mac-dist lₐ (no ¬p) (Pure x) = Pure (ε-Mac-dist⇝ lₐ (no ¬p) x)
εᵖ-Mac-dist lₐ (no ¬p) (BindCtx s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (CatchCtx s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (unlabelCtx p s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (joinCtx p s) = Hole (context-⊆ s)
εᵖ-Mac-dist lₐ (no ¬p) (join p) = Hole refl-⊆
εᵖ-Mac-dist lₐ (no ¬p) (joinEx p) = Hole refl-⊆
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
