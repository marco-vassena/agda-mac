module Typed.Valid where

open import Data.Product
open import Typed.Base
open import Typed.Semantics
import Data.List as L

-- Now that we have memory we have to ensure that memory references are all valid.
-- The following data type is such a proof.

data Valid {Δ} (Δᵐ : Context) : ∀ {τ} -> Term Δ τ -> Set where
  （） : Valid Δᵐ （）
  True : Valid Δᵐ True
  False : Valid Δᵐ False

  Var : ∀ {τ } -> (p : τ ∈ Δ) -> Valid Δᵐ (Var p)
  App : ∀ {α β}{f : Term Δ (α => β)} {x : Term Δ α} ->
          Valid Δᵐ f -> Valid Δᵐ x -> Valid Δᵐ (App f x)
  Abs : ∀ {α β} {t : Term (α ∷ Δ) β} -> Valid Δᵐ t -> Valid Δᵐ (Abs t)

  ξ : Valid Δᵐ ξ

  Mac : ∀ {α} {l : Label} {t : Term Δ α} ->
          Valid Δᵐ t -> Valid Δᵐ (Mac t)
  Macₓ : ∀ {α} {l : Label} {e : Term Δ Exception} ->
           Valid Δᵐ e -> Valid Δᵐ (Macₓ {α = α} e)

  Res : ∀ {α}  {l : Label} {t : Term Δ α} ->
           Valid Δᵐ t -> Valid Δᵐ (Res t)
  Resₓ : ∀ {α} {l : Label}{e : Term Δ Exception} ->
           Valid Δᵐ e -> Valid Δᵐ (Resₓ {α = α} e)

  Ref : ∀ {α n} {l : Label} -> TypedIx α n Δᵐ -> Valid Δᵐ (Ref {{α}} n)

  If_Then_Else_ : ∀ {α} {c : Term Δ Bool} {t e : Term Δ α} ->
                  Valid Δᵐ c -> Valid Δᵐ t -> Valid Δᵐ e -> Valid Δᵐ (If c Then t Else e)

  Return : ∀ {{l}} {α} {t : Term Δ α} -> Valid Δᵐ t -> Valid Δᵐ (Return t)
  
  _>>=_ : ∀ {{l}} {α β} {t₁ : Term Δ (Mac l α)} {t₂ : Term Δ (α => Mac l β)} ->
            Valid Δᵐ t₁ -> Valid Δᵐ t₂ -> Valid Δᵐ (t₁ >>= t₂)

  Throw : ∀ {{l : Label}} {{α : Ty}} {t : Term Δ Exception} ->
            Valid Δᵐ t -> Valid Δᵐ (Throw {{l = l}} {{α}} t)

  Catch : ∀ {{l}} {α}  -> {t : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
            Valid Δᵐ t -> Valid Δᵐ h -> Valid Δᵐ (Catch t h)

  label : ∀ {l h α} {t : Term Δ α} -> (p : l ⊑ h) -> Valid Δᵐ t -> Valid Δᵐ (label p t)
  unlabel : ∀ {l h α} {t : Term Δ (Labeled l α)} ->
              (p : l ⊑ h) -> Valid Δᵐ t -> Valid Δᵐ (unlabel p t)

  join : ∀ {l h α} {t : Term Δ (Mac h α)} ->
           (p : l ⊑ h) -> Valid Δᵐ t -> Valid Δᵐ (join p t)

  read : ∀ {α l h} {t : Term Δ (Ref l α)} ->
           (p : l ⊑ h) -> Valid Δᵐ t -> Valid Δᵐ (read p t)

  write : ∀ {α l h} {t₁ : Term Δ (Ref h α)} -> {t₂ : Term Δ α} ->
            (p : l ⊑ h) -> Valid Δᵐ t₁ -> Valid Δᵐ t₂ -> Valid Δᵐ (write p t₁ t₂)
  
  new : ∀ {α l h} {t : Term Δ α} -> (p : l ⊑ h) -> Valid Δᵐ t ->
          Valid Δᵐ (new p t)
          
  ∙ : ∀ {τ} -> Valid Δᵐ (∙ {{τ}})


data ValidMemory (Δ : Context) : ∀ {Δᵐ} -> (m : Memory Δᵐ) -> Set where
  [] : ValidMemory Δ []
  _∷_ : ∀ {τ Δᵐ} {c : CTerm τ} {m : Memory Δᵐ} -> Valid Δ c -> ValidMemory Δ m -> ValidMemory Δ (c ∷ m)
  ∙ : ∀ {Δᵐ} -> ValidMemory Δ {Δᵐ} ∙ 
 
--------------------------------------------------------------------------------
-- Lemmas and proofs
--------------------------------------------------------------------------------

-- This lemma shows that the context of the memory in a step always
-- grows, but never shrinks, i.e. the initial memory context is a subset
-- of the final memory context.
context-⊆ : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
context-⊆ (Pure x) = refl-⊆
context-⊆ (BindCtx s) = context-⊆ s
context-⊆ (CatchCtx s) = context-⊆ s
context-⊆ (unlabelCtx p s) = context-⊆ s
context-⊆ (joinCtx p s) = context-⊆ s
context-⊆ (join p) = refl-⊆
context-⊆ (joinEx p) = refl-⊆
context-⊆ (new p) = snoc-⊆
context-⊆ (writeCtx p s) = context-⊆ s
context-⊆ (write p i) = refl-⊆
context-⊆ (readCtx p s) = context-⊆ s
context-⊆ (read p i) = refl-⊆
context-⊆ (Hole x) = x

--------------------------------------------------------------------------------


-- If a term has valid references with respect to a certain memory context Δ₁
-- then it is also valid in any memory context Δ₂ that extends it (Δ₁ ⊆ Δ₂).
extendValid : ∀ {Δ Δ₁ Δ₂ τ} {t : Term Δ τ} ->
               Valid Δ₁ t -> Δ₁ ⊆ Δ₂ -> Valid Δ₂ t
extendValid （） p = （）
extendValid True p = True
extendValid False p = False
extendValid (Var p) p₁ = Var p
extendValid (App v v₁) p = App (extendValid v p) (extendValid v₁ p)
extendValid (Abs v) p = Abs (extendValid v p)
extendValid ξ p = ξ
extendValid (Mac v) p = Mac (extendValid v p)
extendValid (Macₓ v) p = Macₓ (extendValid v p)
extendValid (Res v) p = Res (extendValid v p)
extendValid (Resₓ v) p = Resₓ (extendValid v p)
extendValid (Ref r) p = Ref (castIx r p)
extendValid (If v Then v₁ Else v₂) p
  = If extendValid v p Then extendValid v₁ p Else extendValid v₂ p
extendValid (Return v) p = Return (extendValid v p)
extendValid (v >>= v₁) p = (extendValid v p) >>= (extendValid v₁ p)
extendValid (Throw v) p = Throw (extendValid v p)
extendValid (Catch v v₁) p = Catch (extendValid v p) (extendValid v₁ p)
extendValid (label x v) p = label x (extendValid v p)
extendValid (unlabel x v) p = unlabel x (extendValid v p)
extendValid (join x v) p = join x (extendValid v p)
extendValid (read x v) p = read x (extendValid v p)
extendValid (write x v v₁) p = write x (extendValid v p) (extendValid v₁ p)
extendValid (new x v) p = new x (extendValid v p)
extendValid ∙ p = ∙

extendValidMemory : ∀ {Δ₁ Δ₂ Δᵐ} {m : Memory Δᵐ} -> ValidMemory Δ₁ m -> Δ₁ ⊆ Δ₂ -> ValidMemory Δ₂ m
extendValidMemory [] p = []
extendValidMemory (x ∷ m) p = (extendValid x p) ∷ extendValidMemory m p
extendValidMemory ∙ p = ∙

lookupValidMemory : ∀ {Δᵐ Δ τ} {m : Memory Δᵐ} -> (p : τ ∈ Δᵐ) -> ValidMemory Δ m -> Valid Δ (m [ p ])
lookupValidMemory Here (x ∷ m) = x
lookupValidMemory (There p) (x ∷ m) = lookupValidMemory p m
lookupValidMemory r ∙ = ∙

validMemoryUpdate : ∀ {Δ Δᵐ τ} {m : Memory Δᵐ} {c : CTerm τ} ->
                    ValidMemory Δ m -> (p : τ ∈ Δᵐ) -> Valid Δ c  -> ValidMemory Δ (m [ p ]≔ c)
validMemoryUpdate [] () v
validMemoryUpdate (x ∷ vᵐ) Here v = v ∷ vᵐ
validMemoryUpdate (x ∷ vᵐ) (There p) v = x ∷ validMemoryUpdate vᵐ p v
validMemoryUpdate ∙ Here v = ∙
validMemoryUpdate ∙ (There m) v = ∙

validMemoryNew : ∀ {Δ Δᵐ τ} {m : Memory Δᵐ} {c : CTerm τ} ->
                   ValidMemory Δ m -> Valid Δ c -> ValidMemory Δ (m ∷ʳ c)
validMemoryNew [] v = v ∷ []
validMemoryNew (x ∷ Γ₁) v = x ∷ validMemoryNew Γ₁ v
validMemoryNew ∙ _ = ∙

valid-wken :  ∀ {τ Δ₁ Δ₂ Δᵐ} {t : Term Δ₁ τ} -> Valid Δᵐ t -> (p : Δ₁ ⊆ˡ Δ₂) -> Valid Δᵐ (wken t p)
valid-wken （） p = （）
valid-wken True p = True
valid-wken False p = False
valid-wken (Var p) p₁ = Var (wken-∈ p p₁)
valid-wken (App v v₁) p = App (valid-wken v p) (valid-wken v₁ p)
valid-wken (Abs v) p = Abs (valid-wken v (cons p))
valid-wken ξ p = ξ
valid-wken (Mac v) p = Mac (valid-wken v p)
valid-wken (Macₓ v) p = Macₓ (valid-wken v p)
valid-wken (Res v) p = Res (valid-wken v p)
valid-wken (Resₓ v) p = Resₓ (valid-wken v p)
valid-wken (Ref x) p = Ref x
valid-wken (If v Then v₁ Else v₂) p = If valid-wken v p Then valid-wken v₁ p Else valid-wken v₂ p
valid-wken (Return v) p = Return (valid-wken v p)
valid-wken (v >>= v₁) p = (valid-wken v p) >>= (valid-wken v₁ p)
valid-wken (Throw v) p = Throw (valid-wken v p)
valid-wken (Catch v v₁) p = Catch (valid-wken v p) (valid-wken v₁ p)
valid-wken (label p v) p₁ = label p (valid-wken v p₁)
valid-wken (unlabel p v) p₁ = unlabel p (valid-wken v p₁)
valid-wken (join p v) p₁ = join p (valid-wken v p₁)
valid-wken (read p v) p₁ = read p (valid-wken v p₁)
valid-wken (write p v v₁) p₁ = write p (valid-wken v p₁) (valid-wken v₁ p₁)
valid-wken (new p v) p₁ = new p (valid-wken v p₁)
valid-wken ∙ p = ∙

valid-var-subst : ∀ {α β Δᵐ} (Δ₁ Δ₂ : Context) {x : Term Δ₂ α} -> (p : β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) -> Valid Δᵐ x -> Valid Δᵐ (var-subst Δ₁ Δ₂ x p)
valid-var-subst [] Δ₂ Here x₁ = x₁
valid-var-subst [] Δ₂ (There p) x₁ = Var p
valid-var-subst (β ∷ Δ₁) Δ₂ Here x₂ = Var Here
valid-var-subst (_ ∷ Δ₁) Δ₂ (There p) x = valid-wken (valid-var-subst Δ₁ Δ₂ p x) (drop refl-⊆ˡ)

valid-tm-subst : ∀ {α τ Δᵐ} (Δ₁ Δ₂ : Context) {x : Term Δ₂ α} {t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ} ->
                 Valid Δᵐ x -> Valid Δᵐ t -> Valid Δᵐ (tm-subst Δ₁ Δ₂ x t)
valid-tm-subst Δ₁ Δ₂ xᵛ （） = （）
valid-tm-subst Δ₁ Δ₂ xᵛ True = True
valid-tm-subst Δ₁ Δ₂ xᵛ False = False
valid-tm-subst Δ₁ Δ₂ xᵛ (Var p) = valid-var-subst Δ₁ Δ₂ p xᵛ
valid-tm-subst Δ₁ Δ₂ xᵛ (App tᵛ tᵛ₁) = App (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ₁)
valid-tm-subst Δ₁ Δ₂ xᵛ (Abs tᵛ) = Abs (valid-tm-subst (_ ∷ Δ₁) Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ ξ = ξ
valid-tm-subst Δ₁ Δ₂ xᵛ (Mac tᵛ) = Mac (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (Macₓ tᵛ) = Macₓ (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (Res tᵛ) = Res (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (Resₓ tᵛ) = Resₓ (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (Ref x₁) = Ref x₁
valid-tm-subst Δ₁ Δ₂ xᵛ (If tᵛ Then tᵛ₁ Else tᵛ₂)
  = If (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) Then (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ₁) Else (valid-tm-subst  Δ₁ Δ₂ xᵛ tᵛ₂)
valid-tm-subst Δ₁ Δ₂ xᵛ (Return tᵛ) = Return (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (tᵛ >>= tᵛ₁) = (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) >>= (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ₁)
valid-tm-subst Δ₁ Δ₂ xᵛ (Throw tᵛ) = Throw (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (Catch tᵛ tᵛ₁) = Catch (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ₁)
valid-tm-subst Δ₁ Δ₂ xᵛ (label p tᵛ) = label p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (unlabel p tᵛ) = unlabel p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (join p tᵛ) = join p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (read p tᵛ) = read p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ (write p tᵛ tᵛ₁) = write p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ₁)
valid-tm-subst Δ₁ Δ₂ xᵛ (new p tᵛ) = new p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ)
valid-tm-subst Δ₁ Δ₂ xᵛ ∙ = ∙

valid-subst : ∀ {Δ Δᵐ α β} {x : Term Δ α} {t : Term (α ∷ Δ) β} -> Valid Δᵐ x -> Valid Δᵐ t -> Valid Δᵐ (subst x t)
valid-subst x t = valid-tm-subst [] _ x t


stepValidCTerm : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> Valid Δ₂ c₂
stepValidCTerm (Pure (AppL x₁)) (App v v₁) m = App (stepValidCTerm (Pure x₁) v m) v₁
stepValidCTerm (Pure Beta) (App (Abs v) v₁) m = valid-subst v₁ v
stepValidCTerm (Pure (IfCond x)) (If v Then v₁ Else v₂) m = If (stepValidCTerm (Pure x) v m) Then v₁ Else v₂
stepValidCTerm (Pure IfTrue) (If True Then v₁ Else v₂) m = v₁
stepValidCTerm (Pure IfFalse) (If False Then v₁ Else v₂) m = v₂
stepValidCTerm (Pure Return) (Return v) m = Mac v
stepValidCTerm (Pure Throw) (Throw v) m = Macₓ v
stepValidCTerm (Pure Bind) (Mac v >>= v₁) m = App v₁ v
stepValidCTerm (Pure BindEx) (Macₓ v >>= v₁) m = Throw v
stepValidCTerm (Pure Catch) (Catch (Mac v) v₁) m = Return v
stepValidCTerm (Pure CatchEx) (Catch (Macₓ v) v₁) m = App v₁ v
stepValidCTerm (Pure (label p)) (label .p v) m = Return (Res v)
stepValidCTerm (Pure (unlabel p)) (unlabel .p (Res v)) m = Return v
stepValidCTerm (Pure (unlabelEx p)) (unlabel .p (Resₓ v)) m = Throw v
stepValidCTerm (Pure Hole) ∙ m = ∙
stepValidCTerm (BindCtx s) (v >>= v₁) m = (stepValidCTerm s v m) >>= extendValid v₁ (context-⊆ s)
stepValidCTerm (CatchCtx s) (Catch v v₁) m = Catch (stepValidCTerm s v m) (extendValid v₁ (context-⊆ s))
stepValidCTerm (unlabelCtx p s) (unlabel .p v) m = unlabel p (stepValidCTerm s v m)
stepValidCTerm (joinCtx p s) (join .p v) m = join p (stepValidCTerm s v m)
stepValidCTerm (join p) (join .p (Mac v)) m = Return (Res v)
stepValidCTerm (joinEx p) (join .p (Macₓ v)) m = Return (Resₓ v)
stepValidCTerm {Δ₁ = Δ₁} (new p) (new .p v) m = Return (Ref (newTypeIx Δ₁))
stepValidCTerm (writeCtx p s) (write .p v v₁) m = write p (stepValidCTerm s v m) (extendValid v₁ (context-⊆ s))
stepValidCTerm (write p i) v m = Return （）
stepValidCTerm (readCtx p s) (read .p v) m = read p (stepValidCTerm s v m)
stepValidCTerm (read p i) (read .p (Ref x)) m = Return (lookupValidMemory (# i) m)
stepValidCTerm (Hole x) ∙ m = ∙

stepValidMemory : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> ValidMemory Δ₂ m₂
stepValidMemory (Pure x) v m = m
stepValidMemory (BindCtx s) (v >>= v₁) m = stepValidMemory s v m
stepValidMemory (CatchCtx s) (Catch v v₁) m = stepValidMemory s v m
stepValidMemory (unlabelCtx p s) (unlabel .p v) m = stepValidMemory s v m
stepValidMemory (joinCtx p s) (join .p v) m = stepValidMemory s v m
stepValidMemory (join p) (join .p v) m = m
stepValidMemory (joinEx p) v m = m
stepValidMemory (new p) (new .p v) m = extendValidMemory (validMemoryNew m v) snoc-⊆
stepValidMemory (writeCtx p s) (write .p v v₁) m = stepValidMemory s v m
stepValidMemory (write p i) (write .p (Ref x) v₁) m = validMemoryUpdate m (# i) v₁
stepValidMemory (readCtx p s) (read .p v) m = stepValidMemory s v m
stepValidMemory (read p i) v m = m
stepValidMemory (Hole x) ∙ m = ∙

-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
-- The final memory is also valid.
stepValid : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> 
              ValidMemory Δ₂ m₂ × Valid Δ₂ c₂
stepValid s v m = (stepValidMemory s v m) , (stepValidCTerm s v m)
