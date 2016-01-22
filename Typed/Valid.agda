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

context-⊆⋆ : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩ ⟼⋆ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
context-⊆⋆ [] = refl-⊆
context-⊆⋆ (x ∷ ss) = trans-⊆ (context-⊆ x) (context-⊆⋆ ss)

context-⊆⇓ :  ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩ ⇓ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
context-⊆⇓ (BigStep isV ss) = context-⊆⋆ ss

context-⊆ (Pure x) = refl-⊆
context-⊆ (BindCtx s) = context-⊆ s
context-⊆ (CatchCtx s) = context-⊆ s
context-⊆ (unlabelCtx p s) = context-⊆ s
context-⊆ (join p bs) = context-⊆⇓ bs
context-⊆ (joinEx p bs) = context-⊆⇓ bs
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



-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
-- The final memory is also valid.
valid⟼ :  ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> 
              ValidMemory Δ₂ m₂ × Valid Δ₂ c₂

valid⟼⋆ :  ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼⋆ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> 
              ValidMemory Δ₂ m₂ × Valid Δ₂ c₂
valid⟼⋆ [] v m = m , v
valid⟼⋆ (s ∷ ss) v m with valid⟼ s v m
... | m₂ , c₂ = valid⟼⋆ ss c₂ m₂

valid⇓ :  ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
              ⟨ m₁ ∥ c₁ ⟩ ⇓ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> 
              ValidMemory Δ₂ m₂ × Valid Δ₂ c₂
valid⇓ (BigStep isV ss) v m = valid⟼⋆ ss v m

valid⇝ :  ∀ {τ Δᵐ} {c₁ c₂ : CTerm τ} ->
             c₁ ⇝ c₂ -> Valid Δᵐ c₁ -> Valid Δᵐ c₂
valid⇝ (AppL s) (App v v₁) = App (valid⇝ s v) v₁
valid⇝ Beta (App (Abs v) v₁) = valid-subst v₁ v
valid⇝ (IfCond s) (If v Then v₁ Else v₂) = If (valid⇝ s v) Then v₁ Else v₂
valid⇝ IfTrue (If v Then v₁ Else v₂) = v₁
valid⇝ IfFalse (If v Then v₁ Else v₂) = v₂
valid⇝ Return (Return v) = Mac v
valid⇝ Throw (Throw v) = Macₓ v
valid⇝ Bind (Mac v >>= v₁) = App v₁ v
valid⇝ BindEx (Macₓ v >>= v₁) = Throw v
valid⇝ Catch (Catch (Mac v) v₁) = Return v
valid⇝ CatchEx (Catch (Macₓ v) v₁) = App v₁ v
valid⇝ (label p) (label .p v) = Return (Res v)
valid⇝ (unlabel p) (unlabel .p (Res v)) = Return v
valid⇝ (unlabelEx p) (unlabel .p (Resₓ v)) = Throw v
valid⇝ Hole ∙ = ∙

valid⟼ (Pure s) v m = m , (valid⇝ s v)
valid⟼ (BindCtx s) (v >>= v₁) m with valid⟼ s v m
valid⟼ (BindCtx s) (v >>= v₁) m | m₂ , v₂ = m₂ , (v₂ >>= (extendValid v₁ (context-⊆ s)))
valid⟼ (CatchCtx s) (Catch v v₁) m with valid⟼ s v m
... | m₂ , v₂ = m₂ , (Catch v₂ (extendValid v₁ (context-⊆ s)))
valid⟼ (unlabelCtx p s) (unlabel .p v) m with valid⟼ s v m
... | m₂ , v₂ = m₂ , (unlabel p v₂)
valid⟼ (join p bs) (join .p v) m with valid⇓ bs v m
valid⟼ (join p bs) (join .p v) m | m₃ , Mac v₂ = m₃ , (Return (Res v₂))
valid⟼ (joinEx p bs) (join .p v) m with valid⇓ bs v m
valid⟼ (joinEx p bs) (join .p v) m | m₃ , Macₓ v₂ = m₃ , (Return (Resₓ v₂))
valid⟼ {Δ₁ = Δ₁} (new p) (new .p v) m = extendValidMemory (validMemoryNew m v) snoc-⊆ , Return (Ref (newTypeIx Δ₁))
valid⟼ (writeCtx p s) (write .p v v') m with valid⟼ s v m
... | m₂ , v₂ = m₂ , (write p v₂ (extendValid v' (context-⊆ s)))
valid⟼ (write p i) (write .p v v₁) m = (validMemoryUpdate m (# i) v₁) , (Return （）)
valid⟼ (readCtx p s) (read .p v) m with valid⟼ s v m
... | m₂ , v₂ = m₂ , (read p v₂)
valid⟼ (read p i) v m = m , (Return (lookupValidMemory (# i) m))
valid⟼ (Hole x) ∙ ∙ = ∙ , ∙
