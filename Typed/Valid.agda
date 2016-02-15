module Typed.Valid where

open import Data.Product
open import Typed.Base
open import Typed.Semantics
import Data.List as L

-- Now that we have memory we have to ensure that memory references are all valid.
-- The following data type is such a proof.

data Valid {Δ} {ls : List Label} (s : Store ls) : ∀ {τ} -> Term Δ τ -> Set where
  （） : Valid s （）
  True : Valid s True
  False : Valid s False

  Var : ∀ {τ } -> (p : τ ∈ Δ) -> Valid s (Var p)
  App : ∀ {α β}{f : Term Δ (α => β)} {x : Term Δ α} ->
          Valid s f -> Valid s x -> Valid s (App f x)
  Abs : ∀ {α β} {t : Term (α ∷ Δ) β} -> Valid s t -> Valid s (Abs t)

  ξ : Valid s ξ

  Mac : ∀ {α} {l : Label} {t : Term Δ α} ->
          Valid s t -> Valid s (Mac t)
  Macₓ : ∀ {α} {l : Label} {e : Term Δ Exception} ->
           Valid s e -> Valid s (Macₓ {α = α} e)

  Res : ∀ {α}  {l : Label} {t : Term Δ α} ->
           Valid s t -> Valid s (Res t)
  Resₓ : ∀ {α} {l : Label}{e : Term Δ Exception} ->
           Valid s e -> Valid s (Resₓ {α = α} e)

  Ref : ∀ {α} {l : Label} -> (r : ⟨ α , l ⟩∈ˢ s) -> Valid s (Ref r)

  If_Then_Else_ : ∀ {α} {c : Term Δ Bool} {t e : Term Δ α} ->
                  Valid s c -> Valid s t -> Valid s e -> Valid s (If c Then t Else e)

  Return : ∀ {{l}} {α} {t : Term Δ α} -> Valid s t -> Valid s (Return t)
  
  _>>=_ : ∀ {{l}} {α β} {t₁ : Term Δ (Mac l α)} {t₂ : Term Δ (α => Mac l β)} ->
            Valid s t₁ -> Valid s t₂ -> Valid s (t₁ >>= t₂)

  Throw : ∀ {{l : Label}} {{α : Ty}} {t : Term Δ Exception} ->
            Valid s t -> Valid s (Throw {{l = l}} {{α}} t)

  Catch : ∀ {{l}} {α}  -> {t : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
            Valid s t -> Valid s h -> Valid s (Catch t h)

  label : ∀ {l h α} {t : Term Δ α} -> (p : l ⊑ h) -> Valid s t -> Valid s (label p t)
  unlabel : ∀ {l h α} {t : Term Δ (Labeled l α)} ->
              (p : l ⊑ h) -> Valid s t -> Valid s (unlabel p t)

  join : ∀ {l h α} {t : Term Δ (Mac h α)} ->
           (p : l ⊑ h) -> Valid s t -> Valid s (join p t)

  read : ∀ {α l h} {t : Term Δ (Ref l α)} ->
           (p : l ⊑ h) -> Valid s t -> Valid s (read p t)

  write : ∀ {α l h} {t₁ : Term Δ (Ref h α)} -> {t₂ : Term Δ α} ->
            (p : l ⊑ h) -> Valid s t₁ -> Valid s t₂ -> Valid s (write p t₁ t₂)
  
  new : ∀ {α l h} {t : Term Δ α} -> (p : l ⊑ h) -> Valid s t -> (q : ⟨ α , h ⟩∈ˢ s) -> Valid s (new p t q)
          
  ∙ : ∀ {τ} -> Valid s (∙ {{τ}})

data ValidMemory {l : Label} {ls : List Label} (s : Store ls) : Memory l -> Set where
  [] : ValidMemory s []
  _∷_ : ∀ {τ} {c : CTerm τ} {m : Memory l} -> Valid s c -> ValidMemory s m -> ValidMemory s (c ∷ m)
  ∙ : ValidMemory s ∙

data ValidStore : ∀ {ls} -> (s : Store ls) -> Set where
  [] : ValidStore []
  _∷_ : ∀ {l ls} {s : Store ls} {m : Memory l} {{p : Unique l ls}} -> ValidMemory (m ∷ s) m -> ValidStore s -> ValidStore (m ∷ s)
 
--------------------------------------------------------------------------------

valid-wken :  ∀ {τ Δ₁ Δ₂ ls} {s : Store ls} {t : Term Δ₁ τ} -> Valid s t -> (p : Δ₁ ⊆ˡ Δ₂) -> Valid s (wken t p)
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
valid-wken (new p v r) p₁ = new p (valid-wken v p₁) r
valid-wken ∙ p = ∙

valid-var-subst : ∀ {α β ls} {s : Store ls} (Δ₁ Δ₂ : Context) {x : Term Δ₂ α} -> (p : β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) -> Valid s x -> Valid s (var-subst Δ₁ Δ₂ x p)
valid-var-subst [] Δ₂ Here x₁ = x₁
valid-var-subst [] Δ₂ (There p) x₁ = Var p
valid-var-subst (β ∷ Δ₁) Δ₂ Here x₂ = Var Here
valid-var-subst (_ ∷ Δ₁) Δ₂ (There p) x = valid-wken (valid-var-subst Δ₁ Δ₂ p x) (drop refl-⊆ˡ)

valid-tm-subst : ∀ {α τ ls} {s : Store ls} (Δ₁ Δ₂ : Context) {x : Term Δ₂ α} {t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ} ->
                 Valid s x -> Valid s t -> Valid s (tm-subst Δ₁ Δ₂ x t)
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
valid-tm-subst Δ₁ Δ₂ xᵛ (new p tᵛ r) = new p (valid-tm-subst Δ₁ Δ₂ xᵛ tᵛ) r
valid-tm-subst Δ₁ Δ₂ xᵛ ∙ = ∙

valid-subst : ∀ {Δ ls α β} {s : Store ls} {x : Term Δ α} {t : Term (α ∷ Δ) β} -> Valid s x -> Valid s t -> Valid s (subst x t)
valid-subst x t = valid-tm-subst [] _ x t

-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
-- The final memory is also valid.
-- valid⟼ :  ∀ {τ ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm τ} ->
--               ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> Valid s₁ c₁ -> ValidStore s₁ -> 
--               ValidStore s₂ × Valid s₂ c₂

-- valid⟼⋆ :  ∀ {τ ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm τ} ->
--               ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₂ ∥ c₂ ⟩ -> Valid s₁ c₁ -> ValidStore s₁ -> 
--               ValidStore s₂ × Valid s₂ c₂
-- valid⟼⋆ [] v m = m , v
-- valid⟼⋆ (s ∷ ss) v m with valid⟼ s v m
-- ... | m₂ , c₂ = valid⟼⋆ ss c₂ m₂

-- valid⇓ :  ∀ {τ ls} {s₁ s₂ : Store ls} {c₁ c₂ : CTerm τ} ->
--               ⟨ s₁ ∥ c₁ ⟩ ⇓ ⟨ s₂ ∥ c₂ ⟩ -> Valid s₁ c₁ -> ValidStore s₁ -> 
--               ValidStore s₂ × Valid s₂ c₂
-- valid⇓ (BigStep isV ss) v m = valid⟼⋆ ss v m

valid⇝ :  ∀ {τ ls} {s : Store ls} {c₁ c₂ : CTerm τ} ->
             c₁ ⇝ c₂ -> Valid s c₁ -> Valid s c₂
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

valid-readᵐ : ∀ {l ls τ} {m : Memory l} {s : Store ls} -> ValidMemory s m -> (x : τ ∈ᵐ m) -> Valid s (m [ x ])
valid-readᵐ (x ∷ m₁) Here = Res x
valid-readᵐ (x ∷ m₁) (There x₁) = valid-readᵐ m₁ x₁
valid-readᵐ m ∙ = Res ∙

valid-writeᵐ : ∀ {l ls τ} {m : Memory l} {c : CTerm τ} {s : Store ls} -> ValidMemory s m -> Valid s c -> (x : τ ∈ᵐ m) -> ValidMemory s (m [ x ]≔ c)
valid-writeᵐ (x ∷ m₁) v Here = v ∷ m₁
valid-writeᵐ (x ∷ m₁) v (There x₁) = x ∷ (valid-writeᵐ m₁ v x₁)
valid-writeᵐ m v ∙ = m

valid-newᵐ : ∀ {l ls τ}  {m : Memory l} {c : CTerm τ} {s : Store ls} -> ValidMemory s m -> Valid s c -> ValidMemory s (m ∷ʳ c)
valid-newᵐ [] v = v ∷ []
valid-newᵐ (x ∷ m₁) v = x ∷ valid-newᵐ m₁ v
valid-newᵐ ∙ v = ∙

data _⊴ᵐ_ {l : Label} :  Memory l -> Memory l ->  Set where
  base : ∀ {m : Memory l} -> [] ⊴ᵐ m
  cons : ∀ {τ} {m₁ m₂ : Memory l} {c₁ c₂ : CTerm τ} -> m₁ ⊴ᵐ m₂ -> (c₁ ∷ m₁) ⊴ᵐ (c₂ ∷ m₂)

data _⊴_ : ∀ {ls} -> Store ls -> Store ls -> Set where
  base : [] ⊴ []
  cons : ∀ {l ls} {s₁ s₂ : Store ls} {p : Unique l ls} {m₁ : Memory l} {m₂ : Memory l} -> m₁ ⊴ᵐ m₂ -> s₁ ⊴ s₂ -> (m₁ ∷ s₁) ⊴ (m₂ ∷ s₂)

-- This does not work!
-- extendValid : ∀ {Δ τ ls} {s₁ s₂ : Store ls} {t : Term Δ τ} -> Valid s₁ t -> s₁ ⊴ s₂ -> Valid s₂ t
-- extendValid （） p = （）
-- extendValid True p = True
-- extendValid False p = False
-- extendValid (Var p) p₁ = Var p
-- extendValid (App v v₁) p = App (extendValid v p) (extendValid v₁ p)
-- extendValid (Abs v) p = Abs (extendValid v p)
-- extendValid ξ p = ξ
-- extendValid (Mac v) p = Mac (extendValid v p)
-- extendValid (Macₓ v) p = Macₓ (extendValid v p)
-- extendValid (Res v) p = Res (extendValid v p)
-- extendValid (Resₓ v) p = Resₓ (extendValid v p)
-- extendValid (Ref r) p = {!!} -- This does not work because r is fixed and parametrixed over s₁ (instead of s₂)
-- extendValid (If v Then v₁ Else v₂) p = If extendValid v p Then extendValid v₁ p Else extendValid v₂ p
-- extendValid (Return v) p = Return (extendValid v p)
-- extendValid (v >>= v₁) p = (extendValid v p) >>= (extendValid v₁ p)
-- extendValid (Throw v) p = Throw (extendValid v p)
-- extendValid (Catch v v₁) p = Catch (extendValid v p) (extendValid v₁ p)
-- extendValid (label p v) p₁ = label p (extendValid v p₁)
-- extendValid (unlabel p v) p₁ = unlabel p (extendValid v p₁)
-- extendValid (join p v) p₁ = join p (extendValid v p₁)
-- extendValid (read p v) p₁ = read p (extendValid v p₁)
-- extendValid (write p v v₁) p₁ = write p (extendValid v p₁) (extendValid v₁ p₁)
-- extendValid (new p v q) p₁ = {!new  !} -- This does not work because q is fixed and parametrixed over s₁ (instead of s₂)
-- extendValid ∙ p = ∙

-- extendValid-writeˢ : ∀ {ls l τ₁ τ₂} -> {s₁ : Store ls} {c₁ : CTerm τ₁} {c₂ : CTerm τ₂} -> (q : ⟨ τ₂ , l ⟩∈ˢ s₁) ->
--                        let s₂ = writeˢ c₂ s₁ q in
--                        Valid s₁ c₁ -> Valid s₂ c₁
-- extendValid-writeˢ (Here x) v = {!!}
-- extendValid-writeˢ {s₁ = m ∷ s} (There q) v = {!extendValid-writeˢ q ?!}

-- valid⟼ (Pure x) v m = m , (valid⇝ x v)
-- valid⟼ (BindCtx s) (v >>= v₁) m with valid⟼ s v m
-- ... | a , b = a , (b >>= {!!})
-- valid⟼ (CatchCtx s) v m = {!!} 
-- valid⟼ (unlabelCtx p s) v m = {!!}
-- valid⟼ (join p x) v m = {!!}
-- valid⟼ (joinEx p x) v m = {!!}
-- valid⟼ (new p r) v m = {!!}
-- valid⟼ (writeCtx p s) v m = {!!}
-- valid⟼ (write p q) v m = {!!}
-- valid⟼ (readCtx p s) v m = {!!}
-- valid⟼ (read p q) v m = m , (unlabel p {!!})
