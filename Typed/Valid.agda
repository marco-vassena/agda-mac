module Typed.Valid where

open import Data.Product
open import Typed.Base
open import Typed.Semantics
import Data.List as L

-- Now that we have memory we have to ensure that memory references are all valid.
-- The following data type is such a proof.

data ValidT {Δ} (Δᵐ : Context) : ∀ {τ} -> Term Δ τ -> Set where
  （） : ValidT Δᵐ （）
  True : ValidT Δᵐ True
  False : ValidT Δᵐ False

  Var : ∀ {τ } -> (p : τ ∈ Δ) -> ValidT Δᵐ (Var p)
  App : ∀ {α β}{f : Term Δ (α => β)} {x : Term Δ α} ->
          ValidT Δᵐ f -> ValidT Δᵐ x -> ValidT Δᵐ (App f x)
  Abs : ∀ {α β} {t : Term (α ∷ Δ) β} -> ValidT Δᵐ t -> ValidT Δᵐ (Abs t)

  ξ : ValidT Δᵐ ξ

  Mac : ∀ {α} {l : Label} {t : Term Δ α} ->
          ValidT Δᵐ t -> ValidT Δᵐ (Mac t)
  Macₓ : ∀ {α} {l : Label} {e : Term Δ Exception} ->
           ValidT Δᵐ e -> ValidT Δᵐ (Macₓ {α = α} e)

  Res : ∀ {α}  {l : Label} {t : Term Δ α} ->
           ValidT Δᵐ t -> ValidT Δᵐ (Res t)
  Resₓ : ∀ {α} {l : Label}{e : Term Δ Exception} ->
           ValidT Δᵐ e -> ValidT Δᵐ (Resₓ {α = α} e)

  Ref : ∀ {α n} {l : Label} -> TypedIx α n Δᵐ -> ValidT Δᵐ (Ref {{α}} n)

  If_Then_Else_ : ∀ {α} {c : Term Δ Bool} {t e : Term Δ α} ->
                  ValidT Δᵐ c -> ValidT Δᵐ t -> ValidT Δᵐ e -> ValidT Δᵐ (If c Then t Else e)

  Return : ∀ {{l}} {α} {t : Term Δ α} -> ValidT Δᵐ t -> ValidT Δᵐ (Return t)
  
  _>>=_ : ∀ {{l}} {α β} {t₁ : Term Δ (Mac l α)} {t₂ : Term Δ (α => Mac l β)} ->
            ValidT Δᵐ t₁ -> ValidT Δᵐ t₂ -> ValidT Δᵐ (t₁ >>= t₂)

  Throw : ∀ {{l : Label}} {{α : Ty}} {t : Term Δ Exception} ->
            ValidT Δᵐ t -> ValidT Δᵐ (Throw {{l = l}} {{α}} t)

  Catch : ∀ {{l}} {α}  -> {t : Term Δ (Mac l α)} {h : Term Δ (Exception => Mac l α)} ->
            ValidT Δᵐ t -> ValidT Δᵐ h -> ValidT Δᵐ (Catch t h)

  label : ∀ {l h α} {t : Term Δ α} -> (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (label p t)
  unlabel : ∀ {l h α} {t : Term Δ (Labeled l α)} ->
              (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (unlabel p t)

  join : ∀ {l h α} {t : Term Δ (Mac h α)} ->
           (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (join p t)

  read : ∀ {α l h} {t : Term Δ (Ref l α)} ->
           (p : l ⊑ h) -> ValidT Δᵐ t -> ValidT Δᵐ (read p t)

  write : ∀ {α l h} {t₁ : Term Δ (Ref h α)} -> {t₂ : Term Δ α} ->
            (p : l ⊑ h) -> ValidT Δᵐ t₁ -> ValidT Δᵐ t₂ -> ValidT Δᵐ (write p t₁ t₂)
  
  new : ∀ {α l h} {t : Term Δ α} -> (p : l ⊑ h) -> ValidT Δᵐ t ->
          ValidT Δᵐ (new p t)
          
  ∙ : ∀ {τ} -> ValidT Δᵐ (∙ {{τ}})

mutual

 data ValidEnv (Δᵐ : Context) : ∀ {Δ} -> Env Δ -> Set where
   [] : ValidEnv Δᵐ []
   _∷_ : ∀ {τ Δ} {Γ : Env Δ} {c : CTerm τ} -> Valid Δᵐ c -> ValidEnv Δᵐ Γ -> ValidEnv Δᵐ (c ∷ Γ)
   
 data Valid (Δᵐ : Context) : ∀ {τ} -> CTerm τ -> Set where
   _,_ : ∀ {Δ τ} -> {Γ : Env Δ} {t : Term Δ τ} -> ValidEnv Δᵐ Γ -> ValidT Δᵐ t -> Valid Δᵐ (Γ , t)
   _$_ : ∀ {α β} {c₁ : CTerm (α => β)} {c₂ : CTerm α} -> Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (c₁ $ c₂)
   If_Then_Else_ :  ∀ {τ} {c₁ : CTerm Bool} {c₂ c₃ : CTerm τ} ->
                   Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ c₃ -> Valid Δᵐ (If c₁ Then c₂ Else c₃)
   _>>=_ : ∀ {l α β} {c₁ : CTerm (Mac l α)} {c₂ : CTerm (α => Mac l β)} ->
             Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (c₁ >>= c₂)
   Catch : ∀ {l α} -> {c₁ : CTerm (Mac l α)} {c₂ : CTerm (Exception => Mac l α)} ->
             Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (Catch c₁ c₂)
   unlabel : ∀ {l τ h} {c : CTerm (Labeled l τ)} -> (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (unlabel p c)
   join : ∀ {l h α} {c : CTerm (Mac h α)} -> (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (join p c)
   read : ∀ {α l h} {c : CTerm (Ref l α)} (p : l ⊑ h) -> Valid Δᵐ c -> Valid Δᵐ (read p c)
   write : ∀ {α l h} {c₁ : CTerm (Ref h α)} {c₂ : CTerm α} ->
             (p : l ⊑ h) -> Valid Δᵐ c₁ -> Valid Δᵐ c₂ -> Valid Δᵐ (write p c₁ c₂)
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
context⊆ : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
context⊆ {Δ₁ = Δ₁} Hole = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (Pure x) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} Return = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} Dist->>= = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (BindCtx s) = context⊆ s
context⊆ {Δ₁ = Δ₁} Bind = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} BindEx = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} Throw = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} Dist-Catch = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (CatchCtx s) = context⊆ s
context⊆ {Δ₁ = Δ₁} Catch = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} CatchEx = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (label p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (Dist-unlabel p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (unlabel p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (unlabelEx p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (unlabelCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (Dist-join p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (joinCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (join p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (joinEx p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (new p) = snoc-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (Dist-write p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (Dist-read p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (writeCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (write p r) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (readCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (read p r) = refl-⊆ Δ₁

--------------------------------------------------------------------------------


-- If a term has valid references with respect to a certain memory context Δ₁
-- then it is also valid in any memory context Δ₂ that extends it (Δ₁ ⊆ Δ₂).
extendValidT : ∀ {Δ Δ₁ Δ₂ τ} {t : Term Δ τ} ->
               ValidT Δ₁ t -> Δ₁ ⊆ Δ₂ -> ValidT Δ₂ t
extendValidT （） p = （）
extendValidT True p = True
extendValidT False p = False
extendValidT (Var p) p₁ = Var p
extendValidT (App v v₁) p = App (extendValidT v p) (extendValidT v₁ p)
extendValidT (Abs v) p = Abs (extendValidT v p)
extendValidT ξ p = ξ
extendValidT (Mac v) p = Mac (extendValidT v p)
extendValidT (Macₓ v) p = Macₓ (extendValidT v p)
extendValidT (Res v) p = Res (extendValidT v p)
extendValidT (Resₓ v) p = Resₓ (extendValidT v p)
extendValidT (Ref r) p = Ref (castIx r p)
extendValidT (If v Then v₁ Else v₂) p
  = If extendValidT v p Then extendValidT v₁ p Else extendValidT v₂ p
extendValidT (Return v) p = Return (extendValidT v p)
extendValidT (v >>= v₁) p = (extendValidT v p) >>= (extendValidT v₁ p)
extendValidT (Throw v) p = Throw (extendValidT v p)
extendValidT (Catch v v₁) p = Catch (extendValidT v p) (extendValidT v₁ p)
extendValidT (label x v) p = label x (extendValidT v p)
extendValidT (unlabel x v) p = unlabel x (extendValidT v p)
extendValidT (join x v) p = join x (extendValidT v p)
extendValidT (read x v) p = read x (extendValidT v p)
extendValidT (write x v v₁) p = write x (extendValidT v p) (extendValidT v₁ p)
extendValidT (new x v) p = new x (extendValidT v p)
extendValidT ∙ p = ∙


-- If a closed term has valid references with respect to a certain memory context Δ₁
-- then it is also valid in any memory context Δ₂ that extends it (Δ₁ ⊆ Δ₂).
extendValid : ∀ {Δ₁ Δ₂ τ} {c : CTerm τ} -> Valid Δ₁ c -> Δ₁ ⊆ Δ₂ -> Valid Δ₂ c

-- If an environment has valid references with respect to a certain memory context Δ₁
-- then it is also valid in any memory context Δ₂ that extends it (Δ₁ ⊆ Δ₂).
extendValidEnv : ∀ {Δ Δ₁ Δ₂} {Γ : Env Δ} -> ValidEnv Δ₁ Γ -> Δ₁ ⊆ Δ₂ -> ValidEnv Δ₂ Γ
extendValidEnv [] p = []
extendValidEnv (x ∷ Γ) p = (extendValid x p) ∷ (extendValidEnv Γ p)
                      
extendValid (Γ , t) p = extendValidEnv Γ p , extendValidT t p
extendValid (v $ v₁) p = (extendValid v p) $ (extendValid v₁ p)
extendValid (If v Then v₁ Else v₂) p = If (extendValid v p) Then (extendValid v₁ p) Else (extendValid v₂ p)
extendValid (v >>= v₁) p = (extendValid v p) >>= (extendValid v₁ p)
extendValid (Catch v v₁) p = Catch (extendValid v p) (extendValid v₁ p)
extendValid (unlabel x v) p = unlabel x (extendValid v p)
extendValid (join x v) p = join x (extendValid v p)
extendValid (read x v) p = read x (extendValid v p)
extendValid (write x v v₁) p = write x (extendValid v p) (extendValid v₁ p)
extendValid ∙ p = ∙

extendValidMemory : ∀ {Δ₁ Δ₂ Δᵐ} {m : Memory Δᵐ} -> ValidMemory Δ₁ m -> Δ₁ ⊆ Δ₂ -> ValidMemory Δ₂ m
extendValidMemory [] p = []
extendValidMemory (x ∷ m) p = (extendValid x p) ∷ extendValidMemory m p
extendValidMemory ∙ p = ∙

-- If we lookup in an enviroment with valid references with respect to a certain memory
-- context then the closed term retrieved is also valid. 
lookupValid : ∀ {Δᵐ Δ τ} {Γ : Env Δ} -> (p : τ ∈ Δ) -> ValidEnv Δᵐ Γ -> Valid Δᵐ (p !! Γ)
lookupValid Here (x ∷ Γ₁) = x
lookupValid (There p) (x ∷ Γ₁) = lookupValid p Γ₁

lookupValidMemory : ∀ {Δᵐ Δ τ} {m : Memory Δᵐ} -> (p : τ ∈ Δᵐ) -> ValidMemory Δ m -> Valid Δ (m [ p ])
lookupValidMemory Here (x ∷ m) = x
lookupValidMemory (There p) (x ∷ m) = lookupValidMemory p m
lookupValidMemory r ∙ = ∙

-- id is a valid function
idValid : ∀ {Δ Δᵐ τ} {Γ : Env Δ} -> {{Γᵛ : ValidEnv Δᵐ Γ}} -> Valid Δᵐ (id {τ} {{Γ}})
idValid {{Γᵛ = Γᵛ}} = Γᵛ , (Abs (Var Here))

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

stepValidCTerm : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> Valid Δ₂ c₂
stepValidCTerm (Pure (AppL x₁)) (v $ v₁) m = stepValidCTerm (Pure x₁) v m $ v₁
stepValidCTerm (Pure Beta) ((x₁ , Abs x₂) $ v₁) m = idValid $ ((v₁ ∷ x₁) , x₂)
stepValidCTerm (Pure Lookup) (x , Var p) m = idValid $ (lookupValid p x)
stepValidCTerm (Pure Dist-$) (x₁ , App x₂ x₃) m = (x₁ , x₂) $ (x₁ , x₃)
stepValidCTerm (Pure Dist-If) (x , (If x₁ Then x₂ Else x₃)) m = If (x , x₁) Then (x , x₂) Else (x , x₃)
stepValidCTerm (Pure (IfCond x)) (If v Then v₁ Else v₂) m = If stepValidCTerm (Pure x) v m Then v₁ Else v₂
stepValidCTerm (Pure IfTrue) (If x , True Then v₁ Else v₂) m = idValid $ v₁
stepValidCTerm (Pure IfFalse) (If x , False Then v₁ Else v₂) m = idValid $ v₂
stepValidCTerm (Pure Dist-∙) (x , ∙) m = ∙
stepValidCTerm (Pure Hole) ∙ m = ∙
stepValidCTerm Return (x , Return x₁) m = idValid $ (x , (Mac x₁))
stepValidCTerm Dist->>= (x , (x₁ >>= x₂)) m = (x , x₁) >>= (x , x₂)
stepValidCTerm (BindCtx s) (v >>= v₁) m = (stepValidCTerm s v m) >>= (extendValid v₁ (context⊆ s))
stepValidCTerm Bind ((x , Mac x₁) >>= v₁) m = v₁ $ (x , x₁)
stepValidCTerm BindEx ((x , Macₓ x₁) >>= v₁) m = idValid $ (x , (Throw x₁))
stepValidCTerm Throw (x , Throw x₁) m = idValid $ (x , (Macₓ x₁))
stepValidCTerm Dist-Catch (x , Catch x₁ x₂) m = Catch (x , x₁) (x , x₂)
stepValidCTerm (CatchCtx s) (Catch v v₁) m = Catch (stepValidCTerm s v m) (extendValid v₁ (context⊆ s))
stepValidCTerm Catch (Catch (x , Mac x₁) v₁) m = idValid $ (x , (Return x₁))
stepValidCTerm CatchEx (Catch (x , Macₓ x₁) v₁) m = v₁ $ (x , x₁)
stepValidCTerm (label p) (x , label .p x₁) m = idValid $ (x , (Return (Res x₁)))
stepValidCTerm (Dist-unlabel p) (x , unlabel .p x₁) m = unlabel p (x , x₁)
stepValidCTerm (unlabel p) (unlabel .p (x , Res x₁)) m = idValid $ (x , (Return x₁))
stepValidCTerm (unlabelEx p) (unlabel .p (x , Resₓ x₁)) m = idValid $ (x , (Throw x₁))
stepValidCTerm (unlabelCtx p s) (unlabel .p v) m = unlabel p (stepValidCTerm s v m)
stepValidCTerm (Dist-join p) (x , join .p x₁) m = join p (x , x₁)
stepValidCTerm (joinCtx p s) (join .p v) m = join p (stepValidCTerm s v m)
stepValidCTerm (join p) (join .p (x , Mac x₁)) m = idValid $ (x , (Return (Res x₁)))
stepValidCTerm (joinEx p) (join .p (x , Macₓ x₁)) m = idValid $ (x , (Return (Resₓ x₁)))
stepValidCTerm {Mac l (Ref h τ)} {Δ₁} (new p) (x , new .p x₁) m 
  = idValid {{x'}} $ (x' , (Return (Ref (newTypeIx Δ₁))))
  where x' = extendValidEnv x (snoc-⊆ {_} {τ} Δ₁)
stepValidCTerm (Dist-write p) (x , write .p x₁ x₂) m = write p (x , x₁) (x , x₂)
stepValidCTerm (Dist-read p) (x , read .p x₁) m = read p (x , x₁)
stepValidCTerm (writeCtx p s) (write .p v v₁) m 
  = write p (stepValidCTerm s v m) (extendValid v₁ (context⊆ s))
stepValidCTerm (write p i) (write .p (x , Ref x₁) v₁) m = idValid $ (x , (Return （）))
stepValidCTerm (readCtx p s) (read .p v) m = read p (stepValidCTerm s v m)
stepValidCTerm (read p i) (read .p (x , Ref x₁)) m 
  = (x , (Abs (Return (Var Here)))) $ (lookupValidMemory (# i) m)
stepValidCTerm Hole v m = v

stepValidMemory : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> ValidMemory Δ₂ m₂
stepValidMemory (Pure x) v m = m
stepValidMemory Return v m = m
stepValidMemory Dist->>= v m = m
stepValidMemory (BindCtx s) (v >>= v₁) m = stepValidMemory s v m
stepValidMemory Bind v m = m
stepValidMemory BindEx v m = m
stepValidMemory Throw v m = m
stepValidMemory Dist-Catch v m = m
stepValidMemory (CatchCtx s) (Catch v v₁) m = stepValidMemory s v m
stepValidMemory Catch v m = m
stepValidMemory CatchEx v m = m
stepValidMemory (label p) v m = m
stepValidMemory (Dist-unlabel p) v m = m
stepValidMemory (unlabel p) v m = m
stepValidMemory (unlabelEx p) v m = m
stepValidMemory (unlabelCtx p s) (unlabel .p v) m = stepValidMemory s v m
stepValidMemory (Dist-join p) v m = m
stepValidMemory (joinCtx p s) (join .p v) m = stepValidMemory s v m
stepValidMemory (join p) v m = m
stepValidMemory (joinEx p) v m = m
stepValidMemory (new p) (x , new .p x₁) m = extendValidMemory (validMemoryNew m (x , x₁)) (snoc-⊆ _)
stepValidMemory (Dist-write p) v m = m
stepValidMemory (Dist-read p) v m = m
stepValidMemory (writeCtx p s) (write .p v v₁) m = stepValidMemory s v m
stepValidMemory (write p i) (write .p (x , Ref x₁) v₁) m = validMemoryUpdate m (# i) v₁
stepValidMemory (readCtx p s) (read .p v) m = stepValidMemory s v m
stepValidMemory (read p i) v m = m
stepValidMemory Hole v m = m

-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
-- The final memory is also valid.
stepValid : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory Δ₁ m₁ -> 
              ValidMemory Δ₂ m₂ × Valid Δ₂ c₂
stepValid s v m = (stepValidMemory s v m) , (stepValidCTerm s v m)
