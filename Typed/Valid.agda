module Typed.Valid where

open import Data.Product
open import Typed.Base
open import Typed.Semantics

-- Now that we have memory we have to ensure that memory references are all valid.
-- The following data type is such a proof.

data ValidT {Δ} (Δᵐ : Context) : ∀ {τ} -> Term Δ τ -> Set where
  （） : ValidT Δᵐ （）
  True : ValidT Δᵐ True
  False : ValidT Δᵐ False

  Var : ∀ {τ} -> (p : τ ∈ Δ) -> ValidT Δᵐ (Var p)
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

  Ref : ∀ {α} {l : Label} -> (r : α ∈ Δᵐ) -> ValidT Δᵐ (Ref α)

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
          
  ∙ : ∀ {τ} -> ValidT Δᵐ (∙ {Δ} {τ})

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
   ∙ : ∀ {τ} -> Valid Δᵐ (∙ {τ})

ValidMemory : ∀ {Δᵐ} -> (m : Memory Δᵐ) -> Set
ValidMemory {Δᵐ} m = ValidEnv Δᵐ m

--------------------------------------------------------------------------------
-- Lemmas and proofs
--------------------------------------------------------------------------------

-- This lemma shows that the context of the memory in a step always
-- grows, but never shrinks, i.e. the initial memory context is a subset
-- of the final memory context.
context⊆ : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
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
context⊆ {Δ₁ = Δ₁} (new p) = drop (refl-⊆ Δ₁)
context⊆ {Δ₁ = Δ₁} (Dist-write p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (Dist-read p) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (writeCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (write p r) = refl-⊆ Δ₁
context⊆ {Δ₁ = Δ₁} (readCtx p s) = context⊆ s
context⊆ {Δ₁ = Δ₁} (read p r) = refl-⊆ Δ₁


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
extendValidT (Ref τ) p = Ref (extend-∈ τ p)
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

-- If we lookup in an enviroment with valid references with respect to a certain memory
-- context then the closed term retrieved is also valid. 
lookupValid : ∀ {Δᵐ Δ τ} {Γ : Env Δ} -> (p : τ ∈ Δ) -> ValidEnv Δᵐ Γ -> Valid Δᵐ (p !! Γ)
lookupValid Here (x ∷ Γ₁) = x
lookupValid (There p) (x ∷ Γ₁) = lookupValid p Γ₁

-- id is a valid function
idValid : ∀ {Δ Δᵐ τ} {Γ : Env Δ} -> {{Γᵛ : ValidEnv Δᵐ Γ}} -> Valid Δᵐ (id {τ} {{Γ}})
idValid {{Γᵛ = Γᵛ}} = Γᵛ , (Abs (Var Here))

validMemoryUpdate : ∀ {Δ Δᵐ τ} {m : Memory Δᵐ} {c : CTerm τ} ->
                    ValidEnv Δ m -> (p : τ ∈ Δᵐ) -> Valid Δ c  -> ValidEnv Δ (m [ p ]≔ c)
validMemoryUpdate [] () v
validMemoryUpdate (x ∷ vᵐ) Here v = v ∷ vᵐ
validMemoryUpdate (x ∷ vᵐ) (There p) v = x ∷ validMemoryUpdate vᵐ p v

-- TODO separate the proof in two stepValidCTerm from stepValidMemory
-- TODO adapt proof for new semantics

-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
-- stepValid : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
--               ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidMemory m₁ -> ValidMemory m₂ × Valid Δ₂ c₂
-- stepValid (Pure (AppL s)) (v₁ $ v₂) vᵐ with stepValid (Pure s) v₁ vᵐ
-- stepValid (Pure (AppL s)) (v₁ $ v₂) vᵐ | _ , v₁' = vᵐ , (v₁' $ v₂)
-- stepValid (Pure Beta) (Γ , Abs x $ v) vᵐ = vᵐ , (idValid $ ((v ∷ Γ) , x))
-- stepValid (Pure Lookup) (Γ , (Var p)) vᵐ = vᵐ , (idValid $ lookupValid p Γ)
-- stepValid (Pure Dist-$) (Γ , App f x) vᵐ = vᵐ , (Γ , f $ Γ , x)
-- stepValid (Pure Dist-If) (Γ , If c Then t Else e) vᵐ = vᵐ , If (Γ , c) Then (Γ , t) Else (Γ , e)
-- stepValid (Pure (IfCond x)) (If v Then v₁ Else v₂) vᵐ with stepValid (Pure x) v vᵐ
-- stepValid (Pure (IfCond x)) (If v Then v₁ Else v₂) vᵐ | _ , v' = vᵐ , (If v' Then v₁ Else v₂) 
-- stepValid (Pure IfTrue) (If Γ , True Then v₁ Else v₂) vᵐ = vᵐ , (Γ , Abs (Var Here) $ v₁)
-- stepValid (Pure IfFalse) (If Γ , False Then v₁ Else v₂) vᵐ = vᵐ , (Γ , Abs (Var Here) $ v₂)
-- stepValid (Pure Dist-∙) (Γ , ∙) vᵐ = vᵐ , ∙
-- stepValid (Pure Hole) ∙ vᵐ = vᵐ , ∙
-- stepValid Return (Γ , Return v) vᵐ = vᵐ , ((Γ , Abs (Var Here)) $ (Γ , (Mac v)))
-- stepValid Dist->>= (Γ , (v₁ >>= v₂)) vᵐ = vᵐ , ((Γ , v₁) >>= (Γ , v₂))
-- stepValid (BindCtx s) (v >>= v₁) vᵐ with stepValid s v vᵐ
-- stepValid (BindCtx s) (v >>= v₁) vᵐ | vᵐ' , v' = vᵐ' , (v' >>= (extendValid v₁ (context⊆ s)))  
-- stepValid Bind ((Γ , Mac v) >>= v₁) vᵐ = vᵐ , (v₁ $ Γ , v)
-- stepValid BindEx ((Γ , Macₓ v) >>= v₁) vᵐ = vᵐ , (idValid $ (Γ , (Throw v)))
-- stepValid Throw (Γ , Throw v) vᵐ = vᵐ , (idValid $ (Γ , (Macₓ v)))
-- stepValid Dist-Catch (Γ , Catch v₁ v₂) vᵐ = vᵐ , Catch (Γ , v₁) (Γ , v₂)
-- stepValid (CatchCtx s) (Catch v v₁) vᵐ with stepValid s v vᵐ
-- stepValid (CatchCtx s) (Catch v v₁) vᵐ | vᵐ' , v' = vᵐ' , (Catch v' (extendValid v₁ (context⊆ s))) 
-- stepValid Catch (Catch (Γ , Mac v₁) v₂) vᵐ = vᵐ , (idValid $ (Γ , (Return v₁)))
-- stepValid CatchEx (Catch (Γ , Macₓ v₁) v₂) vᵐ = vᵐ , (v₂ $ Γ , v₁)
-- stepValid (label p) (Γ , label .p v) vᵐ = vᵐ , (idValid $ (Γ , (Return (Res v)))) 
-- stepValid (Dist-unlabel p) (Γ , unlabel .p v) vᵐ = vᵐ , unlabel p (Γ , v)
-- stepValid (unlabel p) (unlabel .p (Γ , Res v)) vᵐ = vᵐ , (idValid $ (Γ , (Return v)))
-- stepValid (unlabelEx p) (unlabel .p (Γ , Resₓ v)) vᵐ = vᵐ , (idValid $ (Γ , (Throw v))) 
-- stepValid (unlabelCtx p s) (unlabel .p v) vᵐ with stepValid s v vᵐ
-- ... | vᵐ' , v'  = vᵐ' , unlabel p v'
-- stepValid (Dist-join p) (Γ , join .p v) vᵐ = vᵐ , join p (Γ , v)
-- stepValid (joinCtx p s) (join .p v) vᵐ with stepValid s v vᵐ
-- ... | vᵐ' , v' = vᵐ' , (join p v')
-- stepValid (join p) (join .p (Γ , Mac v)) vᵐ = vᵐ , (idValid $ (Γ , (Return (Res v)))) 
-- stepValid (joinEx p) (join .p (Γ , Macₓ v)) vᵐ = vᵐ , (idValid $ Γ , (Return (Resₓ v))) 
-- stepValid {Δ₁ = Δ₁} (new p) (Γ , new .p v) vᵐ = (vᵐ' , (idValid' $ Γ' , ( Return (Ref Here))))
--   where q = drop (refl-⊆ Δ₁)
--         Γ' = extendValidEnv Γ q
--         idValid' = Γ' , Abs (Var Here)
--         vᵐ' = extendValidEnv ((Γ , v) ∷ vᵐ) q
-- stepValid (Dist-write p) (Γ , write .p v₁ v₂) vᵐ = vᵐ , write p (Γ , v₁) (Γ , v₂)
-- stepValid (Dist-read p) (Γ , read .p v₁) vᵐ = vᵐ , read p (Γ , v₁)
-- stepValid (writeCtx p s) (write .p v v₁) vᵐ with stepValid s v vᵐ
-- ... | vᵐ' , v' = vᵐ' , (write p v' (extendValid v₁ (context⊆ s))) 
-- stepValid (write p r) (write .p (Γ , Ref r') v₁) vᵐ = validMemoryUpdate vᵐ r v₁ , (idValid $ (Γ , (Return （）))) 
-- stepValid (readCtx p s) (read .p v) vᵐ with stepValid s v vᵐ
-- stepValid (readCtx p s) (read .p v) vᵐ | vᵐ' , v' = vᵐ' , (read p v')
-- stepValid (read p r) (read .p (Γ , Ref r')) vᵐ = vᵐ , (Γ , (Abs (Return (Var Here))) $ lookupValid r vᵐ)
