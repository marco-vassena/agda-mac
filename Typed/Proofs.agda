module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality
open import Data.Sum

-- TODO Show that also the resulting memory preserves valid references

-- This lemma shows that the context of the memory in a step always
-- grows, but never shrinks, i.e. the initial memory context is a subset
-- of the final memory context.
context⊆ : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
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

-- Our small step semantics preserves validity of terms and closed terms.
-- If a closed term has valid references in the initial memory context and
-- can be reduced further then the reduced term is also valid in the final memory context.
stepValid : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                     ⟨ m₁ ∥ c₁ ⟩⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid Δ₁ c₁ -> ValidEnv Δ₁ m₁ -> Valid Δ₂ c₂
stepValid (Pure (AppL s)) (v $ v₁) vᵐ = (stepValid (Pure s) v vᵐ) $ v₁
stepValid (Pure Beta) (Γ , Abs x $ v) vᵐ = (Γ , (Abs (Var Here))) $ (v ∷ Γ , x)
stepValid (Pure Lookup) (Γ , (Var p)) vᵐ = (Γ , Abs (Var Here)) $ lookupValid p Γ
stepValid (Pure Dist-$) (Γ , App f x) vᵐ = Γ , f $ Γ , x
stepValid (Pure Dist-If) (Γ , If c Then t Else e) vᵐ = If (Γ , c) Then (Γ , t) Else (Γ , e)
stepValid (Pure (IfCond x)) (If v Then v₁ Else v₂) vᵐ = If (stepValid (Pure x) v vᵐ) Then v₁ Else v₂
stepValid (Pure IfTrue) (If Γ , True Then v₁ Else v₂) vᵐ = Γ , Abs (Var Here) $ v₁
stepValid (Pure IfFalse) (If Γ , False Then v₁ Else v₂) vᵐ = Γ , Abs (Var Here) $ v₂
stepValid (Pure Dist-∙) (Γ , ∙) vᵐ = ∙
stepValid (Pure Hole) ∙ vᵐ = ∙
stepValid Return (Γ , Return v) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Mac v))
stepValid Dist->>= (Γ , v₁ >>= v₂) vᵐ = (Γ , v₁) >>= (Γ , v₂)
stepValid (BindCtx s) (v >>= v₁) vᵐ = (stepValid s v vᵐ) >>= (extendValid v₁ (context⊆ s))
stepValid Bind ((Γ , Mac v) >>= v₁) vᵐ = v₁ $ Γ , v
stepValid BindEx ((Γ , Macₓ v) >>= v₁) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Throw v))
stepValid Throw (Γ , Throw v) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Macₓ v))
stepValid Dist-Catch (Γ , Catch v₁ v₂) vᵐ = Catch (Γ , v₁) (Γ , v₂)
stepValid (CatchCtx s) (Catch v v₁) vᵐ = Catch (stepValid s v vᵐ) (extendValid v₁ (context⊆ s))
stepValid Catch (Catch (Γ , Mac v₁) v₂) vᵐ = (Γ , (Abs (Var Here))) $ (Γ , (Return v₁))
stepValid CatchEx (Catch (Γ , Macₓ v₁) v₂) vᵐ = v₂ $ Γ , v₁
stepValid (label p) (Γ , label .p v) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Return (Res v)))
stepValid (Dist-unlabel p) (Γ , unlabel .p v) vᵐ = unlabel p (Γ , v)
stepValid (unlabel p) (unlabel .p (Γ , Res v)) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Return v))
stepValid (unlabelEx p) (unlabel .p (Γ , Resₓ v)) vᵐ = (Γ , (Abs (Var Here))) $ (Γ , (Throw v))
stepValid (unlabelCtx p s) (unlabel .p v) vᵐ = unlabel p (stepValid s v vᵐ)
stepValid (Dist-join p) (Γ , join .p v) vᵐ = join p (Γ , v)
stepValid (joinCtx p s) (join .p v) vᵐ = join p (stepValid s v vᵐ)
stepValid (join p) (join .p (Γ , Mac v)) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Return (Res v)))
stepValid (joinEx p) (join .p (Γ , Macₓ v)) vᵐ = (Γ , Abs (Var Here)) $ (Γ , (Return (Resₓ v)))
stepValid {Δ₁ = Δ₁} (new p) (Γᵛ , new .p v) vᵐ
  = (extendValidEnv Γᵛ (drop (refl-⊆ Δ₁)) , (Abs (Var Here))) $ (extendValidEnv Γᵛ (drop (refl-⊆ Δ₁)) , (Return (Ref Here)))
stepValid (Dist-write p) (Γ , write .p v₁ v₂) vᵐ = write p (Γ , v₁) (Γ , v₂)
stepValid (Dist-read p) (Γ , read .p v₁) vᵐ = read p (Γ , v₁)
stepValid (writeCtx p s) (write .p v v₁) vᵐ = write p (stepValid s v vᵐ) (extendValid v₁ (context⊆ s))
stepValid (write p r) (write .p (Γ , Ref r') v₁) vᵐ = (Γ , (Abs (Var Here))) $ (Γ , (Return （）))
stepValid (readCtx p s) (read .p v) vᵐ = read p (stepValid s v vᵐ)
stepValid (read p r) (read .p (Γ , Ref r')) vᵐ = (Γ , (Abs (Return (Var Here)))) $ (lookupValid r vᵐ)

-- A closed term with valid references with respect to the given memory context
-- either can be reduced further or it is a value.
progress : ∀ {τ Δᵐ} {{m : Memory Δᵐ}} (c : CTerm τ) -> Valid Δᵐ c -> (Redex m c) ⊎ (IsValue c)
progress (Γ , （）) v = inj₂ (Γ , （）)
progress (Γ , True) v = inj₂ (Γ , True)
progress (Γ , False) v = inj₂ (Γ , False)
progress (Γ , Var x) v = inj₁ (Step (Pure Lookup))
progress (Γ , Abs t) v = inj₂ (Γ , Abs t)
progress (Γ , App t t₁) v = inj₁ (Step (Pure Dist-$))
progress (Γ , If t Then t₁ Else t₂) v = inj₁ (Step (Pure Dist-If))
progress (Γ , Return t) v = inj₁ (Step Return)
progress (Γ , t >>= t₁) v = inj₁ (Step Dist->>=)
progress (Γ , ξ) v = inj₂ (Γ , ξ)
progress (Γ , Throw t) v = inj₁ (Step Throw)
progress (Γ , Catch m h) v = inj₁ (Step Dist-Catch)
progress (Γ , Mac t) v = inj₂ (Γ , (Mac t))
progress (Γ , Macₓ t) v = inj₂ (Γ , (Macₓ t))
progress (Γ , Res t) v = inj₂ (Γ , (Res t))
progress (Γ , Resₓ t) v = inj₂ (Γ , (Resₓ t))
progress (Γ , label x t) v = inj₁ (Step (label x))
progress (Γ , unlabel x t) v = inj₁ (Step (Dist-unlabel x))
progress (Γ , join x t) v = inj₁ (Step (Dist-join x))
progress (Γ , Ref r) v = inj₂ (Γ , (Ref r))
progress (Γ , read p r) v = inj₁ (Step (Dist-read p))
progress (Γ , write p r t) v = inj₁ (Step (Dist-write p))
progress (Γ , new p r) v = inj₁ (Step (new p))
progress (Γ , ∙) v = inj₁ (Step (Pure Dist-∙))
progress (f $ x) (v₁ $ v₂) with progress f v₁
progress (f $ x₁) (v₁ $ v₂) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (AppL x)))
progress (.(Γ , Abs t) $ x₁) (v₁ $ v₂) | inj₂ (Γ , Abs t) = inj₁ (Step (Pure Beta))
progress (If c₁ Then c₂ Else e) (If v₁ Then v₂ Else v₃) with progress c₁ v₁
progress (If c₁ Then c₃ Else e) (If v₁ Then v₂ Else v₃) | inj₁ (Step (Pure x)) = inj₁ (Step (Pure (IfCond x)))
progress (If .(Γ , True) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , True) = inj₁ (Step (Pure IfTrue))
progress (If .(Γ , False) Then c₂ Else e) (If v₁ Then v₂ Else v₃) | inj₂ (Γ , False) = inj₁ (Step (Pure IfFalse))
progress (m >>= k) (v >>= v₁) with progress m v
progress (m₁ >>= k) (v >>= v₁) | inj₁ (Step x) = inj₁ (Step (BindCtx x))
progress (.(Γ , Mac t) >>= k) (v >>= v₁) | inj₂ (Γ , Mac t) = inj₁ (Step Bind)
progress (.(Γ , Macₓ e) >>= k) (v >>= v₁) | inj₂ (Γ , Macₓ e) = inj₁ (Step BindEx)
progress (Catch m h) (Catch v v₁) with progress m v
progress (Catch m₁ h) (Catch v v₁) | inj₁ (Step x) = inj₁ (Step (CatchCtx x))
progress (Catch .(Γ , Mac t) h) (Catch v v₁) | inj₂ (Γ , Mac t) = inj₁ (Step Catch)
progress (Catch .(Γ , Macₓ e) h) (Catch v v₁) | inj₂ (Γ , Macₓ e) = inj₁ (Step CatchEx)
progress (unlabel x c) (unlabel .x v) with progress c v
progress (unlabel x₁ c) (unlabel .x₁ v) | inj₁ (Step x) = inj₁ (Step (unlabelCtx x₁ x))
progress (unlabel x₁ .(Γ , Res t)) (unlabel .x₁ v) | inj₂ (Γ , Res t) = inj₁ (Step (unlabel x₁))
progress (unlabel x₁ .(Γ , Resₓ e)) (unlabel .x₁ v) | inj₂ (Γ , Resₓ e) = inj₁ (Step (unlabelEx x₁))
progress (join x c) (join .x v) with progress c v
progress (join x₁ c) (join .x₁ v) | inj₁ (Step x) = inj₁ (Step (joinCtx x₁ x))
progress (join x₁ .(Γ , Mac t)) (join .x₁ v) | inj₂ (Γ , Mac t) = inj₁ (Step (join x₁))
progress (join x₁ .(Γ , Macₓ e)) (join .x₁ v) | inj₂ (Γ , Macₓ e) = inj₁ (Step (joinEx x₁))
progress (write p r c) (write .p v v₁) with progress r v
progress (write p r c) (write .p v v₁) | inj₁ (Step x) = inj₁ (Step (writeCtx p x))
progress (write p (Γ , Ref α) c) (write .p (Γ' , Ref r) v₁) | inj₂ (.Γ , Ref .α) = inj₁ (Step (write p r))
progress (read p r) (read .p v) with progress r v
progress (read p r) (read .p v) | inj₁ (Step x) = inj₁ (Step (readCtx p x))
progress (read p (Γ , Ref α)) (read .p (Γ' , Ref r)) | inj₂ (.Γ , Ref .α) = inj₁ (Step (read p r))
progress ∙ v = inj₁ (Step (Pure Hole))

-- valueNotRedex : ∀ {τ Δ} {m : Memory Δ} -> (c : CTerm τ) -> IsValue c -> NormalForm m c
-- valueNotRedex .(Γ , （）) (Γ , （）) (Step (Pure ()))
-- valueNotRedex .(Γ , True) (Γ , True) (Step (Pure ()))
-- valueNotRedex .(Γ , False) (Γ , False) (Step (Pure ()))
-- valueNotRedex .(Γ , Abs t) (Γ , Abs t) (Step (Pure ()))
-- valueNotRedex .(Γ , ξ) (Γ , ξ) (Step (Pure ()))
-- valueNotRedex .(Γ , Mac t) (Γ , Mac t) (Step (Pure ()))
-- valueNotRedex .(Γ , Macₓ e) (Γ , Macₓ e) (Step (Pure ()))
-- valueNotRedex .(Γ , Res t) (Γ , Res t) (Step (Pure ()))
-- valueNotRedex .(Γ , Resₓ e) (Γ , Resₓ e) (Step (Pure ()))

-- determinism⇝ : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃
-- determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
-- determinism⇝ (AppL ()) Beta
-- determinism⇝ Beta (AppL ())
-- determinism⇝ Beta Beta = refl
-- determinism⇝ Lookup Lookup = refl
-- determinism⇝ Dist-$ Dist-$ = refl
-- determinism⇝ Dist-If Dist-If = refl
-- determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
-- determinism⇝ (IfCond ()) IfTrue
-- determinism⇝ (IfCond ()) IfFalse
-- determinism⇝ IfTrue (IfCond ())
-- determinism⇝ IfTrue IfTrue = refl
-- determinism⇝ IfFalse (IfCond ())
-- determinism⇝ IfFalse IfFalse = refl
-- determinism⇝ Dist-∙ Dist-∙ = refl 
-- determinism⇝ Hole Hole = refl

-- determinismMixed : ∀ {Δ τ} {m : Memory Δ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> ⟨ m ∥ c₁ ⟩ ⟼ ⟨ m ∥ c₃ ⟩ -> c₂ ≡ c₃
-- determinismMixed s₁ (Pure s₂) = determinism⇝ s₁ s₂
-- determinismMixed () Return
-- determinismMixed () Dist->>=
-- determinismMixed () (BindCtx s₂)
-- determinismMixed () Bind
-- determinismMixed () BindEx
-- determinismMixed () Throw
-- determinismMixed () Dist-Catch
-- determinismMixed () (CatchCtx s₂)
-- determinismMixed () Catch
-- determinismMixed () CatchEx
-- determinismMixed () (label p)
-- determinismMixed () (Dist-unlabel p)
-- determinismMixed () (unlabel p)
-- determinismMixed () (unlabelEx p)
-- determinismMixed () (unlabelCtx p s₂)
-- determinismMixed () (Dist-join p)
-- determinismMixed () (joinCtx p s₂)
-- determinismMixed () (join p)
-- determinismMixed () (joinEx p)

-- -- TODO
-- -- @Ale I think I should prove this for some m₃ and show also that m₂ ≡ m₃
-- determinism : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ c₃ : CTerm τ} ->
--                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₃ ⟩ -> c₂ ≡ c₃
-- determinism (Pure s₁) s₂ = determinismMixed s₁ s₂
-- determinism s₁ (Pure s₂) = sym (determinismMixed s₂ s₁)
-- determinism Return Return = refl
-- determinism Dist->>= Dist->>= = refl
-- determinism (BindCtx s₁) (BindCtx s₂) rewrite determinism s₁ s₂ = refl
-- determinism (BindCtx (Pure ())) Bind
-- determinism (BindCtx (Pure ())) BindEx
-- determinism Bind (BindCtx (Pure ()))
-- determinism Bind Bind = refl
-- determinism BindEx (BindCtx (Pure ()))
-- determinism BindEx BindEx = refl
-- determinism Throw Throw = refl
-- determinism Dist-Catch Dist-Catch = refl
-- determinism (CatchCtx s₁) (CatchCtx s₂) rewrite determinism s₁ s₂ = refl
-- determinism (CatchCtx (Pure ())) Catch
-- determinism (CatchCtx (Pure ())) CatchEx
-- determinism Catch (CatchCtx (Pure ()))
-- determinism Catch Catch = refl
-- determinism CatchEx (CatchCtx (Pure ()))
-- determinism CatchEx CatchEx = refl
-- determinism (label p) (label .p) = refl
-- determinism (Dist-unlabel p) (Dist-unlabel .p) = refl
-- determinism (unlabel p) (unlabel .p) = refl
-- determinism (unlabel p) (unlabelCtx .p (Pure ()))
-- determinism (unlabelCtx p (Pure ())) (unlabel .p)
-- determinism (unlabelCtx p (Pure ())) (unlabelEx .p)
-- determinism (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinism s₁ s₂ = refl
-- determinism (unlabelEx p) (unlabelEx .p) = refl
-- determinism (unlabelEx p) (unlabelCtx .p (Pure ()))
-- determinism (Dist-join p) (Dist-join .p) = refl
-- determinism (joinCtx p s₁) (joinCtx .p s₂) rewrite determinism s₁ s₂ = refl
-- determinism (joinCtx p (Pure ())) (join .p)
-- determinism (joinCtx p (Pure ())) (joinEx .p)
-- determinism (join p) (joinCtx .p (Pure ()))
-- determinism (join p) (join .p) = refl
-- determinism (joinEx p) (joinCtx .p (Pure ()))
-- determinism (joinEx p) (joinEx .p) = refl

-- preservation : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {τ : Ty} {c₁ c₂ : CTerm τ} -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> τ ≡ τ
-- preservation s = refl
