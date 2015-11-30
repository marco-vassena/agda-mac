module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality
open import Data.Sum

-- Memory grows, but it does not shrink 
memoryGrows : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
memoryGrows {Δ₁} s = aux Δ₁ s
  where aux : ∀ {τ Δ₂} -> (Δ₁ : Context) -> {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                ⟨ m₁ ∥ c₁ ⟩⟼ ⟨ m₂ ∥ c₂ ⟩ -> Δ₁ ⊆ Δ₂
        aux Δ (Pure x) = refl-⊆ Δ
        aux Δ Return = refl-⊆ Δ
        aux Δ Dist->>= = refl-⊆ Δ
        aux Δ (BindCtx s₁) = aux Δ s₁
        aux Δ Bind = refl-⊆ Δ
        aux Δ BindEx = refl-⊆ Δ
        aux Δ Throw = refl-⊆ Δ
        aux Δ Dist-Catch = refl-⊆ Δ
        aux Δ (CatchCtx s₁) = aux Δ s₁
        aux Δ Catch = refl-⊆ Δ
        aux Δ CatchEx = refl-⊆ Δ
        aux Δ (label p) = refl-⊆ Δ
        aux Δ (Dist-unlabel p) = refl-⊆ Δ
        aux Δ (unlabel p) = refl-⊆ Δ
        aux Δ (unlabelEx p) = refl-⊆ Δ
        aux Δ (unlabelCtx p s₁) = aux Δ s₁
        aux Δ (Dist-join p) = refl-⊆ Δ
        aux Δ (joinCtx p s₁) = aux Δ s₁
        aux Δ (join p) = refl-⊆ Δ
        aux Δ (joinEx p) = refl-⊆ Δ
        aux Δ (new p) = drop (refl-⊆ Δ)
        aux Δ (Dist-write p) = refl-⊆ Δ
        aux Δ (Dist-read p) = refl-⊆ Δ
        aux Δ (writeCtx p s₁) = aux Δ s₁
        aux Δ (write p r) = refl-⊆ Δ
        aux Δ (readCtx p s₁) = aux Δ s₁
        aux Δ (read p r) = refl-⊆ Δ

data ValidRef {Δᵐ} (m : Memory Δᵐ) : ∀ {τ}-> CTerm τ -> Set where
  Ref : ∀ {α l Δ} {Γ : Env Δ} -> (ValidEnv m Γ) -> (r : α ∈ Δᵐ) -> ValidRef m (Γ , Ref r)

validRef-ext : ∀ {Δ₁ Δ₂ Δ τ} {l : Label} {Γ : Env Δ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} ->
                 (r : τ ∈ Δ₁) -> Δ₁ ⊆ Δ₂ -> ValidRef m₁ (Γ , Ref r) -> ValidRef m₂ (Γ , Ref r)
validRef-ext r x (Ref Γ .r) = {!Ref Γ ? !}

validRef : ∀ {Δ Δ₁ Δ₂ τ} {l : Label} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} (r : τ ∈ Δ₁) ->
             Δ₁ ⊆ Δ₂ -> ValidT {Δ} m₁ (Ref {Δᵐ = Δ₁} r) -> ValidT {Δ} {Δ₂} m₂ (Ref {Δᵐ = Δ₂} {!r!})
validRef r p v = {!Ref (extend-∈ r p)!}

validT-ext : ∀ {Δ Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {t : Term Δ τ} ->
               ValidT m₁ t -> Δ₁ ⊆ Δ₂ -> ValidT m₂ t
validT-ext （） p = （）
validT-ext True p = True
validT-ext False p = False
validT-ext (Var p) p₁ = Var p
validT-ext (App v v₁) p = App (validT-ext v p) (validT-ext v₁ p)
validT-ext (Abs v) p = Abs (validT-ext v p)
validT-ext ξ p = ξ
validT-ext (Mac v) p = Mac (validT-ext v p)
validT-ext (Macₓ v) p = Macₓ (validT-ext v p)
validT-ext (Res v) p = Res (validT-ext v p)
validT-ext (Resₓ v) p = Resₓ (validT-ext v p)
validT-ext (Ref Here) (drop p) = {!Ref ?!}
validT-ext (Ref Here) (cons p) = {!Ref Here!}
validT-ext (Ref (There r)) p = {!!}
-- {!Ref {Δᵐ = Δ₂} {α} {l} {m = m₂} (extend-∈ r p)!}
validT-ext (If v Then v₁ Else v₂) p
  = If validT-ext v p Then validT-ext v₁ p Else validT-ext v₂ p
validT-ext (Return v) p = Return (validT-ext v p)
validT-ext (v >>= v₁) p = (validT-ext v p) >>= (validT-ext v₁ p)
validT-ext (Throw v) p = Throw (validT-ext v p)
validT-ext (Catch v v₁) p = Catch (validT-ext v p) (validT-ext v₁ p)
validT-ext (label x) p = label x
validT-ext (unlabel x v) p = unlabel x (validT-ext v p)
validT-ext (join x v) p = join x (validT-ext v p)
validT-ext (read x v) p = read x (validT-ext v p)
validT-ext (write x v v₁) p = write x (validT-ext v p) (validT-ext v₁ p)
validT-ext (new x v) p = new x (validT-ext v p)
validT-ext ∙ p = ∙


-- If a term is valid in a certain memory, then it is also valid in an extended memory
valid-ext : ∀ {Δ₁ Δ₂ τ} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c : CTerm τ} ->
                   Valid m₁ c -> Δ₁ ⊆ Δ₂ -> Valid m₂ c

validEnv-ext : ∀ {Δ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {Γ : Env Δ} ->
                      ValidEnv m₁ Γ -> Δ₁ ⊆ Δ₂ -> ValidEnv m₂ Γ
validEnv-ext [] p = []
validEnv-ext (x ∷ Γ) p = (valid-ext x p) ∷ (validEnv-ext Γ p)
                      

valid-ext (Γ , t) p = validEnv-ext Γ p , validT-ext t p
valid-ext (v $ v₁) p = (valid-ext v p) $ (valid-ext v₁ p)
valid-ext (If v Then v₁ Else v₂) p = If (valid-ext v p) Then (valid-ext v₁ p) Else (valid-ext v₂ p)
valid-ext (v >>= v₁) p = (valid-ext v p) >>= (valid-ext v₁ p)
valid-ext (Catch v v₁) p = Catch (valid-ext v p) (valid-ext v₁ p)
valid-ext (unlabel x v) p = unlabel x (valid-ext v p)
valid-ext (join x v) p = join x (valid-ext v p)
valid-ext (read x v) p = read x (valid-ext v p)
valid-ext (write x v v₁) p = write x (valid-ext v p) (valid-ext v₁ p)
valid-ext ∙ p = ∙

valid-lookup : ∀ {Δᵐ Δ τ} {m : Memory Δᵐ} {Γ : Env Δ} -> (p : τ ∈ Δ) -> ValidEnv m Γ -> Valid m (p !! Γ)
valid-lookup Here (x ∷ Γ₁) = x
valid-lookup (There p) (x ∷ Γ₁) = valid-lookup p Γ₁

valid-preserving : ∀ {τ Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm τ} ->
                     ⟨ m₁ ∥ c₁ ⟩⟼ ⟨ m₂ ∥ c₂ ⟩ -> Valid m₁ c₁ -> Valid m₂ c₂
valid-preserving (Pure (AppL s)) (v $ v₁) = (valid-preserving (Pure s) v) $ v₁
valid-preserving (Pure Beta) (Γ , Abs x $ v) = (Γ , (Abs (Var Here))) $ (v ∷ Γ , x)
valid-preserving (Pure Lookup) (Γ , (Var p)) = (Γ , Abs (Var Here)) $ valid-lookup p Γ
valid-preserving (Pure Dist-$) (Γ , App f x) = Γ , f $ Γ , x
valid-preserving (Pure Dist-If) (Γ , If c Then t Else e) = If (Γ , c) Then (Γ , t) Else (Γ , e)
valid-preserving (Pure (IfCond x)) (If v Then v₁ Else v₂) = If (valid-preserving (Pure x) v) Then v₁ Else v₂
valid-preserving (Pure IfTrue) (If Γ , True Then v₁ Else v₂) = Γ , Abs (Var Here) $ v₁
valid-preserving (Pure IfFalse) (If Γ , False Then v₁ Else v₂) = Γ , Abs (Var Here) $ v₂
valid-preserving (Pure Dist-∙) (Γ , ∙) = ∙
valid-preserving (Pure Hole) ∙ = ∙
valid-preserving Return (Γ , Return v) = (Γ , Abs (Var Here)) $ (Γ , (Mac v))
valid-preserving Dist->>= (Γ , v₁ >>= v₂) = (Γ , v₁) >>= (Γ , v₂)
valid-preserving (BindCtx s) (v >>= v₁) = (valid-preserving s v) >>= (valid-ext v₁ (memoryGrows s))
valid-preserving Bind v = {!!}
valid-preserving BindEx v = {!!}
valid-preserving Throw v = {!!}
valid-preserving Dist-Catch v = {!!}
valid-preserving (CatchCtx s) v = {!!}
valid-preserving Catch v = {!!}
valid-preserving CatchEx v = {!!}
valid-preserving (label p) v = {!!}
valid-preserving (Dist-unlabel p) v = {!!}
valid-preserving (unlabel p) v = {!!}
valid-preserving (unlabelEx p) v = {!!}
valid-preserving (unlabelCtx p s) v = {!!}
valid-preserving (Dist-join p) v = {!!}
valid-preserving (joinCtx p s) v = {!!}
valid-preserving (join p) v = {!!}
valid-preserving (joinEx p) v = {!!}
valid-preserving (new p) v = {!!}
valid-preserving (Dist-write p) v = {!!}
valid-preserving (Dist-read p) v = {!!}
valid-preserving (writeCtx p s) v = {!!}
valid-preserving (write p r) v = {!!}
valid-preserving (readCtx p s) v = {!!}
valid-preserving (read p r) v = {!!}

progress : ∀ {τ Δ} {m : Memory Δ} (c : CTerm τ) -> Valid m c -> (Redex m c) ⊎ (IsValue c)
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
progress (write p (Γ , Ref .r) c) (write .p (Γ' , Ref r) v₁) | inj₂ (.Γ , Ref .r) = inj₁ (Step (write p r))
progress (read p r) (read .p v) with progress r v
progress (read p r) (read .p v) | inj₁ (Step x) = inj₁ (Step (readCtx p x))
progress (read p (Γ , Ref .r)) (read .p (Γ' , Ref r)) | inj₂ (.Γ , Ref .r) = inj₁ (Step (read p r))
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
