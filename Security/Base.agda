-- Defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Typed.Base
open import Relation.Binary.PropositionalEquality

-- Erasure function.
-- ε l t transform a term t in ∙ if it is above the security level l.
ε : ∀ {τ Δ} (lₐ : Label) -> Term Δ τ -> Term Δ τ
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If c Then t Else e) = If (ε lₐ c) Then (ε lₐ t) Else (ε lₐ e)
ε {Mac lᵈ α} lₐ (Return t) with lᵈ ⊑? lₐ
ε {Mac lᵈ α} lₐ (Return t) | yes p = Return (ε lₐ t) 
ε {Mac lᵈ α} lₐ (Return t) | no ¬p = ∙
ε {Mac lᵈ β} lₐ (m >>= h) with lᵈ ⊑? lₐ 
ε {Mac lᵈ β} lₐ (m >>= h) | yes p = (ε lₐ m) >>= (ε lₐ h)
ε {Mac lᵈ β} lₐ (m >>= h) | no ¬p = ∙
ε lₐ ξ = ξ
ε {Mac lᵈ α} lₐ (Throw t) with lᵈ ⊑? lₐ
ε {Mac lᵈ α} lₐ (Throw t) | yes p = Throw (ε lₐ t)
ε {Mac lᵈ α} lₐ (Throw t) | no ¬p = ∙
ε {Mac lᵈ α} lₐ (Catch m h) with lᵈ ⊑? lₐ
ε {Mac lᵈ α} lₐ (Catch m h) | yes p = Catch (ε lₐ m) (ε lₐ h)
ε {Mac lᵈ α} lₐ (Catch m h) | no ¬p = ∙ --  Catch (ε lₐ m) (ε lₐ h)
ε {Mac lᵈ α} lₐ (Mac t) with lᵈ ⊑? lₐ
ε {Mac lᵈ α} lₐ (Mac t) | yes p = Mac (ε lₐ t)
ε {Mac lᵈ α} lₐ (Mac t) | no ¬p = ∙
ε {Mac lᵈ α} lₐ (Macₓ t) with lᵈ ⊑? lₐ
ε {Mac lᵈ α} lₐ (Macₓ t) | yes p = Macₓ (ε lₐ t)
ε {Mac lᵈ α} lₐ (Macₓ t) | no ¬p = ∙
ε {Labeled lᵈ α} lₐ (Res t) with lᵈ ⊑? lₐ
ε {Labeled lᵈ α} lₐ (Res t) | yes p = Res (ε lₐ t)
ε {Labeled lᵈ α} lₐ (Res t) | no ¬p = Res ∙
ε lₐ (label {l = lᵈ} {h = lʰ} d⊑h t) with lᵈ ⊑? lₐ
ε lₐ (label d⊑h t) | yes d⊑a = label d⊑h (ε lₐ t) 
ε lₐ (label d⊑h t) | no ¬d⊑a = {!!}
ε lₐ (unlabel x t) = unlabel x (ε lₐ t)
ε lₐ ∙ = ∙

εᶜ : ∀ {τ} -> Label -> CTerm τ -> CTerm τ
εᶜ-env : ∀ {Δ} -> Label -> Env Δ -> Env Δ
-- εᶜ-Labeled : ∀ {τ l₁} -> (l₂ : Label) -> l₁ ⊑ l₂ -> CTerm (Labeled l₁ τ) -> CTerm (Labeled l₁ τ)
-- εᶜ-Mac : ∀ {τ l₁} -> (l₂ : Label) -> l₁ ⊑ l₂ -> CTerm (Mac l₁ τ) -> CTerm (Mac l₁ τ)

εᶜ lₐ (Γ , t) = (εᶜ-env lₐ Γ) , (ε lₐ t)
εᶜ lₐ (f $ x) = (εᶜ lₐ f) $ (εᶜ lₐ x)
εᶜ {Mac lᵈ β} lₐ (f $ˡ Γ , t) with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ β} lₐ (f $ˡ Γ , t) | yes p = (εᶜ lₐ f) $ˡ εᶜ-env lₐ Γ , ε lₐ t
εᶜ {Mac lᵈ β} lₐ (f $ˡ Γ , t) | no ¬p = εᶜ-env lₐ Γ , ∙
εᶜ lₐ (If c Then t Else e) = If (εᶜ lₐ c) Then (εᶜ lₐ t) Else εᶜ lₐ e
εᶜ {Mac lᵈ β} lₐ (m >>= k) with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ β} lₐ (m  >>= k) | yes p = εᶜ lₐ m >>= εᶜ lₐ k
εᶜ {Mac lᵈ β} lₐ ((Γ , t) >>= k) | no ¬p = (εᶜ-env lₐ Γ) , ∙ 
εᶜ {Mac lᵈ β} lₐ (m >>= k) | no ¬p = εᶜ lₐ m >>= εᶜ lₐ k
εᶜ {Mac lᵈ α} lₐ (Catch m h) with lᵈ ⊑? lₐ
εᶜ {Mac lᵈ α} lₐ (Catch m h) | yes p = Catch (εᶜ lₐ m) (εᶜ lₐ h)
εᶜ {Mac lᵈ α} lₐ (Catch (Γ  , t) h) | no ¬p = εᶜ-env lₐ Γ , ∙
εᶜ {Mac lᵈ α} lₐ (Catch m h) | no ¬p = Catch (εᶜ lₐ m) (εᶜ lₐ h)
εᶜ lₐ (unlabel x c) = unlabel x (εᶜ lₐ c) -- Inspect labels, erase if possible

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

open import Typed.Semantics

εᶜ-lookup : ∀ {Δ τ} {{lₐ}} -> (p : τ ∈ Δ) (Γ : Env Δ) -> εᶜ lₐ (p !! Γ) ≡ p !! εᶜ-env lₐ Γ
εᶜ-lookup Here (x ∷ Γ) = refl
εᶜ-lookup (There p) (x ∷ Γ) rewrite εᶜ-lookup p Γ = refl

εᶜ-distributes : ∀ {τ} {c₁ c₂ : CTerm τ} -> (lₐ : Label) -> c₁ ⟼ c₂ -> εᶜ lₐ c₁ ⟼ εᶜ lₐ c₂
εᶜ-distributes lₐ (AppL s) = AppL (εᶜ-distributes lₐ s)
εᶜ-distributes lₐ Beta = Beta
εᶜ-distributes {c₁ = Γ , Var p} lₐ Lookup rewrite εᶜ-lookup p Γ = Lookup
εᶜ-distributes {c₁ = Γ , App f x} lₐ Dist-$ = Dist-$
εᶜ-distributes lₐ Dist-If = Dist-If
εᶜ-distributes lₐ (IfCond s) = IfCond (εᶜ-distributes lₐ s)
εᶜ-distributes lₐ IfTrue = IfTrue
εᶜ-distributes lₐ IfFalse = IfFalse
εᶜ-distributes {Mac lᵈ α} lₐ Return with lᵈ ⊑? lₐ 
εᶜ-distributes {Mac lᵈ α} lₐ Return | yes p = Return
εᶜ-distributes {Mac lᵈ α} lₐ Return | no ¬p = Hole
εᶜ-distributes {Mac lᵈ α} {Γ , m >>= k} lₐ Dist->>= with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} {Γ , m >>= k} lₐ Dist->>= | yes p = Dist->>=
εᶜ-distributes {Mac lᵈ α} {Γ , m >>= k} lₐ Dist->>= | no ¬p = Hole
εᶜ-distributes {Mac lᵈ α} {m >>= k} lₐ (BindCtx s) with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} {m >>= k} lₐ (BindCtx s) | yes p = BindCtx (εᶜ-distributes lₐ s)
εᶜ-distributes {Mac lᵈ α} {m >>= k} lₐ (BindCtx s) | no ¬p = {!BindCtx ?!} -- BindCtx (εᶜ-distributes lₐ s)
εᶜ-distributes {Mac lᵈ β} lₐ Bind with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ β} lₐ Bind | yes p with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ β} lₐ Bind | yes p₁ | yes p = Bind
εᶜ-distributes {Mac lᵈ β} lₐ Bind | yes p | no ¬p = {!!} -- Bind
εᶜ-distributes {Mac lᵈ β} lₐ Bind | no ¬p = Hole
εᶜ-distributes {Mac lᵈ α} lₐ BindEx with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} lₐ BindEx | yes p with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} lₐ BindEx | yes p₁ | yes p = BindEx
εᶜ-distributes {Mac lᵈ α} lₐ BindEx | yes p | no ¬p = ⊥-elim (¬p p)
εᶜ-distributes {Mac lᵈ α} lₐ BindEx | no ¬p = Hole -- BindEx
εᶜ-distributes {Mac lᵈ α} lₐ Throw with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} lₐ Throw | yes p = Throw
εᶜ-distributes {Mac lᵈ α} lₐ Throw | no ¬p = Hole
εᶜ-distributes {Mac lᵈ α} {Γ , Catch m h} lₐ Dist-Catch with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} {Γ , Catch m h} lₐ Dist-Catch | yes p = Dist-Catch
εᶜ-distributes {Mac lᵈ α} {Γ , Catch m h} lₐ Dist-Catch | no ¬p = Hole
εᶜ-distributes {Mac lᵈ α} {Catch m h} {Catch m' .h} lₐ (CatchCtx s) with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} {Catch m h} {Catch m' .h} lₐ (CatchCtx s) | yes p = CatchCtx (εᶜ-distributes lₐ s)
εᶜ-distributes {Mac lᵈ α} {Catch (x , x₁) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (m $ m₁) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (m $ˡ x , x₁) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (If m Then m₁ Else m₂) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (m >>= m₁) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (Catch m m₁) h} {Catch m' .h} lₐ (CatchCtx s) | no ¬p = {!!}
εᶜ-distributes {Mac lᵈ α} {Catch (unlabel x m) h} {Catch m' .h}lₐ (CatchCtx s) | no ¬p = {!!} -- CatchCtx (εᶜ-distributes lₐ s)
εᶜ-distributes {Mac lᵈ α} lₐ Catch with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} lₐ Catch | yes p = {!!}
εᶜ-distributes {Mac lᵈ α} lₐ Catch | no ¬p = Hole -- Catch
εᶜ-distributes {Mac lᵈ α} lₐ CatchEx with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ α} lₐ CatchEx | yes p = {!!} -- CatchEx
εᶜ-distributes {Mac lᵈ α} lₐ CatchEx | no ¬p = Hole -- CatchEx
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) with lʰ ⊑? lₐ
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | yes h⊑a with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | yes h⊑a | yes d⊑a with lʰ ⊑? lₐ -- Agda not sharing results
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | yes h⊑a | yes d⊑a | yes h⊑a' = label d⊑h
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | yes h⊑a | yes d⊑a | no ¬h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | yes h⊑a | no ¬d⊑a = {!!}
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | no ¬h⊑a with lᵈ ⊑? lₐ
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | no ¬h⊑a | yes d⊑a with lʰ ⊑? lₐ -- -- Agda not sharing results
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | no ¬h⊑a | yes d⊑a | yes h⊑a = ⊥-elim (¬h⊑a h⊑a)
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | no ¬h⊑a | yes d⊑a | no ¬h⊑a' = {!!} -- label d⊑h 
εᶜ-distributes {Mac lᵈ (Labeled lʰ α)} lₐ (label d⊑h) | no ¬h⊑a | no ¬d⊑a = {!!}
εᶜ-distributes lₐ (Dist-unlabel p) = Dist-unlabel p
εᶜ-distributes {Mac lʰ α} lₐ (unlabel {l = lᵈ} {h = .lʰ} d⊑h) = {!!}
εᶜ-distributes lₐ (unlabelCtx p s) = unlabelCtx p (εᶜ-distributes lₐ s)
εᶜ-distributes lₐ Hole = Hole

--------------------------------------------------------------------------------

-- Graph of the function ε
-- Erasure l t tₑ corresponds to ε l t ≡ t'
-- data Erasure (l : Label) {n : ℕ} : Term n -> Term n -> Set where
--   True : Erasure l True True
--   False : Erasure l False False
--   Var : (x : Fin n) -> Erasure l (Var x) (Var x)
--   Abs : {t tₑ : Term (suc n)} -> Erasure l t tₑ -> Erasure l (Abs t) (Abs tₑ)
--   App : {f fₑ x xₑ : Term n} -> Erasure l f fₑ -> Erasure l x xₑ -> Erasure l (App f x) (App fₑ xₑ)
--   If_Then_Else_ : {c cₑ t tₑ e eₑ : Term n} -> 
--                   Erasure l c cₑ -> Erasure l t tₑ -> Erasure l e eₑ ->
--                   Erasure l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)
--   Return : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Return t) (Return tₑ)
--   _>>=_ : ∀ {m mₑ k kₑ : Term n} -> Erasure l m mₑ -> Erasure l k kₑ ->
--             Erasure l (m >>= k) (mₑ >>= kₑ)
--   ξ : Erasure l ξ ξ
--   Throw : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Throw t) (Throw tₑ)
--   Catch : {m mₑ h hₑ : Term n} -> Erasure l m mₑ -> Erasure l h hₑ -> Erasure l (Catch m h) (Catch mₑ hₑ) 
--   Mac : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Mac t) (Mac tₑ)
--   Macₓ : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Macₓ t) (Macₓ tₑ)
--   Res : {t tₑ : Term n} -> (l' : Label) -> l ⊑ l' -> 
--         Erasure l t tₑ -> Erasure l (Res l' t) (Res l' tₑ)
--   Res∙ : ∀ {t : Term n} -> (l' : Label) -> ¬ (l ⊑ l') -> Erasure l (Res l' t) (Res l' ∙)
--   label : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t tₑ : Term n} -> l ⊑ l₂ -> 
--             Erasure l t tₑ -> Erasure l (label x t) (label x tₑ)
--   label∙ : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t : Term n} -> ¬ (l ⊑ l₂) -> Erasure l (label x t) (label x ∙) 
--   unlabel : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (unlabel t) (unlabel tₑ)
--   ∙ : Erasure l ∙ ∙

-- -- Sound
-- -- For any term t I can construct Erasure l t (ε l t), 
-- -- i.e. Erasure approximates correctly the erasure function. 
-- ε-Erasure : ∀ {l n} -> (t : Term n) -> Erasure l t (ε l t)
-- ε-Erasure True = True
-- ε-Erasure False = False
-- ε-Erasure (Var x) = Var x
-- ε-Erasure (Abs t) = Abs (ε-Erasure t)
-- ε-Erasure (App f x) = App (ε-Erasure f) (ε-Erasure x)
-- ε-Erasure (If c Then t Else e) = If ε-Erasure c Then ε-Erasure t Else ε-Erasure e
-- ε-Erasure (Return t) = Return (ε-Erasure t)
-- ε-Erasure (m >>= k) = ε-Erasure m >>= ε-Erasure k
-- ε-Erasure ξ = ξ
-- ε-Erasure (Throw e) = Throw (ε-Erasure e)
-- ε-Erasure (Catch m h) = Catch (ε-Erasure m) (ε-Erasure h)
-- ε-Erasure (Mac t) = Mac (ε-Erasure t)
-- ε-Erasure (Macₓ t) = Macₓ (ε-Erasure t)
-- ε-Erasure {l₁} (Res l₂ t) with l₁ ⊑? l₂
-- ε-Erasure (Res l₂ t) | yes p = Res l₂ p (ε-Erasure t)
-- ε-Erasure (Res l₂ t) | no ¬p = Res∙ l₂ ¬p
-- ε-Erasure {l₁} (label {h = l₂} x t) with l₁ ⊑? l₂
-- ε-Erasure (label x t) | yes p = label p (ε-Erasure t)
-- ε-Erasure (label x t) | no ¬p = label∙ ¬p
-- ε-Erasure (unlabel t) = unlabel (ε-Erasure t)
-- ε-Erasure ∙ = ∙

-- -- Complete
-- -- For any term t and tₑ such that Erasure l t tₑ, the ε l t ≡ tₑ
-- -- i.e. Erasure represents only the erasure function.
-- Erasure-ε : ∀ {l n} {t tₑ : Term n} -> Erasure l t tₑ -> ε l t ≡ tₑ
-- Erasure-ε True = refl
-- Erasure-ε False = refl
-- Erasure-ε (Var x) = refl
-- Erasure-ε (Abs t) rewrite Erasure-ε t = refl
-- Erasure-ε (App f x) rewrite Erasure-ε f | Erasure-ε x = refl
-- Erasure-ε (If c Then t Else e) rewrite
--   Erasure-ε c | Erasure-ε t | Erasure-ε e = refl
-- Erasure-ε (Return t) rewrite Erasure-ε t = refl
-- Erasure-ε (m >>= k) rewrite Erasure-ε m | Erasure-ε k = refl
-- Erasure-ε ξ = refl
-- Erasure-ε (Throw e) rewrite Erasure-ε e = refl
-- Erasure-ε (Catch m h) rewrite Erasure-ε m | Erasure-ε h = refl
-- Erasure-ε (Mac t) rewrite Erasure-ε t = refl
-- Erasure-ε (Macₓ t) rewrite Erasure-ε t = refl
-- Erasure-ε {l₁} (Res l₂ l₁⊑l₂ t) with l₁ ⊑? l₂
-- Erasure-ε (Res l₂ l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
-- Erasure-ε (Res l₂ l₁⊑l₂ t) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε {l₁} (Res∙ l₂ l₁⋢l₂) with l₁ ⊑? l₂
-- Erasure-ε (Res∙ l₂ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε (Res∙ l₂ l₁⋢l₂) | no _ = refl
-- Erasure-ε {l₁} (label {l₂ = l₂} l₁⊑l₂ t) with l₁ ⊑? l₂
-- Erasure-ε (label l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
-- Erasure-ε (label l₁⊑l₂ t₁) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε {l₁} (label∙ {l₂ = l₂} l₁⋢l₂) with l₁ ⊑? l₂
-- Erasure-ε (label∙ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
-- Erasure-ε (label∙ l₁⋢l₂) | no _ = refl
-- Erasure-ε (unlabel t) rewrite Erasure-ε t = refl
-- Erasure-ε ∙ = refl

-- -- Corresponds to ε l t ≡ ε l (ε l t).
-- -- I am using the graph of ε because of unification issues. 
-- Erasure-idem : ∀ {n} {{l}} {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l tₑ tₑ 
-- Erasure-idem True = True
-- Erasure-idem False = False
-- Erasure-idem (Var x) = Var x
-- Erasure-idem (Abs t) = Abs (Erasure-idem t)
-- Erasure-idem (App f x) = App (Erasure-idem f) (Erasure-idem x)
-- Erasure-idem (If c Then t Else e) = If (Erasure-idem c) Then (Erasure-idem t) Else (Erasure-idem e)
-- Erasure-idem (Return t) = Return (Erasure-idem t)
-- Erasure-idem (m >>= k) = (Erasure-idem m) >>= (Erasure-idem k)
-- Erasure-idem ξ = ξ
-- Erasure-idem (Throw e) = Throw (Erasure-idem e)
-- Erasure-idem (Catch m h) = Catch (Erasure-idem m) (Erasure-idem h)
-- Erasure-idem (Mac t) = Mac (Erasure-idem t)
-- Erasure-idem (Macₓ t) = Macₓ (Erasure-idem t)
-- Erasure-idem (Res l x t) = Res l x (Erasure-idem t)
-- Erasure-idem (Res∙ l x) = Res∙ l x
-- Erasure-idem (label x t) = label x (Erasure-idem t)
-- Erasure-idem (label∙ x) = label∙ x
-- Erasure-idem (unlabel t) = unlabel (Erasure-idem t)
-- Erasure-idem ∙ = ∙

-- -- Now we need a similar construction for εᶜ and εᶜ-env

-- mutual
--   data Erasureᶜ (l : Label) : CTerm -> CTerm -> Set where
--     _,_ : ∀ {n} {t tₑ : Term n} {Γ Γₑ : Env n} -> 
--             ErasureEnvᶜ l Γ Γₑ -> Erasure l t tₑ -> Erasureᶜ l (Γ , t) (Γₑ , tₑ)
--     _$_ : ∀ {f fₑ x xₑ} -> Erasureᶜ l f fₑ -> Erasureᶜ l x xₑ -> Erasureᶜ l (f $ x) (fₑ $ xₑ)
    
--     If_Then_Else_ : ∀ {c cₑ t tₑ e eₑ} -> Erasureᶜ l c cₑ -> Erasureᶜ l t tₑ -> Erasureᶜ l e eₑ ->
--                     Erasureᶜ l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)

--     _>>=_ : ∀ {m mₑ k kₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l k kₑ -> Erasureᶜ l (m >>= k) (mₑ >>= kₑ)

--     Catch : ∀ {m mₑ h hₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l h hₑ -> Erasureᶜ l (Catch m h) (Catch mₑ hₑ)

--     unlabel : ∀ {t tₑ} -> Erasureᶜ l t tₑ -> Erasureᶜ l (unlabel t) (unlabel tₑ)


--   data ErasureEnvᶜ (l : Label) : ∀ {n} -> Env n -> Env n -> Set where
--     [] : ErasureEnvᶜ l [] []
--     _∷_ : ∀ {n c cₑ} {Γ Γₑ : Env n} -> Erasureᶜ l c cₑ -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l (c ∷ Γ) (cₑ ∷ Γₑ)

-- -- Sound
-- εᶜ-Erasureᶜ : ∀ {{l}} -> (c : CTerm) -> Erasureᶜ l c (εᶜ l c)
-- εᶜ-env-ErasureEnvᶜ : ∀ {l n} -> (Γ : Env n) -> ErasureEnvᶜ l Γ (εᶜ-env l Γ)

-- εᶜ-Erasureᶜ (Γ , x) = (εᶜ-env-ErasureEnvᶜ Γ) , (ε-Erasure x)
-- εᶜ-Erasureᶜ (f $ x) = εᶜ-Erasureᶜ f $ εᶜ-Erasureᶜ x
-- εᶜ-Erasureᶜ (If c Then c₁ Else c₂) = If εᶜ-Erasureᶜ c Then εᶜ-Erasureᶜ c₁ Else εᶜ-Erasureᶜ c₂
-- εᶜ-Erasureᶜ (c >>= c₁) = εᶜ-Erasureᶜ c >>= εᶜ-Erasureᶜ c₁
-- εᶜ-Erasureᶜ (Catch c c₁) = Catch (εᶜ-Erasureᶜ c) (εᶜ-Erasureᶜ c₁)
-- εᶜ-Erasureᶜ (unlabel c) = unlabel (εᶜ-Erasureᶜ c)

-- εᶜ-env-ErasureEnvᶜ [] = []
-- εᶜ-env-ErasureEnvᶜ (x ∷ Γ) = (εᶜ-Erasureᶜ x) ∷ εᶜ-env-ErasureEnvᶜ Γ

-- -- Complete
-- Erasureᶜ-εᶜ : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> εᶜ l c ≡ cₑ
-- ErasureEnvᶜ-εᶜ-env : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> εᶜ-env l Γ ≡ Γₑ

-- Erasureᶜ-εᶜ (Γ , e) rewrite
--   ErasureEnvᶜ-εᶜ-env Γ | Erasure-ε e = refl
-- Erasureᶜ-εᶜ (f $ x) rewrite
--   Erasureᶜ-εᶜ f | Erasureᶜ-εᶜ x = refl
-- Erasureᶜ-εᶜ (If c Then t Else e) rewrite
--   Erasureᶜ-εᶜ c | Erasureᶜ-εᶜ t | Erasureᶜ-εᶜ e = refl
-- Erasureᶜ-εᶜ (m >>= k) rewrite
--   Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ k = refl
-- Erasureᶜ-εᶜ (Catch m h) rewrite
--   Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ h = refl
-- Erasureᶜ-εᶜ (unlabel e) rewrite
--   Erasureᶜ-εᶜ e = refl

-- ErasureEnvᶜ-εᶜ-env [] = refl
-- ErasureEnvᶜ-εᶜ-env (e ∷ Γ) rewrite
--   Erasureᶜ-εᶜ e | ErasureEnvᶜ-εᶜ-env Γ = refl

-- Erasureᶜ-idem : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> Erasureᶜ l cₑ cₑ 
-- ErasureEnvᶜ-idem : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l Γₑ Γₑ 

-- Erasureᶜ-idem (Γ , c) = (ErasureEnvᶜ-idem Γ) , (Erasure-idem c)
-- Erasureᶜ-idem (f $ x) = Erasureᶜ-idem f $ Erasureᶜ-idem x
-- Erasureᶜ-idem (If c Then t Else e) = If Erasureᶜ-idem c Then Erasureᶜ-idem t Else Erasureᶜ-idem e
-- Erasureᶜ-idem (c >>= c₁) = Erasureᶜ-idem c >>= Erasureᶜ-idem c₁
-- Erasureᶜ-idem (Catch c c₁) = Catch (Erasureᶜ-idem c) (Erasureᶜ-idem c₁)
-- Erasureᶜ-idem (unlabel c) = unlabel (Erasureᶜ-idem c)

-- ErasureEnvᶜ-idem [] = []
-- ErasureEnvᶜ-idem (x ∷ Γ) = (Erasureᶜ-idem x) ∷ (ErasureEnvᶜ-idem Γ)

-- --------------------------------------------------------------------------------
-- -- Going through the graph of the erasure function we can prove the original
-- -- idempotence lemma.

-- -- ε is idempotent
-- ε-idem : ∀ {l n} -> (t : Term n) -> ε l t ≡ ε l (ε l t)
-- ε-idem t with Erasure-idem (ε-Erasure t)
-- ... | r = sym (Erasure-ε r)

-- -- εᶜ is idempotent
-- εᶜ-idem : ∀ {l} -> (c : CTerm) -> εᶜ l c ≡ εᶜ l (εᶜ l c)
-- εᶜ-idem c with Erasureᶜ-idem (εᶜ-Erasureᶜ c) 
-- ... | r = sym (Erasureᶜ-εᶜ r)

-- -- εᶜ-env is idempotent
-- εᶜ-env-idem : ∀ {l n} -> (Γ : Env n) -> εᶜ-env l Γ ≡ εᶜ-env l (εᶜ-env l Γ)
-- εᶜ-env-idem Γ with ErasureEnvᶜ-idem (εᶜ-env-ErasureEnvᶜ Γ)
-- ... | r = sym (ErasureEnvᶜ-εᶜ-env r)

-- --------------------------------------------------------------------------------
