-- Defines the erasure function, auxiliary lemmas and definitions.

module Security.Base where

open import Semantics
open import Proofs
open import Relation.Binary.PropositionalEquality

-- Erasure function.
-- ε l t transform a term t in ∙ if it is above the security level l.
ε : ∀ {n} -> Label -> Term n -> Term n
ε l True = True
ε l False = False
ε l (Var x) = Var x
ε l (Abs t) = Abs (ε l t)
ε l (App f x) = App (ε l f) (ε l x)
ε l (If c Then t Else e) = If (ε l c) Then (ε l t) Else (ε l e)
ε l (Return t) = Return (ε l t)
ε l (m >>= k) = (ε l m) >>= (ε l k)
ε l ξ = ξ
ε l (Throw t) = Throw (ε l t)
ε l (Catch m h) = Catch (ε l m) (ε l h)
ε l (Mac t) = Mac (ε l t)
ε l (Macₓ t) = Macₓ (ε l t)
ε l₁ (Res l₂ t) with l₁ ⊑? l₂
ε l₁ (Res l₂ t) | yes l₁⊑l₂ = Res l₂ (ε l₁ t)
ε l₁ (Res l₂ t) | no l₁⋢l₂ = Res l₂ ∙
ε l₁ (label {h = l₂} x t) with l₁ ⊑? l₂
ε l₁ (label x t) | yes l₁⊑l₂ = label x (ε l₁ t)
ε l₁ (label x t) | no l₁⋢l₂ = label x ∙
ε l (unlabel t) = unlabel (ε l t)
ε l ∙ = ∙

-- Erasure function for enviroments and closed terms,
-- defined mutually recursively.
εᶜ-env : ∀ {n} -> Label -> Env n -> Env n
εᶜ : Label -> CTerm -> CTerm

εᶜ l (Γ , t) = εᶜ-env l Γ , ε l t
εᶜ l (f $ x) = (εᶜ l f) $ (εᶜ l x)
εᶜ l (If c Then t Else e) = If (εᶜ l c) Then (εᶜ l t) Else (εᶜ l e)
εᶜ l (m >>= k) = (εᶜ l m) >>= (εᶜ l k)
εᶜ l (Catch m h) = Catch (εᶜ l m) (εᶜ l h)
εᶜ l (unlabel c) = unlabel (εᶜ l c)

εᶜ-env l [] = []
εᶜ-env l (x ∷ Γ) = εᶜ l x ∷ εᶜ-env l Γ

--------------------------------------------------------------------------------

-- Graph of the function ε
-- Erasure l t tₑ corresponds to ε l t ≡ t'
data Erasure (l : Label) {n : ℕ} : Term n -> Term n -> Set where
  True : Erasure l True True
  False : Erasure l False False
  Var : (x : Fin n) -> Erasure l (Var x) (Var x)
  Abs : {t tₑ : Term (suc n)} -> Erasure l t tₑ -> Erasure l (Abs t) (Abs tₑ)
  App : {f fₑ x xₑ : Term n} -> Erasure l f fₑ -> Erasure l x xₑ -> Erasure l (App f x) (App fₑ xₑ)
  If_Then_Else_ : {c cₑ t tₑ e eₑ : Term n} -> 
                  Erasure l c cₑ -> Erasure l t tₑ -> Erasure l e eₑ ->
                  Erasure l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)
  Return : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Return t) (Return tₑ)
  _>>=_ : ∀ {m mₑ k kₑ : Term n} -> Erasure l m mₑ -> Erasure l k kₑ ->
            Erasure l (m >>= k) (mₑ >>= kₑ)
  ξ : Erasure l ξ ξ
  Throw : {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Throw t) (Throw tₑ)
  Catch : {m mₑ h hₑ : Term n} -> Erasure l m mₑ -> Erasure l h hₑ -> Erasure l (Catch m h) (Catch mₑ hₑ) 
  Mac : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Mac t) (Mac tₑ)
  Macₓ : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (Macₓ t) (Macₓ tₑ)
  Res : {t tₑ : Term n} -> (l' : Label) -> l ⊑ l' -> 
        Erasure l t tₑ -> Erasure l (Res l' t) (Res l' tₑ)
  Res∙ : ∀ {t : Term n} -> (l' : Label) -> ¬ (l ⊑ l') -> Erasure l (Res l' t) (Res l' ∙)
  label : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t tₑ : Term n} -> l ⊑ l₂ -> 
            Erasure l t tₑ -> Erasure l (label x t) (label x tₑ)
  label∙ : ∀ {l₁ l₂} {x : l₁ ⊑ l₂} {t : Term n} -> ¬ (l ⊑ l₂) -> Erasure l (label x t) (label x ∙) 
  unlabel : ∀ {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l (unlabel t) (unlabel tₑ)
  ∙ : Erasure l ∙ ∙

-- Sound
-- For any term t I can construct Erasure l t (ε l t), 
-- i.e. Erasure approximates correctly the erasure function. 
ε-Erasure : ∀ {l n} -> (t : Term n) -> Erasure l t (ε l t)
ε-Erasure True = True
ε-Erasure False = False
ε-Erasure (Var x) = Var x
ε-Erasure (Abs t) = Abs (ε-Erasure t)
ε-Erasure (App f x) = App (ε-Erasure f) (ε-Erasure x)
ε-Erasure (If c Then t Else e) = If ε-Erasure c Then ε-Erasure t Else ε-Erasure e
ε-Erasure (Return t) = Return (ε-Erasure t)
ε-Erasure (m >>= k) = ε-Erasure m >>= ε-Erasure k
ε-Erasure ξ = ξ
ε-Erasure (Throw e) = Throw (ε-Erasure e)
ε-Erasure (Catch m h) = Catch (ε-Erasure m) (ε-Erasure h)
ε-Erasure (Mac t) = Mac (ε-Erasure t)
ε-Erasure (Macₓ t) = Macₓ (ε-Erasure t)
ε-Erasure {l₁} (Res l₂ t) with l₁ ⊑? l₂
ε-Erasure (Res l₂ t) | yes p = Res l₂ p (ε-Erasure t)
ε-Erasure (Res l₂ t) | no ¬p = Res∙ l₂ ¬p
ε-Erasure {l₁} (label {h = l₂} x t) with l₁ ⊑? l₂
ε-Erasure (label x t) | yes p = label p (ε-Erasure t)
ε-Erasure (label x t) | no ¬p = label∙ ¬p
ε-Erasure (unlabel t) = unlabel (ε-Erasure t)
ε-Erasure ∙ = ∙

-- Complete
-- For any term t and tₑ such that Erasure l t tₑ, the ε l t ≡ tₑ
-- i.e. Erasure represents only the erasure function.
Erasure-ε : ∀ {l n} {t tₑ : Term n} -> Erasure l t tₑ -> ε l t ≡ tₑ
Erasure-ε True = refl
Erasure-ε False = refl
Erasure-ε (Var x) = refl
Erasure-ε (Abs t) rewrite Erasure-ε t = refl
Erasure-ε (App f x) rewrite Erasure-ε f | Erasure-ε x = refl
Erasure-ε (If c Then t Else e) rewrite
  Erasure-ε c | Erasure-ε t | Erasure-ε e = refl
Erasure-ε (Return t) rewrite Erasure-ε t = refl
Erasure-ε (m >>= k) rewrite Erasure-ε m | Erasure-ε k = refl
Erasure-ε ξ = refl
Erasure-ε (Throw e) rewrite Erasure-ε e = refl
Erasure-ε (Catch m h) rewrite Erasure-ε m | Erasure-ε h = refl
Erasure-ε (Mac t) rewrite Erasure-ε t = refl
Erasure-ε (Macₓ t) rewrite Erasure-ε t = refl
Erasure-ε {l₁} (Res l₂ l₁⊑l₂ t) with l₁ ⊑? l₂
Erasure-ε (Res l₂ l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
Erasure-ε (Res l₂ l₁⊑l₂ t) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε {l₁} (Res∙ l₂ l₁⋢l₂) with l₁ ⊑? l₂
Erasure-ε (Res∙ l₂ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε (Res∙ l₂ l₁⋢l₂) | no _ = refl
Erasure-ε {l₁} (label {l₂ = l₂} l₁⊑l₂ t) with l₁ ⊑? l₂
Erasure-ε (label l₁⊑l₂ t) | yes _ rewrite Erasure-ε t = refl
Erasure-ε (label l₁⊑l₂ t₁) | no l₁⋢l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε {l₁} (label∙ {l₂ = l₂} l₁⋢l₂) with l₁ ⊑? l₂
Erasure-ε (label∙ l₁⋢l₂) | yes l₁⊑l₂ = ⊥-elim (l₁⋢l₂ l₁⊑l₂)
Erasure-ε (label∙ l₁⋢l₂) | no _ = refl
Erasure-ε (unlabel t) rewrite Erasure-ε t = refl
Erasure-ε ∙ = refl

-- Corresponds to ε l t ≡ ε l (ε l t).
-- I am using the graph of ε because of unification issues. 
Erasure-idem : ∀ {n} {{l}} {t tₑ : Term n} -> Erasure l t tₑ -> Erasure l tₑ tₑ 
Erasure-idem True = True
Erasure-idem False = False
Erasure-idem (Var x) = Var x
Erasure-idem (Abs t) = Abs (Erasure-idem t)
Erasure-idem (App f x) = App (Erasure-idem f) (Erasure-idem x)
Erasure-idem (If c Then t Else e) = If (Erasure-idem c) Then (Erasure-idem t) Else (Erasure-idem e)
Erasure-idem (Return t) = Return (Erasure-idem t)
Erasure-idem (m >>= k) = (Erasure-idem m) >>= (Erasure-idem k)
Erasure-idem ξ = ξ
Erasure-idem (Throw e) = Throw (Erasure-idem e)
Erasure-idem (Catch m h) = Catch (Erasure-idem m) (Erasure-idem h)
Erasure-idem (Mac t) = Mac (Erasure-idem t)
Erasure-idem (Macₓ t) = Macₓ (Erasure-idem t)
Erasure-idem (Res l x t) = Res l x (Erasure-idem t)
Erasure-idem (Res∙ l x) = Res∙ l x
Erasure-idem (label x t) = label x (Erasure-idem t)
Erasure-idem (label∙ x) = label∙ x
Erasure-idem (unlabel t) = unlabel (Erasure-idem t)
Erasure-idem ∙ = ∙

-- Now we need a similar construction for εᶜ and εᶜ-env

mutual
  data Erasureᶜ (l : Label) : CTerm -> CTerm -> Set where
    _,_ : ∀ {n} {t tₑ : Term n} {Γ Γₑ : Env n} -> 
            ErasureEnvᶜ l Γ Γₑ -> Erasure l t tₑ -> Erasureᶜ l (Γ , t) (Γₑ , tₑ)
    _$_ : ∀ {f fₑ x xₑ} -> Erasureᶜ l f fₑ -> Erasureᶜ l x xₑ -> Erasureᶜ l (f $ x) (fₑ $ xₑ)
    
    If_Then_Else_ : ∀ {c cₑ t tₑ e eₑ} -> Erasureᶜ l c cₑ -> Erasureᶜ l t tₑ -> Erasureᶜ l e eₑ ->
                    Erasureᶜ l (If c Then t Else e) (If cₑ Then tₑ Else eₑ)

    _>>=_ : ∀ {m mₑ k kₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l k kₑ -> Erasureᶜ l (m >>= k) (mₑ >>= kₑ)

    Catch : ∀ {m mₑ h hₑ} -> Erasureᶜ l m mₑ -> Erasureᶜ l h hₑ -> Erasureᶜ l (Catch m h) (Catch mₑ hₑ)

    unlabel : ∀ {t tₑ} -> Erasureᶜ l t tₑ -> Erasureᶜ l (unlabel t) (unlabel tₑ)


  data ErasureEnvᶜ (l : Label) : ∀ {n} -> Env n -> Env n -> Set where
    [] : ErasureEnvᶜ l [] []
    _∷_ : ∀ {n c cₑ} {Γ Γₑ : Env n} -> Erasureᶜ l c cₑ -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l (c ∷ Γ) (cₑ ∷ Γₑ)

-- Sound
εᶜ-Erasureᶜ : ∀ {{l}} -> (c : CTerm) -> Erasureᶜ l c (εᶜ l c)
εᶜ-env-ErasureEnvᶜ : ∀ {l n} -> (Γ : Env n) -> ErasureEnvᶜ l Γ (εᶜ-env l Γ)

εᶜ-Erasureᶜ (Γ , x) = (εᶜ-env-ErasureEnvᶜ Γ) , (ε-Erasure x)
εᶜ-Erasureᶜ (f $ x) = εᶜ-Erasureᶜ f $ εᶜ-Erasureᶜ x
εᶜ-Erasureᶜ (If c Then c₁ Else c₂) = If εᶜ-Erasureᶜ c Then εᶜ-Erasureᶜ c₁ Else εᶜ-Erasureᶜ c₂
εᶜ-Erasureᶜ (c >>= c₁) = εᶜ-Erasureᶜ c >>= εᶜ-Erasureᶜ c₁
εᶜ-Erasureᶜ (Catch c c₁) = Catch (εᶜ-Erasureᶜ c) (εᶜ-Erasureᶜ c₁)
εᶜ-Erasureᶜ (unlabel c) = unlabel (εᶜ-Erasureᶜ c)

εᶜ-env-ErasureEnvᶜ [] = []
εᶜ-env-ErasureEnvᶜ (x ∷ Γ) = (εᶜ-Erasureᶜ x) ∷ εᶜ-env-ErasureEnvᶜ Γ

-- Complete
Erasureᶜ-εᶜ : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> εᶜ l c ≡ cₑ
ErasureEnvᶜ-εᶜ-env : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> εᶜ-env l Γ ≡ Γₑ

Erasureᶜ-εᶜ (Γ , e) rewrite
  ErasureEnvᶜ-εᶜ-env Γ | Erasure-ε e = refl
Erasureᶜ-εᶜ (f $ x) rewrite
  Erasureᶜ-εᶜ f | Erasureᶜ-εᶜ x = refl
Erasureᶜ-εᶜ (If c Then t Else e) rewrite
  Erasureᶜ-εᶜ c | Erasureᶜ-εᶜ t | Erasureᶜ-εᶜ e = refl
Erasureᶜ-εᶜ (m >>= k) rewrite
  Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ k = refl
Erasureᶜ-εᶜ (Catch m h) rewrite
  Erasureᶜ-εᶜ m | Erasureᶜ-εᶜ h = refl
Erasureᶜ-εᶜ (unlabel e) rewrite
  Erasureᶜ-εᶜ e = refl

ErasureEnvᶜ-εᶜ-env [] = refl
ErasureEnvᶜ-εᶜ-env (e ∷ Γ) rewrite
  Erasureᶜ-εᶜ e | ErasureEnvᶜ-εᶜ-env Γ = refl

Erasureᶜ-idem : ∀ {l} {c cₑ : CTerm} -> Erasureᶜ l c cₑ -> Erasureᶜ l cₑ cₑ 
ErasureEnvᶜ-idem : ∀ {l n} {Γ Γₑ : Env n} -> ErasureEnvᶜ l Γ Γₑ -> ErasureEnvᶜ l Γₑ Γₑ 

Erasureᶜ-idem (Γ , c) = (ErasureEnvᶜ-idem Γ) , (Erasure-idem c)
Erasureᶜ-idem (f $ x) = Erasureᶜ-idem f $ Erasureᶜ-idem x
Erasureᶜ-idem (If c Then t Else e) = If Erasureᶜ-idem c Then Erasureᶜ-idem t Else Erasureᶜ-idem e
Erasureᶜ-idem (c >>= c₁) = Erasureᶜ-idem c >>= Erasureᶜ-idem c₁
Erasureᶜ-idem (Catch c c₁) = Catch (Erasureᶜ-idem c) (Erasureᶜ-idem c₁)
Erasureᶜ-idem (unlabel c) = unlabel (Erasureᶜ-idem c)

ErasureEnvᶜ-idem [] = []
ErasureEnvᶜ-idem (x ∷ Γ) = (Erasureᶜ-idem x) ∷ (ErasureEnvᶜ-idem Γ)

--------------------------------------------------------------------------------
-- Going through the graph of the erasure function we can prove the original
-- idempotence lemma.

-- ε is idempotent
ε-idem : ∀ {l n} -> (t : Term n) -> ε l t ≡ ε l (ε l t)
ε-idem t with Erasure-idem (ε-Erasure t)
... | r = sym (Erasure-ε r)

-- εᶜ is idempotent
εᶜ-idem : ∀ {l} -> (c : CTerm) -> εᶜ l c ≡ εᶜ l (εᶜ l c)
εᶜ-idem c with Erasureᶜ-idem (εᶜ-Erasureᶜ c) 
... | r = sym (Erasureᶜ-εᶜ r)

-- εᶜ-env is idempotent
εᶜ-env-idem : ∀ {l n} -> (Γ : Env n) -> εᶜ-env l Γ ≡ εᶜ-env l (εᶜ-env l Γ)
εᶜ-env-idem Γ with ErasureEnvᶜ-idem (εᶜ-env-ErasureEnvᶜ Γ)
... | r = sym (ErasureEnvᶜ-εᶜ-env r)

--------------------------------------------------------------------------------
