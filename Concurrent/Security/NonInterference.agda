open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure
open import Data.Product

module Concurrent.Security.NonInterference
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε-state : Label -> State -> State) -- Erasure function of the scheduler state
  (_≈ᵀ-⟨_⟩_ : State -> Label -> State -> Set)
  (_≈ˢ-⟨_~_~_⟩_ : State -> ℕ -> Label -> ℕ -> State -> Set)
  (offset₁ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂ -> ℕ)
  (offset₂ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂ -> ℕ)
  (align : ∀ {lₐ s₁ s₂} -> (eq : s₁ ≈ᵀ-⟨ lₐ ⟩ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq ~ lₐ ~ offset₂ eq ⟩ s₂)
  (forget : ∀ {lₐ s₁ s₂ n m} -> s₁ ≈ˢ-⟨ n ~ lₐ ~ m ⟩ s₂ -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂)
  (ε-sch-dist : ∀ {s₁ s₂ l lₐ} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ⟶ (ε-state lₐ s₂) ↑ (εᴹ x m))
  -- TODO as long as ≈ is isomorphic to ≡ we can just stick to one of them!
  (ε-sch-≡ : ∀ {s₁ s₂ l lₐ} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ≡ (ε-state lₐ s₂))



  (deterministic-scheduler : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃ )
  
  where


open import Concurrent.Determinism State _⟶_↑_ deterministic-scheduler
open import Concurrent.Security.Distributivity State _⟶_↑_ ε-state ε-sch-dist ε-sch-≡
open import Concurrent.Semantics State _⟶_↑_
open import Concurrent.Calculus
open import Concurrent.Security.Erasure renaming (ε-pools to εᵖ)

open import Sequential.Security.Distributivity renaming (εˢ-≡ to high-stepˢ) hiding (εᵖ)
open import Sequential.Security.NonInterference hiding (_≈ᵖ_ ; non-interference)

open Global

--------------------------------------------------------------------------------
-- TODO find good name/symbols for structural low-equivalence

mutual
  data _≌ᴾ_ {lₐ : Label} {l : Label} : ∀ {n m} -> Pool l n -> Pool l m -> Set where
    high : ∀ {n m} {p₁ : Pool l n} {p₂ : Pool l m} -> (¬p : ¬ (l ⊑ lₐ)) -> p₁ ≌ᴾ p₂
    nil : [] ≌ᴾ [] 
    cons : ∀ {n m} {p₁ : Pool l n} {p₂ : Pool l m} {t₁ t₂ : Thread l} -> l ⊑ lₐ -> t₁ ≈-⟨ lₐ ⟩ t₂ -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ -> (t₁ ◅ p₁) ≌ᴾ (t₂ ◅ p₂)
    bullet : ∀ {n m} -> (∙ {n = n}) ≌ᴾ (∙ {n = m})

  _≌ᴾ-⟨_⟩_ : ∀ {l n m} -> Pool l n -> Label -> Pool l m -> Set
  p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ = _≌ᴾ_ {lₐ} p₁ p₂ 

-- Is this equivalent to the definition of low-equivalence?
≌ᴾ-≡ : ∀ {l lₐ n} {p₁ : Pool l n} {p₂ : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂ -> εᵗ x p₁ ≡ εᵗ x p₂
≌ᴾ-≡ (yes p) (high ¬p) = ⊥-elim (¬p p)
≌ᴾ-≡ (no ¬p) (high ¬p₁) = refl
≌ᴾ-≡ x nil = refl
≌ᴾ-≡ {l} {lₐ} (yes p) (cons {t₁ = t₁}  {t₂ = t₂} x₁ (ε-≡ eq) x₃)
  rewrite ≌ᴾ-≡ (yes p) x₃ | ε-Mac-extensional (yes p) (l ⊑? lₐ) t₁ | ε-Mac-extensional (yes p) (l ⊑? lₐ) t₂ | eq = refl
≌ᴾ-≡ (no ¬p) (cons x₁ x₂ x₃) = refl
≌ᴾ-≡ x bullet = refl

◅-≡ : ∀ {l n} {t₁ t₂ : Thread l} {ts₁ ts₂ : Pool l n} ->  _≡_ {A = Pool l (suc n)}(_◅_ {n = n} t₁ ts₁) (_◅_ {n = n} t₂ ts₂) -> (t₁ ≡ t₂) × (ts₁ ≡ ts₂)
◅-≡ refl = refl , refl

≡-≌ᴾ : ∀ {l lₐ n} {p₁ : Pool l n} {p₂ : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> εᵗ x p₁ ≡ εᵗ x p₂ -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂
≡-≌ᴾ {p₁ = []} {[]} x eq = nil
≡-≌ᴾ {p₁ = []} {∙} (yes p) ()
≡-≌ᴾ {p₁ = []} {∙} (no ¬p) refl = high ¬p
≡-≌ᴾ {l} {lₐ} {p₁ = x ◅ p₁} {x₁ ◅ p₂} (yes p) eq with ◅-≡ eq
... | eq₁ , eq₂ rewrite ε-Mac-extensional (yes p) (l ⊑? lₐ) x | ε-Mac-extensional (yes p) (l ⊑? lₐ) x₁ = cons p (ε-≡ eq₁) (≡-≌ᴾ (yes p) eq₂)
≡-≌ᴾ {p₁ = x ◅ p₁} {x₁ ◅ p₂} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = x ◅ p₁} {∙} (yes p) ()
≡-≌ᴾ {p₁ = x ◅ p₁} {∙} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {[]} (yes p) ()
≡-≌ᴾ {p₁ = ∙} {[]} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {x ◅ p₂} (yes p) ()
≡-≌ᴾ {p₁ = ∙} {x ◅ p₂} (no ¬p) eq = high ¬p
≡-≌ᴾ {p₁ = ∙} {∙} x eq = bullet

--------------------------------------------------------------------------------
-- (ps₁ ps₂ : Pools ls)

mutual 
  data _≈ᴾ_ {{lₐ : Label}} : ∀ {ls} -> Pools ls -> Pools ls -> Set where
    _∷_ : ∀ {ls l n} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n} {u : Unique l ls} -> ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂ -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂ -> (ts₁ ◅ ps₁) ≈ᴾ (ts₂ ◅  ps₂)
    [] : [] ≈ᴾ []

  _≈ᴾ-⟨_⟩_ : ∀ {ls} -> Pools ls -> Label -> Pools ls -> Set
  p₁ ≈ᴾ-⟨ lₐ ⟩ p₂ = _≈ᴾ_ {{lₐ}} p₁ p₂ 

◅ᵖ-≡ⁿᵘ : ∀ {l n m ls} {u₁ u₂ : Unique l ls} {ps₁ ps₂ : Pools ls} {ts₁ : Pool l n} {ts₂ : Pool l m} -> _≡_ {A = Pools (l ∷ ls)} (_◅_ {{u = u₁}} ts₁ ps₁) (_◅_ {{u = u₂}} ts₂ ps₂)
            -> n ≡ m × u₁ ≡ u₂
◅ᵖ-≡ⁿᵘ refl = refl , refl

◅ᵖ-≡ : ∀ {l n ls} {u₁ u₂ : Unique l ls} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n} -> _≡_ {A = Pools (l ∷ ls)} (_◅_ {{u = u₁}} ts₁ ps₁) (_◅_ {{u = u₂}} ts₂ ps₂)
            -> ts₁ ≡ ts₂ × ps₁ ≡ ps₂
◅ᵖ-≡ refl = refl , refl


≡-≈ᴾ : ∀ {lₐ ls} {ps₁ ps₂ : Pools ls} -> εᵖ lₐ ps₁ ≡ εᵖ lₐ ps₂ -> ps₁ ≈ᴾ ps₂
≡-≈ᴾ {ps₁ = []} {[]} eq = []
≡-≈ᴾ {lₐ} {ps₁ = _◅_ {l = l} x ps₁} {x₁ ◅ ps₂} eq with ◅ᵖ-≡ⁿᵘ eq
... | eq₁ , eq₂ rewrite eq₁ | eq₂ with ◅ᵖ-≡ eq
... | eq₃ , eq₄ = ≡-≌ᴾ (l ⊑? lₐ) eq₃ ∷ ≡-≈ᴾ eq₄

≈ᴾ-≡ : ∀ {lₐ ls} {ps₁ ps₂ : Pools ls} -> ps₁ ≈ᴾ ps₂ -> εᵖ lₐ ps₁ ≡ εᵖ lₐ ps₂
≈ᴾ-≡ {lₐ} (_∷_ {l = l} ts ps) rewrite ≌ᴾ-≡ (l ⊑? lₐ) ts | ≈ᴾ-≡ ps = refl
≈ᴾ-≡ [] = refl

sym-≈ᴾ : ∀ {ls lₐ} {p₁ p₂ : Pools ls} -> p₁ ≈ᴾ p₂ -> p₂ ≈ᴾ p₁
sym-≈ᴾ eq = ≡-≈ᴾ (sym (≈ᴾ-≡ eq))

trans-≈ᴾ : ∀ {ls lₐ} {p₁ p₂ p₃ : Pools ls} -> p₁ ≈ᴾ p₂ -> p₂ ≈ᴾ p₃ -> p₁ ≈ᴾ p₃
trans-≈ᴾ a b = ≡-≈ᴾ (trans (≈ᴾ-≡ a) (≈ᴾ-≡ b))

--------------------------------------------------------------------------------

-- Since we cannot really do anything special with this, it would be best to define this as a synonym
-- data _≈ᵀ_ {{lₐ : Label}} (s₁ s₂ : State) : Set where
--   ε-≡ : ε-state lₐ s₁ ≡ ε-state lₐ s₂ -> s₁ ≈ᵀ s₂


_≈ᵀ_ : {{lₐ : Label}} (s₁ s₂ : State) -> Set
_≈ᵀ_ {{lₐ}} s₁ s₂ = s₁ ≈ᵀ-⟨ lₐ ⟩ s₂

-- We need ≈ᵀ to be an isomoprphic to the ε based defintion
-- Then we can even prove that it is an equivalence relation

postulate ≈ᵀ-≡ : ∀ {lₐ s₁ s₂} -> s₁ ≈ᵀ s₂ -> ε-state lₐ s₁ ≡ ε-state lₐ s₂
postulate ≡-≈ᵀ : ∀ {lₐ s₁ s₂} -> ε-state lₐ s₁ ≡ ε-state lₐ s₂ -> s₁ ≈ᵀ s₂

postulate sym-≈ᵀ : ∀ {lₐ} {s₁ s₂ : State} -> s₁ ≈ᵀ s₂ -> s₂ ≈ᵀ s₁
-- sym-≈ᵀ x = sym x

postulate trans-≈ᵀ : ∀ {lₐ} {s₁ s₂ s₃ : State} -> s₁ ≈ᵀ s₂ -> s₂ ≈ᵀ s₃ -> s₁ ≈ᵀ s₃
-- trans-≈ᵀ x y = trans x y


--------------------------------------------------------------------------------

-- Global l-equivalence
data _≈ᵍ_ {{lₐ : Label}} {ls : List Label} (g₁ g₂ : Global ls) : Set where
  ⟨_,_,_⟩ : state g₁ ≈ᵀ  state g₂ -> storeᵍ g₁ ≈ˢ storeᵍ g₂ -> pools g₁ ≈ᴾ pools g₂ -> g₁ ≈ᵍ g₂

sym-≈ᵍ : ∀ {ls lₐ} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ g₂ -> g₂ ≈ᵍ g₁
sym-≈ᵍ ⟨ x , y , z ⟩ = ⟨ (sym-≈ᵀ x) , (sym-≈ˢ y) , (sym-≈ᴾ z) ⟩

trans-≈ᵍ : ∀ {ls lₐ} {g₁ g₂ g₃ : Global ls} -> g₁ ≈ᵍ g₂ -> g₂ ≈ᵍ g₃ -> g₁ ≈ᵍ g₃
trans-≈ᵍ ⟨ x₁ , y₁ , z₁ ⟩ ⟨ x₂ , y₂ , z₂ ⟩ = ⟨ trans-≈ᵀ x₁ x₂ , trans-≈ˢ y₁ y₂ , trans-≈ᴾ z₁ z₂ ⟩

postulate refl-≈ᵍ : ∀ {lₐ ls} {g : Global ls}  -> g ≈ᵍ g

--- Syntactic sugar to avoid ambiguities
_≈ᵍ-⟨_⟩_ : ∀ {ls} -> Global ls -> Label -> Global ls -> Set
g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ = g₁ ≈ᵍ g₂
 
unlift-≈ᵍ : ∀ {lₐ ls} {g₁ g₂ : Global ls} -> g₁ ≈ᵍ g₂ -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂
unlift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} ⟨ x , εˢ-≡ y , z ⟩
  rewrite ≈ᵀ-≡ x | y | ≈ᴾ-≡ z =  refl

lift-≈ᵍ :  ∀ {lₐ ls} {g₁ g₂ : Global ls}  -> εᵍ lₐ g₁ ≡ εᵍ lₐ g₂ -> g₁ ≈ᵍ g₂
lift-≈ᵍ {g₁ = ⟨ state , storeᵍ , pools ⟩} {⟨ state₁ , storeᵍ₁ , pools₁ ⟩} eq = ⟨ ≡-≈ᵀ (state-≡ eq) , εˢ-≡ (storeᵍ-≡ eq) , ≡-≈ᴾ (pools-≡ eq) ⟩

--------------------------------------------------------------------------------

-- Progress insensitive non-interference
simulation↪ : ∀ {ls l n} {{lₐ : Label}} {g₁ g₂ g₁' g₂' : Global ls} ->
                    g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ ->
                    l , n ⊢ g₁ ↪ g₁' ->
                    l , n ⊢ g₂ ↪ g₂' ->
                    g₁' ≈ᵍ-⟨ lₐ ⟩ g₂'
simulation↪ {{lₐ}} p s₁ s₂ = lift-≈ᵍ (aux (unlift-≈ᵍ p) (εᵍ-dist lₐ s₁) (εᵍ-dist lₐ s₂))
  where aux : ∀ {ls l n} {t₁ t₂ t₃ t₄ : Global ls} -> t₁ ≡ t₂ -> l , n ⊢ t₁ ↪ t₃ -> l , n ⊢ t₂ ↪ t₄ -> t₃ ≡ t₄
        aux refl s₁ s₂ = determinism↪ s₁ s₂

--------------------------------------------------------------------------------

open import Sequential.Semantics

high-step : ∀ {lₐ l ls n} {g₁ g₂ : Global ls} -> ¬ (l ⊑ lₐ) -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂
high-step ¬p (step r st sc w) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (ε-updateᵖ-≡ ¬p w) ⟩
high-step ¬p (fork r₁ r₂ st sc  w₁ w₂)
  = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (trans (ε-updateᵖ-≡ ¬p w₁) (ε-updateᵗ-≡ (trans-⋢ (fork-⊑ st) ¬p) w₂)) ⟩
high-step ¬p (hole r st sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (skip r b sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (exit r isV sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩

read-≌ᴾ : ∀ {l lₐ n n'} {t₁ : Thread l} {ts₁ ts₂ : Pool l n} -> l ⊑ lₐ -> ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂ -> LookupThread t₁ n' ts₁ -> ∃ (λ t₂ -> LookupThread t₂ n' ts₂ × t₁ ≈-⟨ lₐ ⟩ t₂)
read-≌ᴾ p (high ¬p) ∙ = ⊥-elim (¬p p)
read-≌ᴾ p bullet ∙ = ∙ , ∙ , ε-≡ refl
read-≌ᴾ p (high ¬p) Here = ⊥-elim (¬p p)
read-≌ᴾ p (cons p' eq _) Here = _ , Here , eq
read-≌ᴾ p (high ¬p) (There r) = ⊥-elim (¬p p)
read-≌ᴾ p (cons p' _ eq₁) (There r₁) with read-≌ᴾ p eq₁ r₁
... | t₂ , r₂ , eq₂ = t₂ , There r₂ , eq₂

read-≈ : ∀ {ls l lₐ n} {t₁ : Thread l} {ps₁ ps₂ : Pools ls} -> l ⊑ lₐ -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂ -> ps₁ [ l ][ n ]= t₁ -> ∃ (λ t₂ -> ps₂ [ l ][ n ]= t₂ × t₁ ≈-⟨ lₐ ⟩ t₂)
read-≈ p (eq₁ ∷ _) (Here r₁) with read-≌ᴾ p eq₁ r₁
... | t₂ , r₂ , eq₂ = t₂ , Here r₂ , eq₂
read-≈ p (_ ∷ eq₁) (There r₁)  with read-≈ p eq₁ r₁
... | t₂ , r₂ , eq' = t₂ , There r₂ , eq'

-- TODO USE CONSISTENT NAMES
open import Concurrent.Security.Scheduler State _⟶_↑_ ε-state _≈ᵀ-⟨_⟩_ _≈ˢ-⟨_~_~_⟩_

--------------------------------------------------------------------------------

data NI {ls} (lₐ : Label) (g₁' g₂ : Global ls) : Set where
  isNI : ∀ {g₂'} -> g₁' ↪⋆ g₂' -> g₂ ≈ᵍ-⟨ lₐ ⟩ g₂' -> NI lₐ g₁' g₂

-- I need to show that low-equivalent terms have the same status (Stuck, Value, Redex)
-- and in the Redex case that they generate the same event! 

-- TODO I don't have to do this by induction on the global step, but on the event of the scheduler.
-- 

postulate square : ∀ {l n e ls s₂' lₐ} {g₁ g₂ g₁' : Global ls} -> l ⊑ lₐ ->
                                let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
                                    ⟨ s₁' , Σ₁' , ps₁' ⟩ = g₁'
                                    ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂ in s₁' ⟶ s₂' ↑ ⟪ l , n , e ⟫ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ ->
                                ∃ (λ Σ₂' -> (∃ (λ ps₂' ->
                                  let g₂' = ⟨ s₂' , Σ₂' , ps₂' ⟩ in (l , n ⊢ g₁' ↪ g₂') × (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂'))))

data _≈ᵉ_ {lₐ : Label} {l} : Effect l -> Effect l -> Set where
  ∙ : ∙ ≈ᵉ ∙
  ∅ : ∅ ≈ᵉ ∅
  fork : ∀ {h} {t₁ t₂ : Thread h} -> l ⊑ lₐ -> t₁ ≈-⟨ lₐ ⟩ t₂ -> fork t₁ ≈ᵉ fork t₂
  nv : ∀ {e₁ e₂} -> ¬ (l ⊑ lₐ) -> e₁ ≈ᵉ e₂
  
_≈ᵉ-⟨_⟩_ : ∀ {l} -> Effect l -> Label -> Effect l -> Set
e₁ ≈ᵉ-⟨ lₐ ⟩ e₂ = _≈ᵉ_ {lₐ} e₁ e₂

≈ᵉ-≡ : ∀ {l lₐ} {e₁ e₂ : Effect l} -> (x : Dec (l ⊑ lₐ)) -> e₁ ≈ᵉ-⟨ lₐ ⟩ e₂ -> εᵉ x e₁ ≡ εᵉ x e₂
≈ᵉ-≡ (yes p) ∙ = refl
≈ᵉ-≡ (yes p) ∅ = refl
≈ᵉ-≡ (yes p) (fork x (ε-≡ eq)) rewrite eq = refl
≈ᵉ-≡ (yes p) (nv x) = ⊥-elim (x p)
≈ᵉ-≡ (no ¬p) ∙ = refl
≈ᵉ-≡ (no ¬p) ∅ = refl
≈ᵉ-≡ (no ¬p) (fork x x₁) = refl
≈ᵉ-≡ (no ¬p) (nv x) = refl

≡-≈ᵉ : ∀ {l lₐ} {e₁ e₂ : Effect l} -> (x : Dec (l ⊑ lₐ)) -> εᵉ x e₁ ≡ εᵉ x e₂ -> e₁ ≈ᵉ-⟨ lₐ ⟩ e₂
≡-≈ᵉ {e₁ = ∙} {∙} (yes p) eq = ∙
≡-≈ᵉ {e₁ = ∙} {∅} (yes p) ()
≡-≈ᵉ {e₁ = ∙} {fork x} (yes p) ()
≡-≈ᵉ {e₁ = ∅} {∙} (yes p) () 
≡-≈ᵉ {e₁ = ∅} {∅} (yes p) refl = ∅
≡-≈ᵉ {e₁ = ∅} {fork x} (yes p) ()
≡-≈ᵉ {e₁ = fork x} {∙} (yes p) ()
≡-≈ᵉ {e₁ = fork x} {∅} (yes p) ()
≡-≈ᵉ {e₁ = fork x} {fork x₁} (yes p) eq = {!!} -- TODO if we know p₁ ≈ p₂ we can conclude that the type is actually the same
≡-≈ᵉ (no ¬p) refl = nv ¬p

open import Sequential.Security.NonInterference

postulate same-event : ∀ {ls l lₐ e₁ e₂} {p₁ p₂ p₁' p₂' : Program ls (Mac l _)} -> l ⊑ lₐ -> p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ -> p₁ ⟼ p₂ ↑ e₁ -> p₁' ⟼ p₂' ↑ e₂ -> e₁ ≈ᵉ-⟨ lₐ ⟩ e₂

-- At the moment I am assuming that the scheduler state contains only valid thread id, that is
-- Ideally it should be: if the scheduler s₁ ⟶ s₂ ↑ (l , n , e) and g₁ = ⟨ s₁ , Σ₁ , ps₁ ⟩ then there is a thread at ps₁ [ l ][ n ],
-- however due to the mutual dependency we cannot retrieve s₁ ⟶ s₂ ↑ _ if we don't know the event e already.
-- postulate getScheduledThread : ∀ {ls l n s₂ e} (g₁ : Global ls) -> let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁ in s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> ∃ (λ t -> ps₁ [ l ][ n ]= t)
postulate getThread : ∀ {ls} (l : Label) (n : ℕ) (ps : Pools ls) -> ∃ (λ t -> ps [ l ][ n ]= t)

-- When a thread is forked we can find the corresponding thread pool.
postulate getPoolThread : ∀ {ls} (l : Label) (ps : Pools ls) -> ∃ (λ n -> Σ (Pool l n) (λ ts -> ps [ l ]= ts))

--------------------------------------------------------------------------------

-- Here we need some proof that ps [ h ] [ n ] does actually generate e
postulate scheduler2global : ∀ {ls h n e} {g₁ g₂ : Global ls} ->
                             let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
                                 ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂ in s₁ ⟶ s₂ ↑ ⟪ h , n , e ⟫ -> h , n ⊢ g₁ ↪ g₂

-- TODO move to semantics module?
-- If we can read from a pool, then we can write something to it
postulate writePool : ∀ {l n ls t₁ t₂} {ps₁ : Pools ls} -> ps₁ [ l ][ n ]= t₁ -> ∃ (λ ps₂ -> ps₂ ← ps₁ [ l ][ n ]≔ t₂)
postulate forkPool : ∀ {h n ls} {ps₁ : Pools ls} {ts : Pool h n} -> ps₁ [ h ]= ts -> (t : Thread h) -> ∃ (λ ps₂ -> ps₂ ← ps₁ [ h ]≔ (ts ▻ t))

-- Inner module defined to break mutual dependency between Security.Scheduler and specific scheduler modules (e.g. RoundRobin)

-- fork? never produces a • event
fork?≠∙ : ∀ {l h n} {tʰ :  Thread h} {p : l ⊑ h} -> fork? p tʰ n ≢ ∙
fork?≠∙ {tʰ = t} {p} with is∙? t
... | yes _ = λ ()
... | no _ = λ ()


module PS
    (highˢ : ∀ {s₁ s₁' s₂ l lₐ n e i j} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ lₐ ~ suc j ⟩ s₁' ->
                    ∃ λ h -> ∃ λ n -> (e' : Event h) -> e' ≢ ∙ -> HighStep lₐ h n e' s₁ s₂ s₁' i j)
    (aligned : ∀ {l lₐ n i e s₁ s₂ s₁'} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ lₐ ~ 0 ⟩ s₁' -> Aligned s₁ s₂ s₁' ⟪ l , n , e ⟫ lₐ)
  where

    low-step : ∀ {l n lₐ n₁ n₂ ls} {g₁ g₂ g₁' : Global ls} -> l ⊑ lₐ -> l , n ⊢ g₁ ↪ g₂ -> (state g₁) ≈ˢ-⟨ n₁ ~ lₐ ~ n₂ ⟩ (state g₁') -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> NI lₐ g₁' g₂
    -- The two configurations are aligned
    low-step {n₂ = zero} p s eq₁ eq₂ with aligned p (getSchedulerStep s) {!!} eq₁ -- This is my assumption
    ... | low sc' eq₁' with square p sc' eq₂ s
    ... | Σ₂' , ps₂' , s' , eq' = isNI (s' ∷ []) eq'                        

    -- The other global configuration performs a high step
    low-step {n₂ = suc n₂} {g₁ = g₁} {g₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ with highˢ p (getSchedulerStep gs) {!!} eq₁ -- IDEM
    ... | h , n , k with getThread h n ps₁'
    ... | t' , r' with programStatus Σ₁' t'

    -- Done Event
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | V isV with k Done (λ ())
    ... | high ¬p sc' eq₁' with low-step p gs eq₁' ⟨ forget eq₁' , b , c ⟩
    ... | isNI ss eq₂' = isNI ((exit r' isV sc') ∷ ss) eq₂'
    
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) with effectOf t' | stepWithEvent st

    -- Hole Event (absurd)
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) | ∙ | st' = {!!} -- Can be ruled out assuming ps[ l ][ n ]≠ ∙

    -- Step Event
    low-step {n₂ = suc n₂} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) | ∅ | st' with k Step (λ ())
    ... | high ¬p sc' eq₁' with writePool r'
    ... | ps₂' , w' with high-step ¬p (step r' st' sc' w')
    ... | eq'' with low-step p gs eq₁' (trans-≈ᵍ ⟨ a , b , c ⟩ eq'')
    ... | isNI {g₂'} ss eq₂' = isNI (step r' st' sc' w' ∷ ss) eq₂'

    -- Fork Event
    -- TODO here we need to assume that the label of the forked thread is in the pool.
    -- Then we can compute nʰ as the length of the corresponding thread pool.
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) | fork {hⁿ} tⁿ | st'
      with getPoolThread hⁿ ps₁'
    ... | nⁿ , tsⁿ , rⁿ with k (fork? (fork-⊑ st') tⁿ nⁿ) fork?≠∙
    ... | high ¬p sc' eq₁' with writePool r'
    ... | ps₂' , w' with forkPool rⁿ tⁿ
    ... | ps₃' , w'' with high-step ¬p (fork {{p = fork-⊑ st'}} r' rⁿ st' sc' w' {!w''!}) -- TODO fix order of writes
    ... | eq'' with low-step p gs eq₁' (trans-≈ᵍ ⟨ a , b , c ⟩ eq'')
    ... | isNI ss eq₂' = isNI (fork {{p = fork-⊑ st'}} r' rⁿ st' sc' w' {!w''!} ∷ ss) eq₂'

    -- NoStep Event
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | S isS with k NoStep (λ ())
    ... | high ¬p sc' eq₁' with low-step p gs eq₁' ⟨ forget eq₁' , b , c ⟩
    ... | isNI ss eq₂' = isNI ((skip r' isS sc') ∷ ss) eq₂'
    -- k Step (λ ())
    -- ... | high ¬p sc' eq₁' 
    -- ... | isNI ss eq₂' = isNI (scheduler2global sc' ∷ ss) eq₂' -- This is somehow suspicious ... why don't I need to use the fact that this is am high-step?
                                                               -- Because scheduler2global is overly simplifying! 

    -- TODO maybe use NI data-type for clarity
    ps-ni-dispatch : ∀ {l n ls lₐ} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ lₐ) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂' )
    ps-ni-dispatch {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩ } (yes p) ⟨ eq₁ , eq₂ , eq₃ ⟩ s with low-step p s (align eq₁) ⟨ eq₁ , eq₂ , eq₃ ⟩
    ... | isNI ss eq'  = _ Σ., (eq' Σ., ss)
    ps-ni-dispatch {g₁' = g₁'} (no ¬p) eq s = g₁' , trans-≈ᵍ (sym-≈ᵍ (high-step ¬p s)) eq , []

    -- TODO I will probably need to add the assumption ps [ l ][ n ] ≠ ∙
    progress-sensitive-ni : ∀ {l ls n} {g₁ g₁' g₂ : Global ls} -> (lₐ : Label) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂')
    progress-sensitive-ni {l} lₐ = ps-ni-dispatch (l ⊑? lₐ)


    -- TODO I will need the assumption that every thread is non ∙
    progress-sensitive-ni⋆ : ∀ {ls} {g₁ g₁' g₂ : Global ls} -> (lₐ : Label) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> g₁ ↪⋆ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂')
    progress-sensitive-ni⋆ lₐ eq [] = _ , (eq , [])
    progress-sensitive-ni⋆ lₐ eq (s ∷ ss) with progress-sensitive-ni lₐ eq s
    ... | g₂' , eq₂' , ss₂' with progress-sensitive-ni⋆ lₐ eq₂' ss
    ... | g₃' , eq₃' , ss₃' = g₃' , (eq₃' , ss₂' ++ˢ ss₃')
