open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality
open import Concurrent.Security.Erasure

module Concurrent.Security.NonInterference
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (ε-state : Label -> State -> State) -- Erasure function of the scheduler state
  (_≈ᵀ-⟨_⟩_ : State -> Label -> State -> Set)
  (_≈ˢ-⟨_,_,_⟩_ : State -> ℕ -> Label -> ℕ -> State -> Set)
  (offset₁ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂ -> ℕ)
  (offset₂ : {lₐ : Label} {s₁ s₂ : State} -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂ -> ℕ)
  (align : ∀ {lₐ s₁ s₂} -> (eq : s₁ ≈ᵀ-⟨ lₐ ⟩ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq , lₐ , offset₂ eq ⟩ s₂)
  (forget : ∀ {lₐ s₁ s₂ n m} -> s₁ ≈ˢ-⟨ n , lₐ , m ⟩ s₂ -> s₁ ≈ᵀ-⟨ lₐ ⟩ s₂)
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

open import Data.Product hiding (_,_)
import Data.Product as P

◅-≡ : ∀ {l n} {t₁ t₂ : Thread l} {ts₁ ts₂ : Pool l n} ->  _≡_ {A = Pool l (suc n)}(_◅_ {n = n} t₁ ts₁) (_◅_ {n = n} t₂ ts₂) -> (t₁ ≡ t₂) × (ts₁ ≡ ts₂)
◅-≡ refl = refl P., refl

≡-≌ᴾ : ∀ {l lₐ n} {p₁ : Pool l n} {p₂ : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> εᵗ x p₁ ≡ εᵗ x p₂ -> p₁ ≌ᴾ-⟨ lₐ ⟩ p₂
≡-≌ᴾ {p₁ = []} {[]} x eq = nil
≡-≌ᴾ {p₁ = []} {∙} (yes p) ()
≡-≌ᴾ {p₁ = []} {∙} (no ¬p) refl = high ¬p
≡-≌ᴾ {l} {lₐ} {p₁ = x ◅ p₁} {x₁ ◅ p₂} (yes p) eq with ◅-≡ eq
... | eq₁ P., eq₂ rewrite ε-Mac-extensional (yes p) (l ⊑? lₐ) x | ε-Mac-extensional (yes p) (l ⊑? lₐ) x₁ = cons p (ε-≡ eq₁) (≡-≌ᴾ (yes p) eq₂)
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
◅ᵖ-≡ⁿᵘ refl = refl P., refl

◅ᵖ-≡ : ∀ {l n ls} {u₁ u₂ : Unique l ls} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n} -> _≡_ {A = Pools (l ∷ ls)} (_◅_ {{u = u₁}} ts₁ ps₁) (_◅_ {{u = u₂}} ts₂ ps₂)
            -> ts₁ ≡ ts₂ × ps₁ ≡ ps₂
◅ᵖ-≡ refl = refl P., refl


≡-≈ᴾ : ∀ {lₐ ls} {ps₁ ps₂ : Pools ls} -> εᵖ lₐ ps₁ ≡ εᵖ lₐ ps₂ -> ps₁ ≈ᴾ ps₂
≡-≈ᴾ {ps₁ = []} {[]} eq = []
≡-≈ᴾ {lₐ} {ps₁ = _◅_ {l = l} x ps₁} {x₁ ◅ ps₂} eq with ◅ᵖ-≡ⁿᵘ eq
... | eq₁ P., eq₂ rewrite eq₁ | eq₂ with ◅ᵖ-≡ eq
... | eq₃ P., eq₄ = ≡-≌ᴾ (l ⊑? lₐ) eq₃ ∷ ≡-≈ᴾ eq₄

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

-- TODO I might need to use structural low-equivalence also for stores

simulation↪ : ∀ {ls l n} {{lₐ : Label}} {g₁ g₂ g₁' g₂' : Global ls} ->
                    g₁ ≈ᵍ-⟨ lₐ ⟩ g₂ ->
                    l , n ⊢ g₁ ↪ g₁' ->
                    l , n ⊢ g₂ ↪ g₂' ->
                    g₁' ≈ᵍ-⟨ lₐ ⟩ g₂'
simulation↪ {{lₐ}} p s₁ s₂ = lift-≈ᵍ (aux (unlift-≈ᵍ p) (εᵍ-dist lₐ s₁) (εᵍ-dist lₐ s₂))
  where aux : ∀ {ls l n} {t₁ t₂ t₃ t₄ : Global ls} -> t₁ ≡ t₂ -> l , n ⊢ t₁ ↪ t₃ -> l , n ⊢ t₂ ↪ t₄ -> t₃ ≡ t₄
        aux refl s₁ s₂ = determinism↪ s₁ s₂

open import Sequential.Semantics

high-step : ∀ {lₐ l ls n} {g₁ g₂ : Global ls} -> ¬ (l ⊑ lₐ) -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂
high-step ¬p (step r₁ r₂ st sc w₁ w₂) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (ε-write-≡ ¬p w₂) ⟩
high-step ¬p (fork r₁ r₂ r₃ st sc  w₁ w₂ w₃)
  = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (trans (ε-write-≡ ¬p w₂) (ε-write-≡ (trans-⋢ (fork-⊑ st) ¬p) w₃)) ⟩
high-step ¬p (hole r sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (skip r₁ r₂ b sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (exit r₁ r₂ isV sc) = ⟨ ≡-≈ᵀ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩

read-≈ : ∀ {l lₐ i n m} {ts₁ : Pool l n} {ts₂ : Pool l m} {t₁ t₂ : Thread l} -> l ⊑ lₐ -> ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂ -> ts₁ [ i ]ᵗ= t₁ -> ts₂ [ i ]ᵗ= t₂ -> t₁ ≈-⟨ lₐ ⟩ t₂
read-≈ p (high ¬p) a b = ⊥-elim (¬p p)
read-≈ p nil () b
read-≈ p (cons x x₁ x₂) Here Here = x₁
read-≈ p (cons x x₁ x₂) (There a) (There b) = read-≈ x x₂ a b
read-≈ p bullet () b

-- TODO I think we can combine this and getPool in a unique lemma
read-≌ᴾ : ∀ {l lₐ n n' ls} {ps ps' : Pools ls} {ts : Pool l n} {ts' : Pool l n'} -> ps ≈ᴾ-⟨ lₐ ⟩ ps' -> ps [ l ]= ts -> ps' [ l ]= ts' -> ts ≌ᴾ-⟨ lₐ ⟩ ts' 
read-≌ᴾ (x ∷ x₁) Here Here = x
read-≌ᴾ (x ∷ x₁) Here (There {u = u} r₂) = ⊥-elim (not-unique u (read-∈ r₂))
read-≌ᴾ (x ∷ x₁) (There {u = u} r₁) Here = ⊥-elim (not-unique u (read-∈ r₁))
read-≌ᴾ (x ∷ x₁) (There r₁) (There r₂) = read-≌ᴾ x₁ r₁ r₂
read-≌ᴾ [] () r₂

read-≈' : ∀ {l lₐ i n m} {ts₁ : Pool l n} {ts₂ : Pool l m} {t₁ : Thread l} -> l ⊑ lₐ -> ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂ -> ts₁ [ i ]ᵗ= t₁ -> ∃ λ t₂ -> (t₁ ≈-⟨ lₐ ⟩ t₂) × (ts₂ [ i ]ᵗ= t₂)
read-≈' p (high ¬p) r = ⊥-elim (¬p p)
read-≈' p nil ()
read-≈' p (cons x x₁ x₂) Here = _ P., (x₁ P., Here)
read-≈' p (cons x x₁ x₂) (There r) with read-≈' p x₂ r
read-≈' p (cons x x₁ x₂) (There r) | t P., eq P., q  = t P., (eq P., (There q))
read-≈' p bullet ()

data HasPool {ls : List Label} (l : Label) (ps : Pools ls) : Set where
  HP : ∀ {n} {ts : Pool l n} -> ps [ l ]= ts -> HasPool l ps

getPool : ∀ {l ls} -> l ∈ ls -> (ps : Pools ls) -> HasPool l ps
getPool Here (ts ◅ ps) = HP Here 
getPool (There r) (ts ◅ ps) with getPool r ps
getPool (There r) (ts₁ ◅ ps) | HP x = HP (There x)

open import Concurrent.Security.Scheduler State _⟶_↑_ ε-state _≈ᵀ-⟨_⟩_ _≈ˢ-⟨_,_,_⟩_ offset₁ offset₂ align

-- This lemma needs to be proved.
-- It gets called when the two configurations are finally aligned (run the same low step).
-- 
-- postulate lemma₃ : ∀ {ls l lₐ s₂' n e} {g₁ g₂ g₁' : Global ls} ->
--                      let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
--                          ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂
--                          ⟨ s₁' , Σ₁' , ps₁' ⟩ = g₁' in
--                      g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' -> s₁' ⟶ s₂' ↑ ⟪ l , n , e ⟫  ->
--                      l , n ⊢ g₁ ↪ g₂ -> ∃ (λ Σ₂' -> ∃ (λ ps₂' -> l , n ⊢ g₁' ↪ ⟨ s₂' , Σ₂' , ps₂' ⟩ ×  g₂ ≈ᵍ-⟨ lₐ ⟩ ⟨ s₂' , Σ₂' , ps₂' ⟩)) 

-- How can we enforce that the scheduler chooses a valid thread id?
-- Here I need something more refined e.g. ps[ l ][ n ]= t
-- Maybe I should merge directly ps[ l ]= ts and ts [ n ]= t in a single data-type
postulate threadToRun : ∀ {ls} (l : Label) (n : ℕ) (g₁ : Global ls) -> Thread l

-- TODO here I definitevely need the proof ps [ l ][ n ]= t where ps = pools g₁
-- This shouldn't be too bad. Depending on the status and the reduction only one rule apply!
-- postulate nextStep : ∀ {ls l } {Σ : Store ls} {t : Thread l} -> (n : ℕ) -> PStatus Σ t -> (g₁ : Global ls) -> ∃ λ g₂ -> l , n ⊢ g₁ ↪ g₂
postulate nextEvent : ∀ {ls l } {Σ : Store ls} {t : Thread l} -> PStatus Σ t -> Event

data NI {ls} (lₐ : Label) (g₁' g₂ : Global ls) : Set where
  isNI : ∀ {g₂'} -> g₁' ↪⋆ g₂' -> g₂ ≈ᵍ-⟨ lₐ ⟩ g₂' -> NI lₐ g₁' g₂

postulate square : ∀ {l n e ls s₂' lₐ} {g₁ g₂ g₁' : Global ls} ->
                                let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
                                    ⟨ s₁' , Σ₁' , ps₁' ⟩ = g₁'
                                    ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂ in s₁' ⟶ s₂' ↑ ⟪ l , n , e ⟫ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ ->
                                ∃ (λ Σ₂' -> (∃ (λ ps₂' -> let g₂' = ⟨ s₂' , Σ₂' , ps₂' ⟩ in (l , n ⊢ g₁' ↪ g₂') × (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂'))))


-- Here we need some proof that ps [ h ] [ n ] does actually generate e
postulate scheduler2global : ∀ {ls h n e} {g₁ g₂ : Global ls} ->
                             let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
                                 ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂ in s₁ ⟶ s₂ ↑ ⟪ h , n , e ⟫ -> h , n ⊢ g₁ ↪ g₂

lemma₂ : ∀ {l n lₐ n₁ n₂ ls} {g₁ g₂ g₁' : Global ls} -> l ⊑ lₐ -> l , n ⊢ g₁ ↪ g₂ -> (state g₁) ≈ˢ-⟨ n₁ , lₐ , n₂ ⟩ (state g₁') -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> NI lₐ g₁' g₂
lemma₂ {n₂ = zero} p s eq₁ eq₂ with getSchedulerStep s
... | e P., sc with aligned p sc eq₁
... | s₂' P., sc' P., eq₁' with square sc' eq₂ s
... | Σ₂' P., ps₂' P., s' P., eq' = isNI (s' ∷ []) eq'
                         
lemma₂ {n₂ = suc n₂} p s eq₁ ⟨ a , b , c ⟩ with highˢ eq₁
... | h P., n P., k with k Step -- An Example. Here the event should come from the actual thread that should run
... | high ¬p s' eq₁' with lemma₂ p s eq₁' ⟨ forget eq₁' , b , c ⟩ -- Yeeee it is terminating!!! :-)
... | isNI ss eq₂' with scheduler2global s'
... | s'' with high-step ¬p s''
... | r = isNI ( s'' ∷ ss) (trans-≈ᵍ eq₂' refl-≈ᵍ)

lemma : ∀ {l n ls lₐ} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ lₐ) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂' )
lemma {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩ } (yes p) ⟨ eq₁ , eq₂ , eq₃ ⟩ s with getSchedulerStep s
... | e P., sc with lemma₂ p s (align eq₁) ⟨ eq₁ , eq₂ , eq₃ ⟩
... | isNI ss eq'  = _ Σ., (eq' Σ., ss)
lemma {g₁' = g₁'} (no ¬p) eq s = g₁' P., trans-≈ᵍ (sym-≈ᵍ (high-step ¬p s)) eq P., []

--  with getPool (read-∈ r₁) ps₁'
-- ... | HP r₁' with read-≈' p (read-≌ᴾ eq₃ r₁ r₁') r₂
-- ... | t , eq' , r₂' with scheduler-ni sc eq₁
-- with 
-- non-interference-scheduler p sc eq₁
-- ... | s₂' , eq₁' , sc' = _ , (⟨ eq₁' , eq₂ , eq₃ ⟩ , ((exit r₁' r₂' (valueᴸ p isV eq') sc') ∷ []))

-- -- non-interference : ∀ {ls l n} {g₁ g₁' g₂ : Global ls} -> (lₐ : Label) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × (l , n ⊢ g₁' ↪ g₂'))
-- -- non-interference {g₁ = g₁} {g₁'} {g₂} lₐ (εᵍ-≡ x) s with εᵍ-dist lₐ s
-- -- ... | r = {!!} , ({!!} , {!r!})

-- -- TODO prove non-interference for multiple steps.
