open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality

module Concurrent.Determinism
  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (deterministic-scheduler : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃ ) where


open import Sequential.Determinism
open import Concurrent.Calculus
open import Data.List.All
open import Concurrent.Semantics State _⟶_↑_ 

read-∈ : ∀ {l ls n} {ts : Pool l n} {ps : Pools ls} -> ps [ l ]= ts -> l ∈ ls
read-∈ Here = Here
read-∈ (There p) = There (read-∈ p)

write-∈ : ∀ {l ls n} {ts : Pool l n} {ps₁ ps₂ : Pools ls} -> ps₂ ← ps₁ [ l ]≔ ts -> l ∈ ls
write-∈ Here = Here
write-∈ (There x) = There (write-∈ x)

stuck-no-redex : ∀ {ls l} {Σ₁ : Store ls} {t₁ : Thread l} -> Stuck Σ₁ t₁ -> Redex Σ₁ t₁ -> ⊥
stuck-no-redex (stuck x x₁) r = ⊥-elim (x r)

stuck-no-value : ∀ {l ls} {Σ : Store ls} {t : Thread l} -> Stuck Σ t -> IsValue t -> ⊥
stuck-no-value (stuck x x₁) isV = x₁ isV

single-event : ∀ {l ls τ} {t : Thread l} {p₁ p₂ p₃ : Program ls τ} -> p₁ ⟼ p₂ ↑ (fork t) -> ¬ (p₁ ⟼ p₃ ↑ ∅)
single-event (fork p t s) (none nF s₁) = nF (fork p t)

unique-event : ∀ {ls τ e₁ e₂} {p₁ p₂ : Program ls τ} -> p₁ ⟼ p₂ ↑ e₁ -> p₁ ⟼ p₂ ↑ e₂ -> e₁ ≡ e₂
unique-event (fork p t s) (fork .p .t s₁) = refl
unique-event (fork p t s) (none x x₁) = ⊥-elim (x (fork p t))
unique-event (none x x₁) (fork p t s) = ⊥-elim (x (fork p t))
unique-event (none x x₁) (none x₂ x₃) = refl

not-unique : ∀ {l ls} -> Unique l ls -> ¬ (l ∈ ls)
not-unique [] ()
not-unique (px ∷ u) Here = px refl
not-unique (px ∷ u) (There y) = not-unique u y

lookup-pool-size : ∀ {ls l n₁ n₂} {ps : Pools ls} {ts₁ : Pool l n₁} {ts₂ : Pool l n₂} ->
              ps [ l ]= ts₁ ->
              ps [ l ]= ts₂ -> n₁ ≡ n₂
lookup-pool-size Here Here = refl
lookup-pool-size Here (There {u = u} y) = ⊥-elim (not-unique u (read-∈ y))
lookup-pool-size (There {u = u} x) Here = ⊥-elim (not-unique u (read-∈ x))
lookup-pool-size (There x) (There y) = lookup-pool-size x y

lookup-pool : ∀ {ls l n} {ps : Pools ls} {ts₁ : Pool l n} {ts₂ : Pool l n} ->
              ps [ l ]= ts₁ ->
              ps [ l ]= ts₂ -> ts₁ ≡ ts₂
lookup-pool Here Here = refl
lookup-pool Here (There {u = u} y) = ⊥-elim (not-unique u (read-∈ y))
lookup-pool (There {u = u} x) Here = ⊥-elim (not-unique u (read-∈ x))
lookup-pool (There x) (There y) = lookup-pool x y              

lookup-thread : ∀ {l n n'} {ts : Pool l n'} {t₁ t₂ : Thread l} ->
                 ts [ n ]ᵗ= t₁ ->
                 ts [ n ]ᵗ= t₂ -> t₁ ≡ t₂
lookup-thread Here Here = refl
lookup-thread (There x) (There y) = lookup-thread x y

write-thread : ∀ {l n n'} {ts ts₁ ts₂ : Pool l n'} {t : Thread l} ->
                    ts₁ ← ts [ n ]ᵗ≔ t ->
                    ts₂ ← ts [ n ]ᵗ≔ t -> ts₁ ≡ ts₂
                    
write-thread ∙ ∙ = refl
write-thread upd upd = refl
write-thread (skip x) (skip y) rewrite write-thread x y = refl

write-pool  : ∀ {ls l n} {ps ps₁ ps₂ : Pools ls} {ts : Pool l n} ->
              ps₁ ← ps [ l ]≔ ts ->
              ps₂ ← ps [ l ]≔ ts -> ps₁ ≡ ps₂
write-pool Here Here = refl
write-pool Here (There {u = u} y) = ⊥-elim (not-unique u (write-∈ y))
write-pool (There {u = u} x) Here = ⊥-elim (not-unique u (write-∈ x))
write-pool (There x) (There y) rewrite write-pool x y = refl

thread-in∙ : ∀ {l n n'} {t : Thread l} -> (∙ {n = n'}) [ n ]ᵗ= t -> ⊥
thread-in∙ ()

-- Determinism for concurrent semantics
-- This proof is rather long because in the definition of ↪ the left hand side is (almost) always the same
-- therefore dependent-pattern match does not help in ruling out spurious cases.
-- It is not useful to refactor pools-unique and PoolView-≡ in one function because we still need to
-- rewrite the proofs l ∈ ls as equal to infer determinism
determinism↪ : ∀ {l n ls} {t₁ t₂ t₃ : Global ls} -> l , n ⊢ t₁ ↪ t₂ -> l , n ⊢ t₁ ↪ t₃ -> t₂ ≡ t₃
determinism↪ (step r₁ r₂ st sc w₁ w₂) (step r₁' r₂' st' sc' w₁' w₂') rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' |
          determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st') | deterministic-scheduler sc sc' |
          write-thread w₁ w₁' | write-pool w₂ w₂' = refl
determinism↪ (step r₁ r₂ st sc w₁ w₂) (fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (single-event st' st)
determinism↪ (step r₁ r₂ st sc w₁ w₂) (hole r₁' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = ⊥-elim (thread-in∙ r₂)
determinism↪ (step r₁ r₂ st sc w₁ w₂) (skip r₁' r₂' b sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-redex b (Step (stepOf st)))
determinism↪ (step r₁ r₂ st sc w₁ w₂) (exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st)))
determinism↪ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (single-event st st')
determinism↪ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂'
    | determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st') with unique-event st st'
... | refl rewrite lookup-pool-size r₃ r₃' | lookup-pool r₃ r₃' 
    | write-thread w₁ w₁' | write-pool w₂ w₂' | write-pool w₃ w₃' | deterministic-scheduler sc sc' = refl
determinism↪ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (hole r₁' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = ⊥-elim (thread-in∙ r₂)
determinism↪ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (skip r₁' r₂' b sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-redex b (Step (stepOf st)))
determinism↪ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st)))
determinism↪ (hole r₁ sc) (step  r₁' r₂' st' sc' w₁' w₂') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (hole r₁ sc) (fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (hole r₁ sc) (hole r₁' sc') rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = refl
determinism↪ (hole r₁ sc) (skip r₁' r₂' b sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (hole r₁ sc) (exit  r₁' r₂' isV sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (skip r₁ r₂ b sc) (step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-redex b (Step (stepOf st')))
determinism↪ (skip r₁ r₂ b sc) (fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-redex b (Step (stepOf st')))
determinism↪ (skip r₁ r₂ b sc) (hole r₁' sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂)
determinism↪ (skip r₁ r₂ b sc) (skip r₁' r₂' b' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' | deterministic-scheduler sc sc' = refl
determinism↪ (skip r₁ r₂ b sc) (exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-value b isV)
determinism↪ (exit r₁ r₂ isV sc) (step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st')))
determinism↪ (exit r₁ r₂ isV sc) (fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st')))
determinism↪ (exit r₁ r₂ isV sc) (hole r₁' sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂)
determinism↪ (exit r₁ r₂ isV sc) (skip r₁' r₂' b' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (stuck-no-value b' isV)
determinism↪ (exit r₁ r₂ isV sc) (exit r₁' r₂' isV' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' | deterministic-scheduler sc sc' = refl
