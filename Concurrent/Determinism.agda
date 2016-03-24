open import Sequential.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Relation.Binary.PropositionalEquality as E
open import Data.Product

module Concurrent.Determinism where

  (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
  (deterministic-scheduler : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃ ) where



open import Data.List.All
open import Concurrent.Semantics
import Concurrent.Communication as C

open C State _⟶_↑_ 

read-∈ : ∀ {l ls n} {ts : Pool l n} {ps : Pools ls} -> ps [ l ]= ts -> l ∈ ls
read-∈ C.Here = Here
read-∈ (C.There p) = There (read-∈ p)

write-∈ : ∀ {l ls n} {ts : Pool l n} {ps₁ ps₂ : Pools ls} -> ps₂ ← ps₁ [ l ]≔ ts -> l ∈ ls
write-∈ C.Here = Here
write-∈ (C.There x) = There (write-∈ x)

blocked-no-redex : ∀ {ls l} {Σ₁ Σ₂ : Store ls} {t₁ t₂ : Thread l} -> Blocked Σ₁ t₁ -> ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ -> ⊥
blocked-no-redex (onPut q r) (Pure ()) 
blocked-no-redex (onPut q r) (putMVarCtx (Pure ()))
blocked-no-redex {Σ₁ = Σ} (onPut q₁ r₁) (putMVar q₂ r₂) rewrite store-unique Σ q₁ q₂ = index-unique-status r₁ r₂
blocked-no-redex (onTake q r) (Pure ())
blocked-no-redex (onTake q r) (takeMVarCtx (Pure ()))
blocked-no-redex {Σ₁ = Σ} (onTake q₁ r₁) (takeMVar q₂ r₂) rewrite store-unique Σ q₁ q₂ = index-unique-status r₂ r₁

blocked-no-value : ∀ {l ls} {Σ : Store ls} {t : Thread l} -> Blocked Σ t -> IsValue t -> ⊥
blocked-no-value (onPut q r) ()
blocked-no-value (onTake q r) ()

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
lookup-pool-size C.Here C.Here = refl
lookup-pool-size C.Here (C.There {u = u} y) = ⊥-elim (not-unique u (read-∈ y))
lookup-pool-size (C.There {u = u} x) C.Here = ⊥-elim (not-unique u (read-∈ x))
lookup-pool-size (C.There x) (C.There y) = lookup-pool-size x y

lookup-pool : ∀ {ls l n} {ps : Pools ls} {ts₁ : Pool l n} {ts₂ : Pool l n} ->
              ps [ l ]= ts₁ ->
              ps [ l ]= ts₂ -> ts₁ ≡ ts₂
lookup-pool C.Here C.Here = refl
lookup-pool C.Here (C.There {u = u} y) = ⊥-elim (not-unique u (read-∈ y))
lookup-pool (C.There {u = u} x) C.Here = ⊥-elim (not-unique u (read-∈ x))
lookup-pool (C.There x) (C.There y) = lookup-pool x y              

lookup-thread : ∀ {l n n'} {ts : Pool l n'} {t₁ t₂ : Thread l} ->
                 ts [ n ]ᵗ= t₁ ->
                 ts [ n ]ᵗ= t₂ -> t₁ ≡ t₂
lookup-thread C.Here C.Here = refl
lookup-thread (C.There x) (C.There y) = lookup-thread x y

write-thread : ∀ {l n n'} {ts ts₁ ts₂ : Pool l n'} {t : Thread l} ->
                    ts₁ ← ts [ n ]ᵗ≔ t ->
                    ts₂ ← ts [ n ]ᵗ≔ t -> ts₁ ≡ ts₂
                    
write-thread C.∙ C.∙ = refl
write-thread C.upd C.upd = refl
write-thread (C.skip x) (C.skip y) rewrite write-thread x y = refl

write-pool  : ∀ {ls l n} {ps ps₁ ps₂ : Pools ls} {ts : Pool l n} ->
              ps₁ ← ps [ l ]≔ ts ->
              ps₂ ← ps [ l ]≔ ts -> ps₁ ≡ ps₂
write-pool C.Here C.Here = refl
write-pool C.Here (C.There {u = u} y) = ⊥-elim (not-unique u (write-∈ y))
write-pool (C.There {u = u} x) C.Here = ⊥-elim (not-unique u (write-∈ x))
write-pool (C.There x) (C.There y) rewrite write-pool x y = refl

thread-in∙ : ∀ {l n n'} {t : Thread l} -> (∙ {n = n'}) [ n ]ᵗ= t -> ⊥
thread-in∙ ()

-- Determinism for concurrent semantics
-- This proof is rather long because in the definition of ↪ the left hand side is (almost) always the same
-- therefore dependent-pattern match does not help in ruling out spurious cases.
-- It is not useful to refactor pools-unique and PoolView-≡ in one function because we still need to
-- rewrite the proofs l ∈ ls as equal to infer determinism
determinism↪ : ∀ {l n ls} {t₁ t₂ t₃ : Global ls} -> l , n ⊢ t₁ ↪ t₂ -> l , n ⊢ t₁ ↪ t₃ -> t₂ ≡ t₃
determinism↪ (C.step r₁ r₂ st sc w₁ w₂) (C.step r₁' r₂' st' sc' w₁' w₂') rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' |
          determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st') | deterministic-scheduler sc sc' |
          write-thread w₁ w₁' | write-pool w₂ w₂' = refl
determinism↪ (C.step r₁ r₂ st sc w₁ w₂) (C.fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (single-event st' st)
determinism↪ (C.step r₁ r₂ st sc w₁ w₂) (C.hole r₁' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = ⊥-elim (thread-in∙ r₂)
determinism↪ (C.step r₁ r₂ st sc w₁ w₂) (C.skip r₁' r₂' b sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-redex b (stepOf st))
determinism↪ (C.step r₁ r₂ st sc w₁ w₂) (C.exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st)))
determinism↪ (C.fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (C.step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (single-event st st')
determinism↪ (C.fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (C.fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂'
    | determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st') with unique-event st st'
... | refl rewrite lookup-pool-size r₃ r₃' | lookup-pool r₃ r₃' 
    | write-thread w₁ w₁' | write-pool w₂ w₂' | write-pool w₃ w₃' | deterministic-scheduler sc sc' = refl
determinism↪ (C.fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (C.hole r₁' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = ⊥-elim (thread-in∙ r₂)
determinism↪ (C.fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (C.skip r₁' r₂' b sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-redex b (stepOf st))
determinism↪ (C.fork r₁ r₂ r₃ st sc w₁ w₂ w₃) (C.exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st)))
determinism↪ (C.hole r₁ sc) (C.step  r₁' r₂' st' sc' w₁' w₂') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (C.hole r₁ sc) (C.fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (C.hole r₁ sc) (C.hole r₁' sc') rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' = refl
determinism↪ (C.hole r₁ sc) (C.skip r₁' r₂' b sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (C.hole r₁ sc) (C.exit  r₁' r₂' isV sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂')
determinism↪ (C.skip r₁ r₂ b sc) (C.step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-redex b (stepOf st'))
determinism↪ (C.skip r₁ r₂ b sc) (C.fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-redex b (stepOf st'))
determinism↪ (C.skip r₁ r₂ b sc) (C.hole r₁' sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂)
determinism↪ (C.skip r₁ r₂ b sc) (C.skip r₁' r₂' b' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' | deterministic-scheduler sc sc' = refl
determinism↪ (C.skip r₁ r₂ b sc) (C.exit r₁' r₂' isV sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-value b isV)
determinism↪ (C.exit r₁ r₂ isV sc) (C.step r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st')))
determinism↪ (C.exit r₁ r₂ isV sc) (C.fork r₁' r₂' r₃' st' sc' w₁' w₂' w₃')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (valueNotRedex _ isV (Step (stepOf st')))
determinism↪ (C.exit r₁ r₂ isV sc) (C.hole r₁' sc') rewrite lookup-pool-size r₁ r₁' with lookup-pool r₁ r₁'
... | refl = ⊥-elim (thread-in∙ r₂)
determinism↪ (C.exit r₁ r₂ isV sc) (C.skip r₁' r₂' b' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' = ⊥-elim (blocked-no-value b' isV)
determinism↪ (C.exit r₁ r₂ isV sc) (C.exit r₁' r₂' isV' sc')
  rewrite lookup-pool-size r₁ r₁' | lookup-pool r₁ r₁' | lookup-thread r₂ r₂' | deterministic-scheduler sc sc' = refl
