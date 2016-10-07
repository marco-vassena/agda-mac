open import Lattice
open import Scheduler using (Scheduler)

module Concurrent.Determinism (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Types 𝓛
open import Scheduler 𝓛 as S

open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Determinism 𝓛
open import Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢

open import Relation.Binary.PropositionalEquality
open import Data.List.All

read-∈ : ∀ {l ls n} {ts : Pool l n} {ps : Pools ls} -> ps [ l ]= ts -> l ∈ ls
read-∈ Here = Here
read-∈ (There p) = There (read-∈ p)

read-∈' : ∀ {l ls n} {t : Thread l} {ps : Pools ls} -> ps [ l ][ n ]= t -> l ∈ ls
read-∈' (Here x) = Here
read-∈' (There x) = There (read-∈' x)

write-∈ : ∀ {l ls n} {ts : Pool l n} {ps₁ ps₂ : Pools ls} -> ps₂ ← ps₁ [ l ]≔ ts -> l ∈ ls
write-∈ Here = Here
write-∈ (There x) = There (write-∈ x)

write-∈' : ∀ {l ls n} {t : Thread l} {ps₁ ps₂ : Pools ls} -> ps₂ ← ps₁ [ l ][ n ]≔ t -> l ∈ ls
write-∈' (Here x) = Here
write-∈' (There x) = There (write-∈' x)

single-event : ∀ {l ls e₁ e₂} {p₁ p₂ p₃ : Program ls (Mac l （）)} -> p₁ ⟼ p₂ ↑ e₁ -> e₁ ≢ e₂ -> ¬ (p₁ ⟼ p₃ ↑ e₂)
single-event (bullet x) e₁≠e₂ (bullet x₁) = e₁≠e₂ refl
single-event (bullet x) e₁≠e₂ (none x₁ x₂ x₃) = x₂ ∙
single-event (fork p t₁ s) e₁≠e₂ (fork .p .t₁ s₁) = e₁≠e₂ refl
single-event (fork p t₁ s) e₁≠e₂ (none x x₁ x₂) = x (fork p t₁)
single-event (none x x₁ x₂) e₁≠e₂ (bullet x₃) = x₁ Is∙.∙
single-event (none x x₁ x₂) e₁≠e₂ (fork p t₁ s) = x (fork p t₁)
single-event (none x x₁ x₂) e₁≠e₂ (none x₃ x₄ x₅) = e₁≠e₂ refl

unique-event : ∀ {ls l e₁ e₂} {p₁ p₂ : Program ls (Mac l （）)} -> p₁ ⟼ p₂ ↑ e₁ -> p₁ ⟼ p₂ ↑ e₂ -> e₁ ≡ e₂
unique-event (bullet x) (bullet x₁) = refl
unique-event (bullet x) (none x₁ x₂ x₃) = ⊥-elim (x₂ ∙)
unique-event (fork p t s) (fork .p .t s₁) = refl
unique-event (fork p t s) (none x x₁ x₂) = ⊥-elim (x (fork p t))
unique-event (none x x₁ x₂) (bullet x₃) = ⊥-elim (x₁ ∙)
unique-event (none x x₁ x₂) (fork p t s) = ⊥-elim (x (fork p t))
unique-event (none x x₁ x₂) (none x₃ x₄ x₅) = refl

not-unique : ∀ {l ls} -> Unique l ls -> ¬ (l ∈ ls)
not-unique [] ()
not-unique (px ∷ u) Here = px refl
not-unique (px ∷ u) (There y) = not-unique u y

stuck-no-redex : ∀ {ls l} {Σ₁ : Store ls} {t₁ : Thread l} -> Stuck Σ₁ t₁ -> Redex Σ₁ t₁ -> ⊥
stuck-no-redex (stuck x x₁) r = ⊥-elim (x r)

stuck-no-value : ∀ {l ls} {Σ : Store ls} {t : Thread l} -> Stuck Σ t -> IsValue t -> ⊥
stuck-no-value (stuck x x₁) isV = x₁ isV


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
                 LookupThread t₁ n ts -> LookupThread t₂ n ts -> t₁ ≡ t₂
lookup-thread ∙ ∙ = refl
lookup-thread Here Here = refl
lookup-thread (There x) (There y) = lookup-thread x y

lookup-tpool : ∀ {ls l n} {ps : Pools ls} {t₁ t₂ : Thread l} ->
              ps [ l ][ n ]= t₁ ->
              ps [ l ][ n ]= t₂ -> t₁ ≡ t₂
lookup-tpool (Here x) (Here y) = lookup-thread x y
lookup-tpool (Here x) (There {u = u} y) = ⊥-elim (not-unique u (read-∈' y))
lookup-tpool (There {u = u} x) (Here y) = ⊥-elim (not-unique u (read-∈' x))
lookup-tpool (There x) (There y) = lookup-tpool x y              


write-thread : ∀ {l n n'} {ts₁ ts₂ ts₃ : Pool l n'} {t : Thread l} ->
                    UpdateThread t n ts₁ ts₂ ->
                    UpdateThread t n ts₁ ts₃ -> ts₂ ≡ ts₃
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

write-tpool  : ∀ {ls l n} {ps ps₁ ps₂ : Pools ls} {t : Thread l} ->
               ps₁ ← ps [ l ][ n ]≔ t ->
               ps₂ ← ps [ l ][ n ]≔ t -> ps₁ ≡ ps₂
write-tpool (Here x) (Here y) rewrite write-thread x y = refl
write-tpool (Here x) (There {u = u} y) = ⊥-elim (not-unique u (write-∈' y))
write-tpool (There {u = u} x) (Here x₁) = ⊥-elim (not-unique u (write-∈' x))
write-tpool (There x) (There y) rewrite write-tpool x y = refl

-- This is needed only in fork vs fork case
-- We could probably do it without a postulate using a proof l ⊑? h ≡ yes p
postulate extensional-⊑ : ∀ {l h} -> (p₁ p₂ : l ⊑ h) -> p₁ ≡ p₂

-- Determinism for concurrent semantics
-- This proof is rather long because in the definition of ↪ the left hand side is (almost) always the same
-- therefore dependent-pattern match does not help in ruling out spurious cases.
-- It is not useful to refactor pools-unique and PoolView-≡ in one function because we still need to
-- rewrite the proofs l ∈ ls as equal to infer determinism
determinism↪ : ∀ {l n ls} {t₁ t₂ t₃ : Global ls} -> l , n ⊢ t₁ ↪ t₂ -> l , n ⊢ t₁ ↪ t₃ -> t₂ ≡ t₃
determinism↪ (step r st sc w) (step r' st' sc' w')
  rewrite lookup-tpool r r'
  -- For reasons beyond my understanding we need 𝓢 as an explicit paramter
  with determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st') | S.Scheduler.deterministic-scheduler 𝓢 sc sc'
... | eq₁ | eq₂ | eq₃ rewrite eq₁ | eq₂ | eq₃ | write-tpool w w' = refl
determinism↪ (step r st sc w) (fork r₁' r₂' st' sc' w₁' w₂') rewrite lookup-tpool r r₁' = ⊥-elim (single-event st' (λ ()) st)
determinism↪ (step r st sc w) (hole r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (single-event st' (λ ()) st)
determinism↪ (step r st sc w) (skip r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-redex st' (redexOf st))
determinism↪ (step r st sc w) (exit r' isV sc') rewrite lookup-tpool r r' = ⊥-elim (valueNotRedex _ isV (redexOf st))
determinism↪ (fork r₁ r₂ st sc w₁ w₂) (step r' st' sc' w') rewrite lookup-tpool r₁ r' = ⊥-elim (single-event st' (λ ()) st)
determinism↪ (fork {{p₁}} r₁ r₂ st sc w₁ w₂) (fork {{p₂}} r₁' r₂' st' sc' w₁' w₂')
  rewrite lookup-tpool r₁ r₁' with determinismS (stepOf st) (stepOf st') | determinismC (stepOf st) (stepOf st')
... | eq₁ | eq₂ rewrite eq₁ | eq₂ with unique-event st st'
... | refl rewrite lookup-pool-size r₂ r₂' |  lookup-pool r₂ r₂' | write-pool w₁ w₁' | write-tpool w₂ w₂'
    | extensional-⊑ p₁ p₂ | S.Scheduler.deterministic-scheduler 𝓢 sc sc' = refl
determinism↪ (fork r₁ r₂ st sc w₁ w₂) (hole r' st' sc') rewrite lookup-tpool r₁ r' = ⊥-elim (single-event st (λ ()) st')
determinism↪ (fork r₁ r₂ st sc w₁ w₂) (skip r' st' sc') rewrite lookup-tpool r₁ r' = ⊥-elim (stuck-no-redex st' (redexOf st))
determinism↪ (fork r₁ r₂ st sc w₁ w₂) (exit r' st' sc') rewrite lookup-tpool r₁ r' = ⊥-elim (valueNotRedex _ st' (redexOf st))
determinism↪ (hole r st sc) (step r' st' sc' w') rewrite lookup-tpool r r' = ⊥-elim (single-event st' (λ ()) st)
determinism↪ (hole r st sc) (fork r₁' r₂' st' sc' w₁' w₂') rewrite lookup-tpool r r₁' = ⊥-elim (single-event st' (λ ()) st)
determinism↪ (hole r st sc) (hole r' st' sc') = refl
determinism↪ (hole r st sc) (skip r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-redex st' (redexOf st))
determinism↪ (hole r st sc) (exit r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (valueNotRedex _ st' (redexOf st))
determinism↪ (skip r st sc) (step r' st' sc' w') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-redex st (redexOf st'))
determinism↪ (skip r st sc) (fork r₁' r₂' st' sc' w₁' w₂') rewrite lookup-tpool r r₁' = ⊥-elim (stuck-no-redex st (redexOf st'))
determinism↪ (skip r st sc) (hole r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-redex st (redexOf st'))
determinism↪ (skip r st sc) (skip r' st' sc') with S.Scheduler.deterministic-scheduler 𝓢 sc sc'
... | eq rewrite eq = refl
determinism↪ (skip r st sc) (exit r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-value st st')
determinism↪ (exit r st sc) (step r' st' sc' w') rewrite lookup-tpool r r' = ⊥-elim (valueNotRedex _ st (redexOf st'))
determinism↪ (exit r st sc) (fork r₁' r₂' st' sc' w₁' w₂') rewrite lookup-tpool r r₁' = ⊥-elim (valueNotRedex _ st (redexOf st'))
determinism↪ (exit r st sc) (hole r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (valueNotRedex _ st (redexOf st'))
determinism↪ (exit r st sc) (skip r' st' sc') rewrite lookup-tpool r r' = ⊥-elim (stuck-no-value st' st)
determinism↪ (exit r st sc) (exit r' st' sc') with S.Scheduler.deterministic-scheduler 𝓢 sc sc'
... | eq rewrite eq = refl
