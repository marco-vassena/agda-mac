open import Lattice 
open import Scheduler using (Scheduler)

module Concurrent.Security.NonInterference (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Types 𝓛
open import Scheduler 𝓛 renaming ( _,_,_ to ⟪_,_,_⟫ )
open Scheduler.Scheduler 𝓛 𝓢 

open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Security.Distributivity 𝓛 renaming (εˢ-≡ to high-stepˢ)
open import Sequential.Security.Erasure.LowEq 𝓛
open import Sequential.Security.NonInterference 𝓛 -- hiding (_≈ᵖ_ ; non-interference)

open import Concurrent.Determinism 𝓛 𝓢
open import Concurrent.Security.Distributivity 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢
open import Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Security.Erasure 𝓛 𝓢
open import Concurrent.Security.Scheduler 𝓛 𝓢

open import Data.Product 
open import Relation.Binary.PropositionalEquality

--open Global

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

high-step : ∀ {lₐ l ls n} {g₁ g₂ : Global ls} -> ¬ (l ⊑ lₐ) -> l , n ⊢ g₁ ↪ g₂ -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₂
high-step ¬p (step r st sc w) = ⟨ ≡-≈ˢ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (ε-updateᵖ-≡ ¬p w) ⟩
high-step ¬p (fork r₁ r₂ st sc  w₁ w₂)
  = ⟨ ≡-≈ˢ ((ε-sch-≡ ¬p sc)) , εˢ-≡ (high-stepˢ _ ¬p (stepOf st)) , ≡-≈ᴾ (trans (ε-updateᵗ-≡ (trans-⋢ (fork-⊑ st) ¬p) w₁) (ε-updateᵖ-≡ ¬p w₂)) ⟩
high-step ¬p (hole r st sc) = ⟨ ≡-≈ˢ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (skip r b sc) = ⟨ ≡-≈ˢ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩
high-step ¬p (exit r isV sc) = ⟨ ≡-≈ˢ ((ε-sch-≡ ¬p sc)) , εˢ-≡ refl , ≡-≈ᴾ refl ⟩

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

-- Why do not we need the contstraint l ⊑ lₐ here?
readPool-≈ : ∀ {ls l lₐ n} {ps₁ ps₂ : Pools ls} {ts₁ : Pool l n} -> ps₁ ≈ᴾ-⟨ lₐ ⟩ ps₂ -> ps₁ [ l ]= ts₁ ->
                   Σ (Pool l n) (λ ts₂ -> (ps₂ [ l ]= ts₂) × (ts₁ ≌ᴾ-⟨ lₐ ⟩ ts₂))
readPool-≈ (ts₁≈ts₂ ∷ eq) Here = _ , (Here , ts₁≈ts₂)
readPool-≈ (ts₁≈ts₂ ∷ eq) (There r) with readPool-≈ eq r
... | _ , r' , eq' = _ , (There r') , eq'

-- TODO USE CONSISTENT NAMES
--open import Concurrent.Security.Scheduler State _⟶_↑_ ε-state _≈ˢ-⟨_⟩_ _≈ˢ-⟨_~_~_⟩_

--------------------------------------------------------------------------------

data NI {ls} (lₐ : Label) (g₁' g₂ : Global ls) : Set where
  isNI : ∀ {g₂'} -> g₁' ↪⋆ g₂' -> g₂ ≈ᵍ-⟨ lₐ ⟩ g₂' -> NI lₐ g₁' g₂

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
≈ᵉ-≡ (yes p) (fork x (ε-≡ eq)) with eq
... | eq' rewrite eq' = refl
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

-- TODO maybe we don't need this
postulate same-event : ∀ {ls l lₐ e₁ e₂} {p₁ p₂ p₁' p₂' : Program ls (Mac l _)} -> l ⊑ lₐ -> p₁ ≈ᵖ-⟨ lₐ ⟩ p₂ -> p₁ ⟼ p₂ ↑ e₁ -> p₁' ⟼ p₂' ↑ e₂ -> e₁ ≈ᵉ-⟨ lₐ ⟩ e₂

-- At the moment I am assuming that the scheduler state contains only valid thread id, that is
-- Ideally it should be: if the scheduler s₁ ⟶ s₂ ↑ (l , n , e) and g₁ = ⟨ s₁ , Σ₁ , ps₁ ⟩ then there is a thread at ps₁ [ l ][ n ],
-- however due to the mutual dependency we cannot retrieve s₁ ⟶ s₂ ↑ _ if we don't know the event e already.
-- postulate getScheduledThread : ∀ {ls l n s₂ e} (g₁ : Global ls) -> let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁ in s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> ∃ (λ t -> ps₁ [ l ][ n ]= t)
postulate getThread : ∀ {ls} (l : Label) (n : ℕ) (ps : Pools ls) -> ∃ (λ t -> ps [ l ][ n ]= t)

-- When a thread is forked we can find the corresponding thread pool.
postulate getPoolThread : ∀ {ls} (l : Label) (ps : Pools ls) -> ∃ (λ n -> Σ (Pool l n) (λ ts -> ps [ l ]= ts))

--------------------------------------------------------------------------------

-- Essentially we rule out ∙ steps.
data Valid {ls} (g : Global ls) : Set where
  isValid : (∀ {l n t} -> (pools g) [ l ][ n ]= t -> t ≢ ∙) -> Valid g

-- In order to actually prove this we need the stronger condition ps [ l ][ n ]= t ∧ • ∉ t
postulate stepValid : ∀ {ls l n} {g₁ g₂ : Global ls} {{ v₁ : Valid g₁ }} -> l , n ⊢ g₁ ↪ g₂ -> Valid g₂

stepValid⋆ : ∀ {ls} {g₁ g₂ : Global ls} {{v₁ : Valid g₁}} -> g₁ ↪⋆ g₂ -> Valid g₂
stepValid⋆ {{v₁}} [] = v₁
stepValid⋆ {{v₁}} (s ∷ ss) = stepValid⋆ {{ stepValid s }} ss


-- fork? never produces a • event
fork?≠∙ : ∀ {l h n} {tʰ :  Thread h} {p : l ⊑ h} -> fork? p tʰ n ≢ ∙
fork?≠∙ {tʰ = t} {p} with is∙? t
... | yes _ = λ ()
... | no _ = λ ()

-- Only ∙ triggers the event •
∙↑∙ : ∀ {ls l n} {g₁ g₂ : Global ls} -> Valid g₁ -> (s : l , n ⊢ g₁ ↪ g₂) -> getEvent s ≢ ∙
∙↑∙ v (step x x₁ x₂ x₃) ()
∙↑∙ v (fork x x₁ x₂ x₃ x₄ x₅) eq = ⊥-elim (fork?≠∙ eq)
∙↑∙ (isValid f) (hole r (bullet s) x₂) refl = ⊥-elim (f r refl)
∙↑∙ v (skip x x₁ x₂) ()
∙↑∙ v (exit x x₁ x₂) ()

-- TODO move to semantics module?
-- If we can read from a pool, then we can write something to it
postulate writePool : ∀ {l n ls t₁ t₂} {ps₁ : Pools ls} -> ps₁ [ l ][ n ]= t₁ -> ∃ (λ ps₂ -> ps₂ ← ps₁ [ l ][ n ]≔ t₂)
postulate forkPool : ∀ {h n ls} {ps₁ : Pools ls} {ts : Pool h n} -> ps₁ [ h ]= ts -> (t : Thread h) -> ∃ (λ ps₂ -> ps₂ ← ps₁ [ h ]≔ (ts ▻ t))
-- TODO could be proved by showing that forking preserves the validity of old references, that is
-- ps [ l ][ n ]= t, ps' ← ps [ h ] = ts ▻ t' => ps [ l ][ n ]= t
postulate writeAfterFork : ∀ {l h n n' ls t₁ t₂} {ps₁ ps₂ : Pools ls} (ts : Pool h n')
                             -> ps₁ [ l ][ n ]= t₁ -> ps₂ ← ps₁ [ h ]≔ ts -> ∃ (λ ps₃ -> ps₃ ← ps₂ [ l ][ n ]≔ t₂)

square : ∀ {l n e ls s₂' lₐ} {g₁ g₂ g₁' : Global ls} {{v₁ : Valid g₁}} -> l ⊑ lₐ ->
                                let ⟨ s₁ , Σ₁ , ps₁ ⟩ = g₁
                                    ⟨ s₁' , Σ₁' , ps₁' ⟩ = g₁'
                                    ⟨ s₂ , Σ₂ , ps₂  ⟩ = g₂
                                    m = ⟪ l , n , e ⟫ in s₁' ⟶ s₂' ↑ m -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> m ⊢ᴹ g₁ ↪ g₂ ->
                                ∃ (λ Σ₂' -> (∃ (λ ps₂' ->
                                  let g₂' = ⟨ s₂' , Σ₂' , ps₂' ⟩ in (l , n ⊢ g₁' ↪ g₂'))))
square p sc' ⟨ s₁≈s₁' , Σ₁≈Σ₁' , ps≈ps₁' ⟩ (withMsg (step r (none ¬fork ¬∙ s) sc w)) with read-≈ p ps≈ps₁' r
... | t₁' , r' , t₁≈t₁' with redexᴸ p s (εᵖ-≡ Σ₁≈Σ₁' t₁≈t₁')
... | Step s' with writePool r'
... | ps₂' , w' = _ , ps₂' , step r' (none (isNotForkᴸ p ¬fork t₁≈t₁') (isNot∙ᴸ p ¬∙ t₁≈t₁') s') sc' w'
square p sc'  ⟨ s₁≈s₁' , Σ₁≈Σ₁' , ps≈ps₁' ⟩ (withMsg (fork r₁ r₂ (fork p' t₁ s) sc w₁ w₂))  with read-≈ p ps≈ps₁' r₁
... | t₁' , r₁' , t₁≈t₁' with redexᴸ p s (εᵖ-≡ Σ₁≈Σ₁' t₁≈t₁')  -- Here by pattern matching on the equivalence proof I would learn that t₁' is also fork
... | Step s' with readPool-≈ ps≈ps₁' r₂
... | ts₁' , r₂' , ts₁≈ts₁' with forkPool r₂' t₁
... | ps₂' , w₁' with writeAfterFork (ts₁' ▻ {!!})  r₁' w₁' -- We should get the forked thread from the l-equivalence proof
... | ps₃' , w₂' = {!!} , {!!} , {!fork r₁' r₂' (fork ? ? ?) sc' w₁' w₂'!}
square {{isValid ¬∙}} p sc' ⟨ s₁≈s₁' , Σ₁≈Σ₁' , ps₁≈ps₁' ⟩ (withMsg (hole r (bullet (Pure Hole)) sc)) = ⊥-elim (¬∙ r refl)
square p sc' ⟨ s₁≈s₁' , Σ₁≈Σ₁' , ps₁≈ps₁' ⟩ (withMsg (skip r isS sc)) with read-≈ p ps₁≈ps₁' r
... | t₁' , r' , t₁≈t₁' = _ , _ , skip r' (stuckᴸ p (εᵖ-≡ Σ₁≈Σ₁' t₁≈t₁') isS) sc'
square p sc' ⟨ s₁≈s₁' , Σ₁≈Σ₁' , ps₁≈ps₁' ⟩ (withMsg (exit r isV sc)) with read-≈ p ps₁≈ps₁' r
... | t₁' , r' , t₁≈t₁' = _ , _ , exit r' (valueᴸ p isV t₁≈t₁') sc'

module PS
    (highˢ : ∀ {s₁ s₁' s₂ l lₐ n e i j} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ lₐ ~ suc j ⟩ s₁' ->
                    ∃ λ h -> ∃ λ n -> (e' : Event h) -> e' ≢ ∙ -> HighStep lₐ h n e' s₁ s₂ s₁' i j)
     (aligned : ∀ {l lₐ n i e s₁ s₂ s₁'} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ lₐ ~ 0 ⟩ s₁' -> Aligned s₁ s₂ s₁' ⟪ l , n , e ⟫ lₐ)
  where

    low-step : ∀ {l n lₐ n₁ n₂ ls} {g₁ g₂ g₁' : Global ls} {{v₁ : Valid g₁}} {{v₁' : Valid g₁'}} -> l ⊑ lₐ ->
                 (s : l , n ⊢ g₁ ↪ g₂) -> (state g₁) ≈ˢ-⟨ n₁ ~ lₐ ~ n₂ ⟩ (state g₁') -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> NI lₐ g₁' g₂
    low-step {lₐ = lₐ} {n₂ = zero} {{v₁}} p gs eq₁ eq₂ with aligned p (getSchedulerStep gs) (∙↑∙ v₁ gs) eq₁
    ... | low sc' eq₁' with square p sc' eq₂ (withMsg gs)
    ... | Σ₂' , ps₂' , gs' = isNI (gs' ∷ []) (simulation↪ {{lₐ}} eq₂ gs gs')                        

    -- The other global configuration performs a high step
    low-step {n₂ = suc n₂} {g₁ = g₁} {g₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} {{v₁}} p gs eq₁ ⟨ a , b , c ⟩ with highˢ p (getSchedulerStep gs) (∙↑∙ v₁ gs) eq₁
    ... | h , n , k with getThread h n ps₁'
    ... | t' , r' with programStatus Σ₁' t'

    -- Done Event
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | V isV with k Done (λ ())
    ... | high ¬p sc' eq₁' with low-step {{ v₁' = stepValid (exit r' isV sc') }} p gs eq₁' ⟨ forget eq₁' , b , c ⟩
    ... | isNI ss eq₂' = isNI ((exit r' isV sc') ∷ ss) eq₂'
    
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) with effectOf t' | stepWithEvent st

    -- Hole Event (absurd)
    low-step {n₂ = suc n₂} {{v₁' = isValid f}} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | .∙ , r' | R (Step st) | ∙ | bullet (Pure Hole) = ⊥-elim (f r' refl)

    -- Step Event
    low-step {n₂ = suc n₂} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) | ∅ | st' with k Step (λ ())
    ... | high ¬p sc' eq₁' with writePool r'
    ... | ps₂' , w' with high-step ¬p (step r' st' sc' w')
    ... | eq'' with low-step {{ v₁' = stepValid (step r' st' sc' w') }} p gs eq₁' (trans-≈ᵍ ⟨ a , b , c ⟩ eq'')
    ... | isNI {g₂'} ss eq₂' = isNI (step r' st' sc' w' ∷ ss) eq₂'

    -- Fork Event
    -- TODO here we need to assume that the label of the forked thread is in the pool.
    -- Then we can compute nʰ as the length of the corresponding thread pool.
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | R (Step st) | fork {hⁿ} tⁿ | st'
      with getPoolThread hⁿ ps₁'
    ... | nⁿ , tsⁿ , rⁿ with k (fork? (fork-⊑ st') tⁿ nⁿ) fork?≠∙
    ... | high ¬p sc' eq₁' with forkPool rⁿ tⁿ
    ... | ps₂' , w' with writeAfterFork (tsⁿ ▻ tⁿ) r' w'
    ... | ps₃' , w'' with high-step ¬p (fork {l⊑h = fork-⊑ st'} r' rⁿ st' sc' w' w'')
    ... | eq'' with low-step {{ v₁' = stepValid (fork {l⊑h = fork-⊑ st'} r' rⁿ st' sc' w' w'') }} p gs eq₁' (trans-≈ᵍ ⟨ a , b , c ⟩ eq'')
    ... | isNI ss eq₂' = isNI (fork {l⊑h = fork-⊑ st'} r' rⁿ st' sc' w' w'' ∷ ss) eq₂'

    -- NoStep Event
    low-step {n₂ = suc n₂} {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩} p gs eq₁ ⟨ a , b , c ⟩ | h , n , k | t' , r' | S isS with k NoStep (λ ())
    ... | high ¬p sc' eq₁' with low-step {{ v₁' = stepValid (skip r' isS sc') }}  p gs eq₁' ⟨ forget eq₁' , b , c ⟩
    ... | isNI ss eq₂' = isNI (skip r' isS sc' ∷ ss) eq₂'

    -- TODO maybe use NI data-type for clarity
    ps-ni-dispatch : ∀ {l n ls lₐ} {g₁ g₁' g₂ : Global ls} {{v₁ : Valid g₁}} {{v₁' : Valid g₁'}} -> Dec (l ⊑ lₐ) ->
                          g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> (s : l , n ⊢ g₁ ↪ g₂) -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂' )
    ps-ni-dispatch {g₁' = ⟨ s₁' , Σ₁' , ps₁' ⟩ } (yes p) ⟨ eq₁ , eq₂ , eq₃ ⟩ s with low-step p s (align eq₁) ⟨ eq₁ , eq₂ , eq₃ ⟩
    ... | isNI ss eq'  = _ Σ., (eq' Σ., ss)
    ps-ni-dispatch {g₁' = g₁'} (no ¬p) eq s = g₁' , trans-≈ᵍ (sym-≈ᵍ (high-step ¬p s)) eq , []

    -- TODO I will probably need to add the assumption ps [ l ][ n ] ≠ ∙
    progress-sensitive-ni : ∀ {l ls n} {g₁ g₁' g₂ : Global ls} {{v₁ : Valid g₁}} {{v₁' : Valid g₁'}}  -> (lₐ : Label) -> g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' ->
                              l , n ⊢ g₁ ↪ g₂ -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂')
    progress-sensitive-ni {l} lₐ = ps-ni-dispatch (l ⊑? lₐ)
    
    progress-sensitive-ni⋆ : ∀ {ls} {g₁ g₁' g₂ : Global ls} {{v₁ : Valid g₁}} {{v₁' : Valid g₁'}} -> (lₐ : Label) ->
                                g₁ ≈ᵍ-⟨ lₐ ⟩ g₁' -> (ss : g₁ ↪⋆ g₂) -> ∃ (λ g₂' → (g₂ ≈ᵍ-⟨ lₐ ⟩ g₂') × g₁' ↪⋆ g₂')
    progress-sensitive-ni⋆ lₐ eq [] = _ , (eq , [])
    progress-sensitive-ni⋆ {{v₁}} {{v₁'}} lₐ eq (s ∷ ss) with progress-sensitive-ni lₐ eq s
    ... | g₂' , eq₂' , ss₂' with progress-sensitive-ni⋆ {{ stepValid s }} {{ stepValid⋆ ss₂' }} lₐ eq₂' ss
    ... | g₃' , eq₃' , ss₃' = g₃' , (eq₃' , ss₂' ++ˢ ss₃')
