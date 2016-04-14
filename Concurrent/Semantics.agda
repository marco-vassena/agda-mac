open import Concurrent.Communication
open import Concurrent.Calculus public


-- TODO pack everything scheduler related in a single record called Scheduler
module Concurrent.Semantics (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set) where

open import Data.Nat
open import Data.List
open import Sequential.Semantics 


--------------------------------------------------------------------------------
-- Lookup threads and thread pools

data LookupThread {l : Label} : ∀ {n} -> (t : Thread l) -> ℕ -> Pool l n -> Set where
  ∙ : ∀ {n n'} -> LookupThread ∙ n (∙ {n = n'})
  Here : ∀ {n t} {ts : Pool l n} -> LookupThread t zero (t ◅ ts)
  There : ∀ {n₁ n₂ t} {ts : Pool l n₂} {t' : Thread l} -> LookupThread t n₁ ts -> LookupThread t (suc n₁) (t' ◅ ts)

data LookupTPool {l : Label} (n : ℕ) (t : Thread l) : ∀ {ls} -> Pools ls -> Set where
  Here : ∀ {ls n'} {u : Unique l ls} {p : Pool l n'} {ps : Pools ls} -> LookupThread t n p -> LookupTPool n t (p ◅ ps)
  There : ∀ {l' n' ls} {u : Unique l' ls} {ps : Pools ls} {p' : Pool l' n'} -> LookupTPool n t ps -> LookupTPool n t (p' ◅ ps)

_[_][_]=_ : ∀ {ls} -> Pools ls -> (l : Label) -> ℕ -> Thread l -> Set
ps [ l ][ n ]= t = LookupTPool n t ps

--------------------------------------------------------------------------------
-- Updates threads

data UpdateThread {l : Label} (t : Thread l) : ∀ {n} -> ℕ -> Pool l n -> Pool l n -> Set where
  ∙ : ∀ {n n'} -> UpdateThread t n (∙ {n = n'}) ∙
  upd : ∀ {n} {ts : Pool l n} {t₁ : Thread l} -> UpdateThread t zero (t₁ ◅ ts) (t ◅ ts)
  skip : ∀ {n} {ts₁ ts₂ : Pool l n} {t' : Thread l} -> UpdateThread t n ts₁ ts₂ -> UpdateThread t (suc n) (t' ◅ ts₁) (t' ◅ ts₂)

data UpdateTPool {l : Label} (t : Thread l) (n : ℕ) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  Here : ∀ {ls n'} {u : Unique l ls} {p₁ p₂ : Pool l n'} {ps : Pools ls} -> UpdateThread t n p₁ p₂ -> UpdateTPool t n (p₁ ◅ ps) (p₂ ◅ ps)
  There : ∀ {l' n' ls} {u : Unique l' ls} {ps₁ ps₂ : Pools ls} {p' : Pool l' n'} -> UpdateTPool t n ps₁ ps₂ -> UpdateTPool t n (p' ◅ ps₁) (p' ◅ ps₂)

_←_[_][_]≔_ : ∀ {ls} -> Pools ls -> Pools ls -> (l : Label) -> ℕ -> Thread l -> Set
ps₂ ← ps₁ [ l ][ n ]≔ t = UpdateTPool t n ps₁ ps₂

--------------------------------------------------------------------------------

-- Read Thread Pool

data LookupPool {l : Label} {n : ℕ} (ts : Pool l n) : ∀ {ls} -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {ps : Pools ls} -> LookupPool ts (ts ◅ ps)
  There : ∀ {ls l' n'} {u : Unique l' ls} {ts' : Pool l' n'} {ps : Pools ls} -> LookupPool ts ps -> LookupPool ts (ts' ◅ ps)

_[_]=_ : ∀ {n ls} -> Pools ls -> (l : Label) -> Pool l n -> Set
ps [ h ]= ts = LookupPool ts ps

-- Update Thread pool

data UpdatePool {l : Label} {n : ℕ} (ts : Pool l n) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {ps : Pools ls} {ts' : Pool l n} -> UpdatePool ts (ts' ◅ ps) (ts ◅ ps) 
  There : ∀ {ls l' n'} {u : Unique l' ls} {ps₁ ps₂ : Pools ls} {ts' : Pool l' n'} -> UpdatePool ts ps₁ ps₂ -> UpdatePool ts (ts' ◅ ps₁) (ts' ◅ ps₂)


_←_[_]≔_ : ∀ {n ls} -> Pools ls -> Pools ls -> (l : Label) -> Pool l n -> Set
ps₂ ← ps₁ [ l ]≔ ts = UpdatePool ts ps₁ ps₂

--------------------------------------------------------------------------------

-- Effect triggered in the sequential setting
data Effect (l : Label) :  Set where
  ∙ : Effect l 
  ∅ : Effect l 
  fork : ∀ {h} -> Thread h -> Effect l      -- I don't think we need l ⊑ h

-- We need to tie the event data type with the small step semantics.
-- I don't want to redefine the small step semantics with an additional index, neither
-- I want to write a wrapper for each of them.
-- Since fork is absolutely lazy, p₁ ⟼ p₂ generates a fork even iff p₁ is fork.
-- Therefore we can use  that to determine which event we need to generate.
-- Note that if we had a forkCtx rule this wouldn't be ok.
-- Nevertheless we want to restrict the pair of programs that can genearte events to
-- only those that denote possible step. That is why internally we store
-- a proof (s : p₁ ⟼ p₂). The fact that s is existentially quantified is good
-- because it means that we don't care about the actual step object: any step
-- with the right type will do.

open Program

data IsFork : ∀ {τ} -> CTerm τ -> Set where
  fork : ∀ {l h} -> (p : l ⊑ h) (t : Thread h) -> IsFork (fork p t)

data Is∙ {τ : Ty} : CTerm τ -> Set where
  ∙ : Is∙ ∙

is∙? : ∀ {τ} -> (c : CTerm τ) -> Dec (Is∙ c)
is∙? （） = no (λ ())
is∙? True = no (λ ())
is∙? False = no (λ ())
is∙? (Var x) = no (λ ())
is∙? (Abs c) = no (λ ())
is∙? (App c c₁) = no (λ ())
is∙? (If c Then c₁ Else c₂) = no (λ ())
is∙? (Return c) = no (λ ())
is∙? (c >>= c₁) = no (λ ())
is∙? ξ = no (λ ())
is∙? (Throw c) = no (λ ())
is∙? (Catch c c₁) = no (λ ())
is∙? (Mac c) = no (λ ())
is∙? (Macₓ c) = no (λ ())
is∙? (Res c) = no (λ ())
is∙? (Resₓ c) = no (λ ())
is∙? (relabel x c) = no (λ ())
is∙? (relabel∙ x c) = no (λ ())
is∙? (label x c) = no (λ ())
is∙? (unlabel x c) = no (λ ())
is∙? (join x c) = no (λ ())
is∙? zero = no (λ ())
is∙? (suc c) = no (λ ())
is∙? (read x c) = no (λ ())
is∙? (write x c c₁) = no (λ ())
is∙? (new x c) = no (λ ())
is∙? (fmap c c₁) = no (λ ())
is∙? (fmap∙ c c₁) = no (λ ())
is∙? (fork x c) = no (λ ())
is∙? (newMVar x) = no (λ ())
is∙? (takeMVar c) = no (λ ())
is∙? (putMVar c c₁) = no (λ ())
is∙? ∙ = yes ∙

data _⟼_↑_ {l : Label} {ls : List Label} : (p₁ p₂ : Program ls (Mac l （）)) -> Effect l -> Set where
  bullet : {Σ : Store ls} -> ⟨ Σ ∥ (∙ {{τ = Mac l （）}}) ⟩ ⟼ ⟨ Σ ∥ ∙ ⟩ -> ⟨ Σ ∥ ∙ {{τ = Mac l （）}} ⟩ ⟼ ⟨ Σ ∥ ∙ ⟩ ↑ ∙
  fork : ∀ {h} {p₂ : Program ls (Mac l （）)} {Σ : Store ls} ->
         (p : l ⊑ h) (t : Thread h) (s : ⟨ Σ ∥ fork p t ⟩ ⟼ p₂) -> ⟨ Σ ∥ fork p t ⟩ ⟼ p₂ ↑ (fork t)
  none : {p₁ p₂ : Program ls (Mac l （）)} -> ¬ IsFork (term p₁) -> ¬ Is∙ (term p₁) -> p₁ ⟼ p₂ -> p₁ ⟼ p₂ ↑ ∅ 

stepOf : ∀ {ls l} {e : Effect l} {p₁ p₂ : Program ls (Mac l （）)} -> p₁ ⟼ p₂ ↑ e -> p₁ ⟼ p₂
stepOf (bullet s) = s
stepOf (fork p t s) = s
stepOf (none ¬f ¬∙ s) = s

redexOf : ∀ {ls l} {e : Effect l} {p₁ p₂ : Program ls (Mac l （）)} -> p₁ ⟼ p₂ ↑ e -> Redex (store p₁) (term p₁)
redexOf s = Step (stepOf s)

fork-⊑ : ∀ {ls l h} {p₁ p₂ : Program ls (Mac l （）)} {t : Thread h }  -> p₁ ⟼ p₂ ↑ fork t -> l ⊑ h
fork-⊑ (fork p t s) = p

--------------------------------------------------------------------------------

fork? : ∀ {l h} -> l ⊑ h ->  Thread h -> ℕ -> Event l
fork? p t n with is∙? t
fork? p t n | yes _ = Step
fork? p t n | no ¬p = Fork _ n p

-------------------------------------------------------------------------------
-- The global configuration is a thread pool paired with some shared split memory Σ
record Global (ls : List Label) : Set where
  constructor ⟨_,_,_⟩
  field state : State
  field storeᵍ : Store ls
  field pools : Pools ls

open Global
open import Relation.Binary.PropositionalEquality

state-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> state g₁ ≡ state g₂
state-≡ refl = refl

storeᵍ-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> storeᵍ g₁ ≡ storeᵍ g₂
storeᵍ-≡ refl = refl

pools-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> pools g₁ ≡ pools g₂
pools-≡ refl = refl

-- Concurrent semantics
data _,_⊢_↪_ {ls : List Label} (l : Label) (n : ℕ) : Global ls -> Global ls -> Set where

  -- Sequential step
  step : ∀ {s₁ s₂ } {t₁ t₂ : Thread l} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ : Pools ls} ->
  
            ps₁ [ l ][ n ]= t₁ ->
            
            ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ ∅ ->            
            s₁ ⟶ s₂ ↑ (l , n , Step) ->

            ps₂ ← ps₁ [ l ][ n ]≔ t₂ ->
            
          l , n ⊢ ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₂ ⟩

  -- A fork step spawns a new thread
  fork : ∀ {s₁ s₂ h nʰ} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ ps₃ : Pools ls} {t₁ t₂ : Thread l} {tʰ : Thread h} {tsʰ : Pool h nʰ} ->
           {{p : l ⊑ h}} ->
           
           ps₁ [ l ][ n ]= t₁ ->
           ps₁ [ h ]= tsʰ  ->
           
           ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ (fork tʰ) ->
           s₁ ⟶ s₂ ↑ (l , n , fork? p tʰ nʰ) ->

           ps₂ ← ps₁ [ l ][ n ]≔ t₂ ->
           ps₃ ← ps₂ [ h ]≔ (tsʰ ▻ tʰ) -> 
         
           l , n ⊢ ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₃ ⟩

  -- The pool at this level is collapsed, nothing to do.
  hole : ∀ {s} {Σ : Store ls} {ps : Pools ls} {t : Thread l} ->
  
         ps [ l ][ n ]= t ->
         ⟨ Σ ∥ t ⟩ ⟼ ⟨ Σ ∥ t ⟩ ↑ ∙ ->
         s ⟶ s ↑ (l , n , ∙) ->
         
         l , n ⊢ ⟨ s , Σ , ps ⟩ ↪ ⟨ s , Σ , ps ⟩

  -- Skip a blocked thread
  skip : ∀ {s₁ s₂} {Σ : Store ls} {ps : Pools ls} {t : Thread l} ->

          ps [ l ][ n ]= t ->
                         
          Stuck Σ t ->
          s₁ ⟶ s₂ ↑ (l , n , NoStep) ->
          l , n ⊢ ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Now we dot remove terminated threads anymore, so that all the indices are still valid.
  -- In the paper Σ changes in this rule. Why is that?
  exit : ∀ {s₁ s₂} {Σ : Store ls} {ps : Pools ls} {t : Thread l} ->

           ps [ l ][ n ]= t  ->

           IsValue t ->
           s₁ ⟶ s₂ ↑ (l , n , Done) ->
           l , n ⊢ ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 

  -- TODO do we need an event Done_Exit ? How would it be different from the current exit?
  -- Bear in mind that our transitions are always of the form ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

open import Data.Product hiding (_,_)

getEvent : ∀ {ls l n} {g₁ g₂ : Global ls} -> l , n ⊢ g₁ ↪ g₂ -> Event l
getEvent (step x x₁ x₂ x₃) = Step
getEvent (fork {nʰ = nʰ} {tʰ = tʰ} {{p}} x x₁ x₂ x₃ x₄ x₅) = fork? p tʰ nʰ
getEvent (hole x x₁ x₂) = ∙
getEvent (skip x x₁ x₂) = NoStep
getEvent (exit x x₁ x₂) = Done


getSchedulerStep : ∀ {ls l n} {g₁ g₂ : Global ls} -> (s : l , n ⊢ g₁ ↪ g₂) -> (state g₁) ⟶ (state g₂) ↑ (l , n , getEvent s)
getSchedulerStep (step x x₁ x₂ x₃) = x₂
getSchedulerStep (fork x x₁ x₂ x₃ x₄ x₅) = x₃
getSchedulerStep (hole x x₁ x₂) = x₂
getSchedulerStep (skip x x₁ x₂) = x₂
getSchedulerStep (exit x x₁ x₂) = x₂

open import Data.Product

-- Transitive closure of the concurrent small step
data _↪⋆_ {ls : List Label} : Global ls -> Global ls -> Set where

  -- Zero steps
  [] : ∀ {g} -> g ↪⋆ g 

  -- More steps
  _∷_ : ∀ {l n g₁ g₂ g₃} -> l , n ⊢ g₁ ↪ g₂ -> g₂ ↪⋆ g₃ -> g₁ ↪⋆ g₃


-- Concatenates two multiple steps reductions
_++ˢ_ : ∀ {ls} {g₁ g₂ g₃ : Global ls} -> g₁ ↪⋆ g₂ -> g₂ ↪⋆ g₃ -> g₁ ↪⋆ g₃
[] ++ˢ ss₂ = ss₂
(s ∷ ss₁) ++ˢ ss₂ = s ∷ (ss₁ ++ˢ ss₂)
