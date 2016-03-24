open import Concurrent.Communication
open import Concurrent.Calculus public


-- TODO pack everything scheduler related in a single record called Scheduler
module Concurrent.Semantics (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set) where

open import Data.Nat
open import Data.List
open import Sequential.Semantics

--------------------------------------------------------------------------------
-- Lookup threads and thread pools

data LookupThread {l : Label} (t : Thread l) : ∀ {n} -> ℕ -> Pool l n -> Set where
  Here : ∀ {n} {ts : Pool l n} -> LookupThread t zero (t ◅ ts)
  There : ∀ {n₁ n₂} {ts : Pool l n₂} {t' : Thread l} -> LookupThread t n₁ ts -> LookupThread t (suc n₁) (t' ◅ ts)

data LookupPool {l : Label} {n : ℕ} (p : Pool l n) : ∀ {ls} -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {ps : Pools ls} -> LookupPool p (p ◅ ps)
  There : ∀ {l' n' ls} {u : Unique l' ls} {ps : Pools ls} {p' : Pool l' n'} -> LookupPool p ps -> LookupPool p (p' ◅ ps)

--------------------------------------------------------------------------------
-- Updates threads and thread pools

data UpdateThread {l : Label} (t : Thread l) : ∀ {n} -> ℕ -> Pool l n -> Pool l n -> Set where
  ∙ : ∀ {n} -> UpdateThread t n (∙ {n = n}) ∙
  upd : ∀ {n} {ts : Pool l n} {t₁ : Thread l} -> UpdateThread t zero (t₁ ◅ ts) (t ◅ ts)
  skip : ∀ {n} {ts₁ ts₂ : Pool l n} {t' : Thread l} -> UpdateThread t n ts₁ ts₂ -> UpdateThread t (suc n) (t' ◅ ts₁) (t' ◅ ts₂)

data UpdatePool {l : Label} {n : ℕ} (p₂ : Pool l n) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {p₁ : Pool l n} {ps : Pools ls} -> UpdatePool p₂ (p₁ ◅ ps) (p₂ ◅ ps)
  There : ∀ {l' n' ls} {u : Unique l' ls} {ps₁ ps₂ : Pools ls} {p' : Pool l' n'} -> UpdatePool p₂ ps₁ ps₂ -> UpdatePool p₂ (p' ◅ ps₁) (p' ◅ ps₂)

--------------------------------------------------------------------------------

-- The proof that a term is blocked
data Blocked {ls : List Label} (Σ : Store ls) : ∀ {τ} -> CTerm τ -> Set where
  onPut : ∀ {l n τ} {t : CTerm τ} -> (q : l ∈ ls) (r : TypedIx τ F n (getMemory q Σ)) -> Blocked Σ (putMVar (Res n) t)
  onTake : ∀ {l n τ} (q : l ∈ ls) (r : TypedIx τ E n (getMemory q Σ)) -> Blocked Σ (takeMVar {α = τ} (Res n))

--------------------------------------------------------------------------------
-- Syntactic sugar

_[_]=_ : ∀ {ls n} -> Pools ls -> (l : Label) -> Pool l n -> Set
ps [ l ]= p = LookupPool p ps

_←_[_]≔_ : ∀ {ls n} -> Pools ls -> Pools ls -> (l : Label) -> Pool l n -> Set
ps₂ ← ps₁ [ l ]≔ p  = UpdatePool p ps₁ ps₂


_[_]ᵗ=_ : ∀ {l n} -> Pool l n -> ℕ -> Thread l -> Set
ts [ n ]ᵗ= t = LookupThread t n ts

_←_[_]ᵗ≔_ : ∀ {l n} -> Pool l n -> Pool l n -> ℕ -> Thread l -> Set
ts₂ ← ts₁ [ n ]ᵗ≔ t = UpdateThread t n ts₁ ts₂

--------------------------------------------------------------------------------

-- Effect triggered in the sequential setting
data Effect : Set where
  ∅ : Effect
  fork : ∀ {l} -> Thread l -> Effect

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

data _⟼_↑_ {ls : List Label} : ∀ {τ} (p₁ p₂ : Program ls τ) -> Effect -> Set where
  fork : ∀ {l h} {p₂ : Program ls (Mac l （）)} {Σ : Store ls} ->
         (p : l ⊑ h) (t : Thread h) (s : ⟨ Σ ∥ fork p t ⟩ ⟼ p₂) -> ⟨ Σ ∥ fork p t ⟩ ⟼ p₂ ↑ (fork t)
  none : ∀ {τ} {p₁ p₂ : Program ls τ} -> ¬ IsFork (term p₁) -> p₁ ⟼ p₂ -> p₁ ⟼ p₂ ↑ ∅ 

stepOf : ∀ {ls τ e} {p₁ p₂ : Program ls τ} -> p₁ ⟼ p₂ ↑ e -> p₁ ⟼ p₂
stepOf (fork p t s) = s
stepOf (none ¬f s) = s

fork-⊑ : ∀ {ls τ l h} {p₁ p₂ : Program ls (Mac l τ)} {t : Thread h }  -> p₁ ⟼ p₂ ↑ fork t -> l ⊑ h
fork-⊑ (fork p t s) = p

--------------------------------------------------------------------------------

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

fork? : ∀ {h} -> Thread h -> ℕ -> Event 
fork? t n with is∙? t
fork? t n | yes p = Step
fork? {h} t n | no ¬p = Fork h n

-------------------------------------------------------------------------------
-- The global configuration is a thread pool paired with some shared split memory Σ
data Global (ls : List Label) : Set where
  ⟨_,_,_⟩ : State -> (Σ : Store ls) -> (ps : Pools ls) -> Global ls
 

-- Concurrent semantics
data _,_⊢_↪_ {ls : List Label} (l : Label) (n : ℕ) : Global ls -> Global ls -> Set where

  -- Sequential stop
  step : ∀ {s₁ s₂ n'} {t₁ t₂ : Thread l} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n'} ->
  
            ps₁ [ l ]= ts₁ ->
            ts₁ [ n ]ᵗ= t₁ ->
            
            ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ ∅ ->            
            s₁ ⟶ s₂ ↑ (l , n , Step) ->

            ts₂ ← ts₁ [ n ]ᵗ≔ t₂ ->
            ps₂ ← ps₁ [ l ]≔ ts₂ ->
            
          l , n ⊢ ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₂ ⟩

  -- A fork step spawns a new thread
  fork : ∀ {s₁ s₂ h n' nʰ} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ ps₃ : Pools ls} {ts₁ ts₂ : Pool l n'} {tsʰ : Pool h nʰ} {t₁ t₂ : Thread l} {tʰ : Thread h} ->
         
           ps₁ [ l ]= ts₁ ->
           ts₁ [ n ]ᵗ= t₁ ->
           ps₁ [ h ]= tsʰ ->
           
           ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ (fork tʰ) ->
           s₁ ⟶ s₂ ↑ (l , n , fork? tʰ nʰ) ->

           ts₂ ← ts₁ [ n ]ᵗ≔ t₂ ->
           ps₂ ← ps₁ [ l ]≔ ts₂ ->
           ps₃ ← ps₂ [ h ]≔ (tsʰ ▻ tʰ) -> 
         
           l , n ⊢ ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₃ ⟩

  -- The pool at this level is collapsed, nothing to do.
  hole : ∀ {s n'} {Σ : Store ls} {ps : Pools ls} ->
         ps [ l ]= (∙ {n = n'}) ->
         s ⟶ s ↑ (l , n , ∙) ->
         l , n ⊢ ⟨ s , Σ , ps ⟩ ↪ ⟨ s , Σ , ps ⟩

  -- Skip a blocked thread
  skip : ∀ {n' s₁ s₂} {Σ : Store ls} {ps : Pools ls} {ts : Pool l n'} {t : Thread l} ->
          ps [ l ]= ts ->
          ts [ n ]ᵗ= t ->

          Blocked Σ t ->
          s₁ ⟶ s₂ ↑ (l , n , NoStep) ->
          l , n ⊢ ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Now we don't remove terminated threads anymore, so that all the indices are still valid.
  -- In the paper Σ changes in this rule. Why is that?
  exit : ∀ {n' s₁ s₂} {Σ : Store ls} {ps : Pools ls} {ts : Pool l n'} {t : Thread l} ->

           ps [ l ]= ts  ->
           ts [ n ]ᵗ= t ->

           IsValue t ->
           s₁ ⟶ s₂ ↑ (l , n , Done) ->
           l , n ⊢ ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 

  -- TODO do we need an event Done_Exit ? How would it be different from the current exit?
  -- Bear in mind that our transitions are always of the form ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩
