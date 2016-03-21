open import Typed.Communication


-- TODO pack everything scheduler related in a single record called Scheduler
module Typed.Concurrent (State : Set) (_⟶_↑_ :  State -> State -> Message -> Set) where

open import Data.List
open import Typed.Base
open import Typed.Semantics

--------------------------------------------------------------------------------
-- The global configuration is a thread pool paired with some shared split memory Σ
data Global (ls : List Label) : Set where
  ⟨_,_,_⟩ : State -> (Σ : Store ls) -> (ps : Pools ls) -> Global ls
  
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
-- TODO remove!
-- Allocate new thread in a pool

data NewThread {l : Label} (t : Thread l) : ∀ {n} -> Pool l n -> Pool l (suc n) -> Set where
  ∙ : ∀ {n} -> NewThread t (∙ {n = n}) ∙
  newT : NewThread t [] (t ◅ [])
  skip : ∀ {n} {ts₁ : Pool l n} {ts₂ : Pool l (suc n)} {t' : Thread l} -> NewThread t ts₁ ts₂ -> NewThread t (t' ◅ ts₁) (t' ◅ ts₂)

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

-- Concurrent semantics
data _↪_ {ls : List Label} : Global ls -> Global ls -> Set where

  -- Sequential stop
  step : ∀ {s₁ s₂ l n n'} {t₁ t₂ : Thread l} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ : Pools ls} {ts₁ ts₂ : Pool l n'} ->
  
            ps₁ [ l ]= ts₁ ->
            ts₁ [ n ]ᵗ= t₁ ->
            
            ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ ∅ ->            
            s₁ ⟶ s₂ ↑ (l , n , Step) ->

            ts₂ ← ts₁ [ n ]ᵗ≔ t₂ ->
            ps₂ ← ps₁ [ l ]≔ ts₂ ->
            
          ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₂ ⟩

  -- A fork step spawns a new thread
  fork : ∀ {s₁ s₂ l h n n' nʰ} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ ps₃ : Pools ls} {ts₁ ts₂ : Pool l n'} {tsʰ : Pool h nʰ} {t₁ t₂ : Thread l} {tʰ : Thread h} ->
           
           ps₁ [ l ]= ts₁ ->
           ts₁ [ n ]ᵗ= t₁ ->
           ps₁ [ h ]= tsʰ ->
           
           ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ (fork tʰ) ->
           s₁ ⟶ s₂ ↑ (l , n , (Fork h nʰ)) ->

           ts₂ ← ts₁ [ n ]ᵗ≔ t₂ ->
           ps₂ ← ps₁ [ l ]≔ ts₂ ->
           ps₃ ← ps₂ [ h ]≔ (tsʰ ▻ tʰ) -> 
         
           ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₃ ⟩

  -- For this we need a particular proof that says that given l and n the pool at l is ‌∙
  -- The pool at this level is collapsed, nothing to do.
  -- TODO I am not sure about which event should be generated here.
  hole : ∀ {s₁ s₂ e l n n'} {Σ : Store ls} {ps : Pools ls} ->
         ps [ l ]= (∙ {n = n'}) ->
         s₁ ⟶ s₂ ↑ (l , n , e) ->
         ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Skip a blocked thread
  skip : ∀ {l n n' s₁ s₂} {Σ : Store ls} {ps : Pools ls} {ts : Pool l n'} {t : Thread l} ->
          ps [ l ]= ts ->
          ts [ n ]ᵗ= t ->

          Blocked Σ t ->
          s₁ ⟶ s₂ ↑ (l , n , NoStep) ->
          ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Now we don't remove terminated threads anymore, so that all the indices are still valid.
  -- In the paper Σ changes in this rule. Why is that?
  exit : ∀ {l n n' s₁ s₂} {Σ : Store ls} {ps : Pools ls} {ts : Pool l n'} {t : Thread l} ->

           ps [ l ]= ts ->
           ts [ n ]ᵗ= t ->

           IsValue t ->
           s₁ ⟶ s₂ ↑ (l , n , Done) ->
           ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 

  -- TODO do we need an event Done_Exit ? How would it be different from the current exit?
  -- Bear in mind that our transitions are always of the form ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 
