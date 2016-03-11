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
-- Extracting the current thread

data VIndex {l : Label} (t : Thread l) : ℕ -> Pool l -> Set where
  Here : ∀ {ts : Pool l} -> VIndex t zero (t ◅ ts)
  There : ∀ {n} {ts : Pool l} {t' : Thread l} -> VIndex t n ts -> VIndex t (suc n) (t' ◅ ts)

data LookupThread {l : Label} (t : Thread l) (n : ℕ) : ∀ {ls} -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {ps : Pools ls} {p : Pool l}  -> VIndex t n p -> LookupThread t n (p ◅ ps)
  There : ∀ {ls l'} {u : Unique l' ls} {p' : Pool l'} {ps : Pools ls} -> LookupThread t n ps -> LookupThread t n (p' ◅ ps)  

data LookupPool {l : Label} (p : Pool l) : ∀ {ls} -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {ps : Pools ls} -> LookupPool p (p ◅ ps)
  There : ∀ {l' ls} {u : Unique l' ls} {ps : Pools ls} {p' : Pool l'} -> LookupPool p ps -> LookupPool p (p' ◅ ps)

--------------------------------------------------------------------------------
-- Updates to the thread pools

data UpdateThread {l : Label} (t : Thread l) : ℕ -> Pool l -> Pool l -> Set where
  ∙ : ∀ {n} -> UpdateThread t n ∙ ∙
  new : UpdateThread t zero [] (t ◅ [])
  upd : ∀ {t₁ : Thread l} {ts : Pool l} -> UpdateThread t zero (t₁ ◅ ts) (t ◅ ts)
  skip : ∀ {n} {t' : Thread l} {ts₁ ts₂ : Pool l} -> UpdateThread t n ts₁ ts₂ -> UpdateThread t n (t' ◅ ts₁) (t' ◅ ts₂)
  
data UpdatePool {l : Label} (t : Thread l) (n : ℕ) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  Here : ∀ {ls} {u : Unique l ls} {p₁ p₂ : Pool l} {ps : Pools ls} -> UpdateThread t n p₁ p₂ -> UpdatePool t n (p₁ ◅ ps) (p₂ ◅ ps)
  There : ∀ {l' ls} {u : Unique l' ls} {ps₁ ps₂ : Pools ls} {p' : Pool l'} -> UpdatePool t n ps₁ ps₂ -> UpdatePool t n (p' ◅ ps₁) (p' ◅ ps₂)

--------------------------------------------------------------------------------

data NewThread {l : Label} (t : Thread l) : Pool l -> Pool l -> Set where
  newT : NewThread t [] (t ◅ [])
  skip : ∀ {ts₁ ts₂ : Pool l} {t' : Thread l} -> NewThread t ts₁ ts₂ -> NewThread t (t' ◅ ts₁) (t' ◅ ts₂)
  ∙ : NewThread t ∙ ∙
  
data NewPool {l : Label} (t : Thread l) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  this : ∀ {ls} {u : Unique l ls} {p₁ p₂ : Pool l} {ps : Pools ls} -> NewThread t p₁ p₂ -> NewPool t (p₁ ◅ ps) (p₂ ◅ ps)
  next : ∀ {l' ls} {u : Unique l' ls} {ps₁ ps₂ : Pools ls} {p' : Pool l'} -> NewPool t ps₁ ps₂ -> NewPool t (p' ◅ ps₁) (p' ◅ ps₂)

lengthᵗ : ∀ {l} -> Pool l -> ℕ
lengthᵗ [] = zero
lengthᵗ (x ◅ p) = suc (lengthᵗ p)
lengthᵗ ∙ = ∙

--------------------------------------------------------------------------------

-- The proof that a term is blocked
data Blocked {ls : List Label} (Σ : Store ls) : ∀ {τ} -> CTerm τ -> Set where
  onPut : ∀ {l n τ} {t : CTerm τ} -> (q : l ∈ ls) (r : TypedIx τ F n (getMemory q Σ)) -> Blocked Σ (putMVar (Res n) t)
  onTake : ∀ {l n τ} (q : l ∈ ls) (r : TypedIx τ E n (getMemory q Σ)) -> Blocked Σ (takeMVar {α = τ} (Res n))

--------------------------------------------------------------------------------
-- Syntactic sugar

_[_][_]=_ : ∀ {ls} -> Pools ls -> (l  : Label) -> ℕ -> Thread l -> Set
ps [ l ][ n ]= t = LookupThread t n ps

_[_]=_ : ∀ {ls} -> Pools ls -> (l : Label) -> Pool l -> Set
ps [ l ]= p = LookupPool p ps

_←_[_][_]≔_ : ∀ {ls} -> Pools ls -> Pools ls -> (l : Label) -> ℕ -> Thread l -> Set
ps₂ ← ps₁ [ l ][ n ]≔ t = UpdatePool t n ps₁ ps₂

_←_[_]∹_ : ∀ {ls} -> Pools ls -> Pools ls -> (h : Label) -> Thread h -> Set
ps₂ ← ps₁ [ h ]∹ tⁿ = NewPool tⁿ ps₁ ps₂ 

--------------------------------------------------------------------------------

-- Concurrent semantics
data _↪_ {ls : List Label} : Global ls -> Global ls -> Set where

  -- Sequential stop
  step : ∀ {s₁ s₂ l n} {t₁ t₂ : Thread l} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ : Pools ls} ->
  
            ps₁ [ l ][ n ]= t₁ ->
            
            ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ ∅ ->            
            s₁ ⟶ s₂ ↑ (l , n , Step) ->

            ps₂ ← ps₁ [ l ][ n ]≔ t₂ ->
            
          ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₂ ⟩

  -- A fork step spawns a new thread
  fork : ∀ {s₁ s₂ l h n} {Σ₁ Σ₂ : Store ls} {ps₁ ps₂ ps₃ : Pools ls} {t₁ t₂ : Thread l} {tⁿ : Thread h} {ts : Pool h} ->

           ps₁ [ l ][ n ]= t₁ ->
           ps₁ [ h ]= ts ->
           
           ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ (fork tⁿ) ->
           s₁ ⟶ s₂ ↑ (l , n , (Fork h (lengthᵗ ts))) ->

           ps₂ ← ps₁ [ l ][ n ]≔ t₂ ->
           ps₃ ← ps₂ [ h ][ lengthᵗ ts ]≔ tⁿ ->
         
           ⟨ s₁ , Σ₁ , ps₁ ⟩ ↪ ⟨ s₂ , Σ₂ , ps₃ ⟩

  -- For this we need a particular proof that says that given l and n the pool at l is ‌∙
  -- The pool at this level is collapsed, nothing to do.
  -- TODO I am not sure about which event should be generated here.
  hole : ∀ {s₁ s₂ e l n} {Σ : Store ls} {ps : Pools ls} ->
         ps [ l ]= ∙ ->
         s₁ ⟶ s₂ ↑ (l , n , e) ->
         ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Skip a blocked thread
  skip : ∀ {l n s₁ s₂} {Σ : Store ls} {t : Thread l} {ps : Pools ls} ->
          ps [ l ][ n ]= t ->
          Blocked Σ t ->
          s₁ ⟶ s₂ ↑ (l , n , NoStep) ->
          ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩

  -- Now we don't remove terminated threads anymore, so that all the indices are still valid.
  -- In the paper Σ changes in this rule. Why is that?
  exit : ∀ {l n s₁ s₂} {Σ : Store ls} {t : Thread l} {ps : Pools ls} ->
           ps [ l ][ n ]= t -> 
           IsValue t ->
           s₁ ⟶ s₂ ↑ (l , n , Done) ->
           ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 

  -- TODO do we need an event Done_Exit ? How would it be different from the current exit?
  -- Bear in mind that our transitions are always of the form ⟨ s₁ , Σ , ps ⟩ ↪ ⟨ s₂ , Σ , ps ⟩ 
