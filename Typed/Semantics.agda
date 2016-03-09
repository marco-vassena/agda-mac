module Typed.Semantics where

open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Typed.Base public
import Data.List as L
open import Data.List.All

data _⇝_ : ∀ {τ} -> CTerm τ -> CTerm τ -> Set where

  -- Reduces the function in an application
  AppL : ∀ {α β} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} -> c₁ ⇝ c₂ -> App c₁ x ⇝ App c₂ x

  -- Pushes a term in the environment
  Beta : ∀ {α β} {t : Term (α ∷ []) β} {x : CTerm α} -> App (Abs t) x ⇝ subst x t

  IfCond : ∀ {τ} {c c' : CTerm Bool} {t e : CTerm τ} -> c ⇝ c' ->
             (If c Then t Else e) ⇝ (If c' Then t Else e)

  IfTrue : ∀ {τ} {t e : CTerm τ} -> (If True Then t Else e) ⇝ t

  IfFalse : ∀ {τ} {t e : CTerm τ} -> (If False Then t Else e) ⇝ e

  Return : ∀ {τ} {l : Label} {t : CTerm τ} -> Return t ⇝ Mac t

  Throw : ∀ {l : Label}  {α : Ty} {e : CTerm Exception} -> Throw {{l}} {{α}} e ⇝ Macₓ e 

  Bind : ∀ {l α β} {t : CTerm α} {k : CTerm (α => Mac l β)} -> (Mac t >>= k) ⇝ App k t

  BindEx : ∀ {l α β} {e : CTerm Exception} {k : CTerm (α => Mac l β)} -> (Macₓ e >>= k) ⇝ Throw e

  Catch : ∀ {l : Label} {α : Ty} {t : CTerm α} {h : CTerm (Exception => Mac l α)} ->
            Catch (Mac t) h ⇝ (Return t)

  CatchEx : ∀ {l : Label} {α : Ty} {e : CTerm Exception} {h : CTerm (Exception => Mac l α)} ->
              Catch (Macₓ e) h ⇝ App h e

  label : ∀ {l h α} {t : CTerm α} -> (p : l ⊑ h) -> label p t ⇝ Return (Res t)

  unlabel : ∀ {l h α} {t : CTerm α} -> (p : l ⊑ h) -> unlabel p (Res t) ⇝ Return t

  unlabelEx : ∀ {l h α} {e : CTerm Exception} -> (p : l ⊑ h) -> unlabel {α = α} p (Resₓ e) ⇝  Throw e

  -- To make Res a secure functor we need a more strict semantics.
  -- In particular to have distributivity we need a strict function application, but interestingly
  -- we need strictness in the function also for Resₓ.
  fmapCtx₁ : ∀ {l α β} {f₁ f₂ : CTerm (α => β)} {x : CTerm α} -> f₁ ⇝ f₂ -> fmap f₁ (Res x) ⇝ fmap f₂ (Res x)

  fmapCtx₂ : ∀ {l α β} {t : Term (α ∷ []) β} {x₁ x₂ : CTerm (Res l α)} -> x₁ ⇝ x₂ -> fmap (Abs t) x₁ ⇝ fmap (Abs t) x₂

  fmap : ∀ {l α β} {t : Term (α ∷ []) β} {x : CTerm α} -> fmap (Abs t) (Res x) ⇝ (Res (subst x t))

  fmapEx : ∀ {l α β} {t : Term (α ∷ []) β} {e : CTerm Exception} -> fmap (Abs t) (Resₓ {{l}} e) ⇝ (Resₓ e)

  fmapCtx₁∙ : ∀ {l α β} {f₁ f₂ : CTerm (α => β)} {x : CTerm (Res l α)} -> f₁ ⇝ f₂ -> fmap∙ f₁ x ⇝ fmap∙ f₂ x    

  fmapCtx₂∙ : ∀ {l α β} {t : Term (α ∷ [])  β} {x₁ x₂ : CTerm (Res l α)} -> x₁ ⇝ x₂ -> fmap∙ (Abs t) x₁ ⇝ fmap∙ (Abs t) x₂

  fmap∙ : ∀ {l α β} {t : Term (α ∷ []) β} {x : CTerm α} -> fmap∙ (Abs t) (Res x) ⇝ (Res ∙)

  fmapEx∙ : ∀ {l α β} {t : Term (α ∷ []) β} {e : CTerm Exception} -> fmap∙ (Abs t) (Resₓ {{l}} e) ⇝ (Res ∙)

  -- Bullet reduces to itself. We need this rule because ∙ is not a value.
  Hole : ∀ {τ : Ty} -> (∙ {{τ}}) ⇝ ∙

  relabelCtx : ∀ {l h α} {c₁ c₂ : CTerm (Res l α)} -> (p : l ⊑ h) -> c₁ ⇝ c₂ -> relabel p c₁ ⇝ relabel p c₂

  relabel : ∀ {l h α} {t : CTerm α} -> (p : l ⊑ h) -> relabel p (Res t) ⇝ Res t

  relabelEx : ∀ {l h α} {e : CTerm Exception} -> (p : l ⊑ h) -> relabel {α = α} p (Resₓ e) ⇝ Resₓ e

  relabelCtx∙ : ∀ {l h α} {c₁ c₂ : CTerm (Res l α)} -> (p : l ⊑ h) -> c₁ ⇝ c₂ -> relabel∙ p c₁ ⇝ relabel∙ p c₂

  relabel∙ : ∀ {l h α} {c : CTerm α} -> (p : l ⊑ h) -> relabel∙ p (Res c) ⇝ Res ∙ 

  relabelEx∙ : ∀ {l h α} {c : CTerm Exception} -> (p : l ⊑ h) -> relabel∙ {α = α} p (Resₓ c) ⇝ Res ∙ 

mutual
  infixr 1 _⟼_

  -- The transitive reflexive closure of the small step relation
  data _⟼⋆_ {ls : List Label} {τ : Ty} : Program ls τ -> Program ls τ -> Set where
    [] : {s : Store ls} {c : CTerm τ} -> ⟨ s ∥ c ⟩  ⟼⋆ ⟨ s ∥ c ⟩
    _∷_ : {s₁ s₂ s₃ : Store ls} {c₁ c₂ c₃ : CTerm τ} ->
          ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> ⟨ s₂ ∥ c₂ ⟩ ⟼⋆ ⟨ s₃ ∥ c₃ ⟩ -> ⟨ s₁ ∥ c₁ ⟩ ⟼⋆ ⟨ s₃ ∥ c₃ ⟩

  -- A big step is made of a finite number (possibly 0) of reduction steps that reduces a term to a value.
  data _⇓_ {ls : List Label} {τ : Ty} : Program ls τ -> Program ls τ -> Set where
    BigStep : ∀ {s₁ s₂ : Store ls} {c v : CTerm τ} -> IsValue v -> ⟨ s₁ ∥ c ⟩ ⟼⋆ ⟨ s₂ ∥ v ⟩ -> ⟨ s₁ ∥ c ⟩ ⇓ ⟨ s₂ ∥ v ⟩

  -- Small step semantics of programs
  data _⟼_ {ls : List Label} : ∀ {τ} -> Program ls τ -> Program ls τ -> Set where
    Pure : ∀ {τ} {s₁ : Store ls} {c₁ c₂ : CTerm τ} -> c₁ ⇝ c₂ -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₁ ∥ c₂ ⟩

    BindCtx : ∀ {l α β} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Mac l α)} {k : CTerm (α => Mac l β)} ->
                ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
                ⟨ s₁  ∥  c₁ >>= k ⟩ ⟼ ⟨ s₂ ∥ c₂ >>= k ⟩ 

    CatchCtx : ∀ {l α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Mac l α)} {h : CTerm (Exception => Mac l α)} ->
                 ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
                 ⟨ s₁ ∥ Catch c₁ h ⟩ ⟼ ⟨ s₂ ∥ Catch c₂ h ⟩

    unlabelCtx : ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Res l α)} -> (p : l ⊑ h) ->
                   ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
                   ⟨ s₁ ∥ unlabel p c₁ ⟩ ⟼ ⟨ s₂ ∥ unlabel p c₂ ⟩
                 
    join : ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls}  {c : CTerm (Mac h α)} {t : CTerm α} (p : l ⊑ h) ->
             ⟨ s₁ ∥ c ⟩ ⇓ ⟨ s₂ ∥  Mac t ⟩ ->
             ⟨ s₁ ∥ join p c ⟩ ⟼ ⟨ s₂ ∥ (Return (Res t)) ⟩

    joinEx : ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c : CTerm (Mac h α)} {e : CTerm Exception} (p : l ⊑ h) ->
               ⟨ s₁ ∥ c ⟩ ⇓ ⟨ s₂ ∥  Macₓ e ⟩ ->
               ⟨ s₁ ∥ join p c ⟩ ⟼ ⟨ s₂ ∥ (Return (Resₓ e)) ⟩

    -- In this rule we don't actually compute the proper reference but we just assume that is there and points
    -- to a fresh location. Unfortunately computing the reference in the rule makes the types too complex for reasoning.
    new : ∀ {l h α} {s : Store ls} {t : CTerm α} -> (p : l ⊑ h) (q : h ∈ ls) ->
               ⟨ s ∥ new p t ⟩ ⟼ ⟨ newˢ q s ⟦ t ⟧ ∥ Return (lengthᵐ (getMemory q s)) ⟩

    writeCtx :  ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Ref h α)} {c₃ : CTerm α} ->
                  (p : l ⊑ h) -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
                  ⟨ s₁ ∥ write p c₁ c₃ ⟩ ⟼ ⟨ s₂ ∥ write p c₂ c₃  ⟩

    write : ∀ {l h α} {s : Store ls} {n : CTerm Nat} {c : CTerm α} -> (p : l ⊑ h) (q : h ∈ ls) (r : TypedIx α F n (getMemory q s)) ->
              ⟨ s ∥ write p (Res n) c ⟩ ⟼ ⟨ s [ q ][ r ]≔ ⟦ c ⟧ ∥ Return （） ⟩

    -- We need the proof h ∈ ls in distributivity, when erased the exception is silently ignored, the write rule applies.
    -- The write is harmless because Memory h is collpased to ∙, but to perform that operation I still need the proof h ∈ ls and  TypedIx τ n (getMemory q s)
    -- Furhtermore agda gives several problems in that proof if I explicitly use the same store s.
    -- One thing is that rewriting fails. The second problem is that not only the second store would be rewritten as s [ q ][ r ]≔ c, but also the first
    -- thus preventing to apply the rule write.
    writeEx : ∀ {l h α n} {s : Store ls} {c : CTerm α} {e : CTerm Exception} ->
              (p : l ⊑ h) (q : h ∈ ls) (r : TypedIx α F n (getMemory q s)) ->
              ⟨ s ∥ write p (Resₓ e) c ⟩ ⟼ ⟨ s ∥ Return （） ⟩

    readCtx : ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Ref l α)} -> (p : l ⊑ h) ->
              ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
              ⟨ s₁ ∥ (read {α = α} p c₁) ⟩ ⟼ ⟨ s₂ ∥ (read p c₂) ⟩

    read : ∀ {l h α n} {s : Store ls} -> (p : l ⊑ h) (q : l ∈ ls) -> (r : TypedIx α F n (getMemory q s)) ->
              ⟨ s ∥ (read p (Res n)) ⟩ ⟼ ⟨ s ∥ unlabel p (s [ q ][ r ]) ⟩

    readEx : ∀ {l h α} {s : Store ls} {e : CTerm Exception} -> (p : l ⊑ h) ->
              ⟨ s ∥ (read {α = α} p (Resₓ e)) ⟩ ⟼ ⟨ s ∥ Throw e ⟩

    fork : ∀ {l h} {Σ : Store ls} -> (p : l ⊑ h) (t : CTerm (Mac h （）)) ->  ⟨ Σ ∥ fork p t ⟩ ⟼ ⟨ Σ ∥ (Return （）) ⟩

    -- This is repeating the new rule. If we actually separate Mac from IO we can reuse that as it actually happens
    newMVar : ∀ {l h τ} {Σ : Store ls} -> (p : l ⊑ h) (q : h ∈ ls) -> ⟨ Σ ∥ newMVar {α = τ} p ⟩ ⟼ ⟨ newˢ {τ = τ} q Σ ⊞ ∥ (Return (lengthᵐ (getMemory q Σ))) ⟩

    putMVarCtx :  ∀ {l α} {Σ₁ Σ₂ : Store ls} {c₁ c₂ : CTerm (MVar l α)} {c₃ : CTerm α} ->
                  ⟨ Σ₁ ∥ c₁ ⟩ ⟼ ⟨ Σ₂ ∥ c₂ ⟩ ->
                  ⟨ Σ₁ ∥ putMVar c₁ c₃ ⟩ ⟼ ⟨ Σ₂ ∥ putMVar c₂ c₃  ⟩

    -- Deciding whether r points to E or F is a read operation!!!
    putMVar : ∀ {l τ n} {Σ : Store ls} {t : CTerm τ} -> (q : l ∈ ls) (r : TypedIx τ E n (getMemory q Σ)) ->
               ⟨ Σ ∥ putMVar (Res n) t ⟩ ⟼ ⟨ Σ [ q ][ r ]≔ ⟦ t ⟧ ∥ Return （） ⟩
              
    putMVarEx : ∀ {l τ} {Σ : Store ls} {e : CTerm Exception} {t : CTerm τ} -> ⟨ Σ ∥ putMVar {l = l} (Resₓ e) t ⟩ ⟼ ⟨ Σ ∥ Throw e ⟩

    takeMVarCtx :  ∀ {l α} {Σ₁ Σ₂ : Store ls} {c₁ c₂ : CTerm (MVar l α)} ->
                  ⟨ Σ₁ ∥ c₁ ⟩ ⟼ ⟨ Σ₂ ∥ c₂ ⟩ ->
                  ⟨ Σ₁ ∥ takeMVar {α = α} c₁ ⟩ ⟼ ⟨ Σ₂ ∥ takeMVar c₂ ⟩
                  
    -- Deciding whether r points to E or F is a read operation!!!
    takeMVar : ∀ {l : Label} {τ : Ty} {n : CTerm Nat} {Σ : Store ls} -> (q : l ∈ ls) (r : TypedIx τ F n (getMemory q Σ)) ->
               ⟨ Σ ∥ takeMVar {α = τ}  (Res n) ⟩ ⟼ ⟨ Σ ∥  unlabel refl-⊑ (Σ [ q ][ r ]) ⟩
              
    takeMVarEx : ∀ {l τ} {Σ : Store ls} {e : CTerm Exception} -> ⟨ Σ ∥ takeMVar {α = τ} (Resₓ e) ⟩ ⟼ ⟨ Σ ∥ Throw e ⟩

  -- A program is a Redex if it can be reduced further in a certain memory configuration
  data Redex {ls : List Label} {τ : Ty} (s₁ : Store ls) (c₁ : CTerm τ) : Set where
    Step : {s₂ : Store ls} {c₂ : CTerm τ} -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> Redex s₁ c₁

  -- Normal forms
  -- A closed term is in normal form for a given store configuration if it cannot be reduced further
  NormalForm : ∀ {ls τ} -> Store ls -> CTerm τ -> Set
  NormalForm s₁ c = ¬ Redex s₁ c

--------------------------------------------------------------------------------

-- TODO move to Typed.Base
Thread : Label -> Set
Thread l = CTerm (Mac l （）)

-- Events triggered
data Event : Set where
  ∅ : Event
  fork : ∀ {l} -> Thread l -> Event

--------------------------------------------------------------------------------
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

data _⟼_↑_ {ls : List Label} : ∀ {τ} (p₁ p₂ : Program ls τ) -> Event -> Set where
  fork : ∀ {l h} {p₂ : Program ls (Mac l （）)} {Σ : Store ls} ->
         (p : l ⊑ h) (t : Thread h) (s : ⟨ Σ ∥ fork p t ⟩ ⟼ p₂) -> ⟨ Σ ∥ fork p t ⟩ ⟼ p₂ ↑ (fork t)
  none : ∀ {τ} {p₁ p₂ : Program ls τ} -> ¬ IsFork (term p₁) -> p₁ ⟼ p₂ -> p₁ ⟼ p₂ ↑ ∅ 

stepOf : ∀ {ls τ e} {p₁ p₂ : Program ls τ} -> p₁ ⟼ p₂ ↑ e -> p₁ ⟼ p₂
stepOf (fork p t s) = s
stepOf (none ¬f s) = s

-- Pool of threads at a certain label
data Pool (l : Label) : Set where
  [] : Pool l
  _◅_ : Thread l -> Pool l -> Pool l
  ∙ : Pool l

infixr 3 _◅_

-- A list of pools 
data Pools : List Label -> Set where
  [] : Pools []
  _◅_ : ∀ {l ls} {{u : Unique l ls}} -> Pool l -> Pools ls -> Pools (l ∷ ls)

-- The global configuration is a thread pool  paired with some shared split memory Σ
data Global (ls : List Label) : Set where
  ⟨_,_,_⟩ :  ℕ -> (Σ : Store ls) -> (ps : Pools ls) -> Global ls
  
-- Enqueue
_▻_ : ∀ {l} -> Pool l -> Thread l -> Pool l
[] ▻ t = t ◅ []
(x ◅ ts) ▻ t = x ◅ (ts ▻ t) 
∙ ▻ t = ∙

infixl 3 _▻_

-- We this data type we don't neet to actually perform a read and constraint
-- somehow the pool that it returns (empty/bullet/non-empty)
-- TODO if we are using numbers for injectivity then we probably don't need the uniqueness proofs in Pools
data PoolView {l : Label} (p : Pool l) : ∀ {ls} -> Pools ls -> ℕ ->  Set where
  Here : ∀ {ls n} {ps : Pools ls}  -> PoolView p ps (suc n)
  There : ∀ {ls n l'} {u : Unique l' ls} {p' : Pool l'} {ps : Pools ls} -> PoolView p ps n -> PoolView p (p' ◅ ps) (suc n)

-- write in pools
update : ∀ {l ls} -> l ∈ ls -> Pools ls -> Pool l -> Pools ls
update Here (x ◅ ps) p = p ◅ ps
update (There q) (p₁ ◅ ps) p₂ = p₁ ◅ update q ps p₂

-- TODO remove
-- Even more precise than write maybe better!
-- This does not work because the current thread has been reduced 
rotate : ∀ {l ls} -> l ∈ ls -> Pools ls -> Pools ls
rotate Here ([] ◅ ps) = [] ◅ ps
rotate Here ((t ◅ p) ◅ ps) = (p ▻ t) ◅ ps
rotate Here (∙ ◅ ps) = ∙ ◅ ps
rotate (There q) (p ◅ ps) = p ◅ (rotate q ps)

forkInPool : ∀ {l ls} -> Thread l -> l ∈ ls -> Pools ls -> Pools ls
forkInPool t Here (p ◅ ps) = (p ▻ t) ◅ ps
forkInPool t (There q) (p ◅ ps) = p ◅ forkInPool t q ps

-- -- Combine fork and update in a single operation
-- forkAndUpdate : ∀ {l h ls} -> l ∈ ls -> h ∈ ls -> Pools ls -> Pool l -> Thread h -> Pools ls
-- forkAndUpdate Here Here (_ ◅ ps) ts t = (ts ▻ t) ◅ ps
-- forkAndUpdate Here (There r) (x ◅ ps) p t = {!!}
-- forkAndUpdate (There q) Here (x ◅ ps) p t = {!!}
-- forkAndUpdate (There q) (There r) (x ◅ ps) p t = {!!}

-- The proof that a term is blocked
data Blocked {ls : List Label} (Σ : Store ls) : ∀ {τ} -> CTerm τ -> Set where
  onPut : ∀ {l n τ} {t : CTerm τ} -> (q : l ∈ ls) (r : TypedIx τ F n (getMemory q Σ)) -> Blocked Σ (putMVar (Res n) t)
  onTake : ∀ {l n τ} (q : l ∈ ls) (r : TypedIx τ E n (getMemory q Σ)) -> Blocked Σ (takeMVar {α = τ} (Res n))

-- Semantics for a thread pool at a certain level
data _↪_ {ls : List Label} : Global ls -> Global ls -> Set where

  -- Sequential stop
  step : ∀ {l n} {t₁ t₂ : Thread l} {ts : Pool l} {Σ₁ Σ₂ : Store ls} {ps : Pools ls} ->
          ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ ∅ -> (q : l ∈ ls) -> PoolView (t₁ ◅ ts) ps (suc n) -> 
          ⟨ suc n , Σ₁ , ps ⟩ ↪ ⟨ n , Σ₂ , update q ps (ts ▻ t₂ ) ⟩

  fork : ∀ {l h n} {Σ₁ Σ₂ : Store ls} {t₁ t₂ : Thread l} {tⁿ : Thread h} {ts : Pool l} {ps : Pools ls} ->
           ⟨ Σ₁ ∥ t₁ ⟩ ⟼ ⟨ Σ₂ ∥ t₂ ⟩ ↑ (fork tⁿ) -> (q : l ∈ ls) (r : h ∈ ls) -> PoolView (t₁ ◅ ts) ps (suc n) ->
           ⟨ suc n , Σ₁ , ps ⟩ ↪ ⟨ n , Σ₂ , update q (forkInPool tⁿ r ps) (ts ▻ t₂) ⟩ 

  empty : ∀ {l n} {Σ : Store ls} {ps : Pools ls} -> PoolView {l} [] ps (suc n) -> ⟨ suc n , Σ , ps ⟩ ↪ ⟨ n , Σ , ps ⟩

  hole : ∀ {l n} {Σ : Store ls} {ps : Pools ls} -> PoolView {l} ∙ ps (suc n) -> ⟨ suc n , Σ , ps ⟩ ↪ ⟨ n , Σ , ps ⟩

  -- Skip a blocked thread
  skip : ∀ {l n} {Σ : Store ls} {t : Thread l} {ts : Pool l} {ps : Pools ls} -> (q : l ∈ ls) -> PoolView (t ◅ ts) ps (suc n) -> 
          Blocked Σ t -> ⟨ suc n , Σ , ps ⟩ ↪ ⟨ n , Σ , update q ps (ts ▻ t) ⟩ 

  -- In the paper Σ changes in this rule. Why is that?
  exit : ∀ {l n} {Σ : Store ls} {t : Thread l} {ts : Pool l} {ps : Pools ls} -> (q : l ∈ ls) -> PoolView (t ◅ ts) ps (suc n) ->
           IsValue t ->  ⟨ suc n , Σ , ps ⟩ ↪ ⟨ n , Σ ,  update q ps ts ⟩

  -- restart the counter (I am assuming ps ≠ [])
  cycle : ∀ {Σ : Store ls} {ps : Pools ls} -> ⟨ zero , Σ , ps ⟩ ↪ ⟨ length ls , Σ , ps ⟩

--------------------------------------------------------------------------------

-- data _forks_ {ls : List Label} {h : Label} : ∀ {τ} {p₁ p₂ : Program ls τ} -> p₁ ⟼ p₂ -> Thread h -> Set where
--   fork : ∀ {l} {Σ : Store ls} -> (p : l ⊑ h) (t : Thread h) -> (fork {Σ = Σ} p t) forks t

-- fork-triggers-fork : ∀ {ls τ l} {t : Thread l} {p₁ p₂ : Program ls τ} -> (s : p₁ ⟼ p₂) -> s ↑ (fork t) -> s forks t
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (AppL x₁)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure Beta) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (IfCond x)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure IfTrue) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure IfFalse) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure Return) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure Throw) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure Bind) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure BindEx) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure Catch) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure CatchEx) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (label p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (unlabel p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (unlabelEx p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (fmapCtx₁ x₁)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (fmapCtx₂ x)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure fmap) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure fmapEx) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (fmapCtx₁∙ x₁)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (fmapCtx₂∙ x)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure fmap∙) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure fmapEx∙) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ .∙ ⟩} (Pure Hole) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabelCtx p x)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabel p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabelEx p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabelCtx∙ p x)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabel∙ p)) ()
-- fork-triggers-fork {p₁ = ⟨ store ∥ ._ ⟩} (Pure (relabelEx∙ p)) ()
-- fork-triggers-fork (BindCtx s) ()
-- fork-triggers-fork (CatchCtx s) ()
-- fork-triggers-fork (unlabelCtx p s) ()
-- fork-triggers-fork (join p x) ()
-- fork-triggers-fork (joinEx p x) ()
-- fork-triggers-fork (new p q) ()
-- fork-triggers-fork (writeCtx p s) ()
-- fork-triggers-fork (write p q r₂) ()
-- fork-triggers-fork (writeEx p q r₂) ()
-- fork-triggers-fork (readCtx p s) ()
-- fork-triggers-fork (read p q r₂) ()
-- fork-triggers-fork (readEx p) ()
-- fork-triggers-fork (fork p t) MkE = fork p t
-- fork-triggers-fork (newMVar p q) ()
-- fork-triggers-fork (putMVarCtx s) ()
-- fork-triggers-fork (putMVar q r₂) ()
-- fork-triggers-fork putMVarEx ()
-- fork-triggers-fork (takeMVarCtx s) ()
-- fork-triggers-fork (takeMVar q r₂) ()
-- fork-triggers-fork takeMVarEx ()
