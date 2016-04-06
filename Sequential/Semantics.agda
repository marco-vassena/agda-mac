module Sequential.Semantics where

open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Sequential.Calculus public
import Data.List as L
open import Data.List.All
open import Data.Stream using (_∷_ ; Stream)
open import Coinduction

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

data Stuck {ls : List Label} {τ : Ty} (Σ : Store ls) (t : CTerm τ) : Set where
  stuck : ∀ {Σ' : Store ls} {t' : CTerm τ} -> ¬ (⟨ Σ ∥ t ⟩ ⟼ ⟨ Σ' ∥ t' ⟩) -> ¬ (IsValue t) -> Stuck Σ t

data PStatus {ls : List Label} {τ : Ty} (Σ : Store ls) (t : CTerm τ) : Set where
  V : IsValue t -> PStatus Σ t
  R : Redex Σ t -> PStatus Σ t
  S : Stuck Σ t -> PStatus Σ t
  
postulate programStatus : ∀ {τ ls} -> (Σ : Store ls) (t : CTerm τ) -> PStatus Σ t
