module Typed.Semantics where

open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Typed.Base public
import Data.List as L

-- The context of a term can be extended without harm
wken : ∀ {τ Δ₁ Δ₂} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Var x) p = Var (wken-∈ x p)
wken (Abs t) p = Abs (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return t) p = Return (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken ξ p = ξ
wken (Throw t) p = Throw (wken t p)
wken (Catch t t₁) p = Catch (wken t p) (wken t₁ p)
wken (Mac t) p = Mac (wken t p)
wken (Macₓ t) p = Macₓ (wken t p)
wken (Res t) p = Res (wken t p)
wken (Resₓ t) p = Resₓ (wken t p)
wken (relabel x c) p = relabel x (wken c p)
wken (relabel∙ x c) p = relabel∙ x (wken c p)
wken (label x t) p = label x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
wken (join x t) p = join x (wken t p)
wken zero p = zero
wken (suc n) p = suc (wken n p)
wken (read x t) p = read x (wken t p)
wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
wken (new x t) p = new x (wken t p)
wken (fmap f x) p = fmap (wken f p) (wken x p)
wken (fmap∙ f x) p = fmap∙ (wken f p) (wken x p)
wken ∙ p = ∙

_↑¹ : ∀ {α β Δ} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) β
var-subst [] Δ₂ t Here = t
var-subst [] Δ t (There p) = Var p
var-subst (β ∷ Δ₁) Δ₂ t Here = Var Here
var-subst (x ∷ Δ₁) Δ₂ t (There p) = (var-subst Δ₁ Δ₂ t p) ↑¹

tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Var x) = var-subst Δ₁ Δ₂ v x
tm-subst Δ₁ Δ₂ v (Abs t) = Abs (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return t) = Return (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v ξ = ξ
tm-subst Δ₁ Δ₂ v (Throw t) = Throw (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Catch t t₁) = Catch (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac t) = Mac (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Macₓ t) = Macₓ (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res t) = Res (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Resₓ t) = Resₓ (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (relabel p t) = relabel p (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (relabel∙ p t) = relabel∙ p (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (join x t) = join x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v zero = zero
tm-subst Δ₁ Δ₂ v (suc n) = suc (tm-subst Δ₁ Δ₂ v n)
tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fmap f x) = fmap (tm-subst Δ₁ Δ₂ v f) (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v (fmap∙ f x) = fmap∙ (tm-subst Δ₁ Δ₂ v f) (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {Δ α β} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ} v t = tm-subst [] Δ v t

mutual

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
    fmapCtx₁ : ∀ {l α β} {f : CTerm (α => β)} {x₁ x₂ : CTerm (Res l α)} -> x₁ ⇝ x₂ -> fmap f x₁ ⇝ fmap f x₂

    fmapCtx₂ : ∀ {l α β} {f₁ f₂ : CTerm (α => β)} {x : CTerm α} -> f₁ ⇝ f₂ -> fmap f₁ (Res x) ⇝ fmap f₂ (Res x)

    fmap : ∀ {l α β} {t : Term (α ∷ []) β} {x : CTerm α} -> fmap (Abs t) (Res x) ⇝ (Res (subst x t))

    fmapEx : ∀ {l α β} {f : CTerm (α => β)} {e : CTerm Exception} -> fmap f (Resₓ {{l}} e) ⇝ (Resₓ e)

    -- Not sure if this is enough
    fmap∙ : ∀ {l α β} {f : CTerm (α => β)} {x : CTerm (Res l α)} -> fmap∙ f x ⇝ (Res ∙)

    fmapCtx₁∙ : ∀ {l α β} {f : CTerm (α => β)} {x₁ x₂ : CTerm (Res l α)} -> x₁ ⇝ x₂ -> fmap∙ f x₁ ⇝ fmap∙ f x₂

    fmapCtx₂∙ : ∀ {l α β} {f₁ f₂ : CTerm (α => β)} {x : CTerm α} -> f₁ ⇝ f₂ -> fmap∙ f₁ (Res x) ⇝ fmap∙ f₂ (Res x)    

    -- Bullet reduces to itself. We need this rule because ∙ is not a value.
    Hole : ∀ {τ : Ty} -> (∙ {{τ}}) ⇝ ∙

    relabelCtx : ∀ {l h α} {c₁ c₂ : CTerm (Res l α)} -> (p : l ⊑ h) -> c₁ ⇝ c₂ -> relabel p c₁ ⇝ relabel p c₂
  
    relabel : ∀ {l h α} {t : CTerm α} -> (p : l ⊑ h) -> relabel p (Res t) ⇝ Res t

    relabelEx : ∀ {l h α} {e : CTerm Exception} -> (p : l ⊑ h) -> relabel {α = α} p (Resₓ e) ⇝ Resₓ e

    relabelCtx∙ : ∀ {l h α} {c₁ c₂ : CTerm (Res l α)} -> (p : l ⊑ h) -> c₁ ⇝ c₂ -> relabel∙ p c₁ ⇝ relabel∙ p c₂
  
    relabel∙ : ∀ {l h α} {c : CTerm α} -> (p : l ⊑ h) -> relabel∙ p (Res c) ⇝ Res ∙ 

    relabelEx∙ : ∀ {l h α} {c : CTerm Exception} -> (p : l ⊑ h) -> relabel∙ {α = α} p (Resₓ c) ⇝ Res ∙ 


-- A program is made of a labeled store and a closed term
data Program (ls : List Label) (τ : Ty) : Set where
  ⟨_∥_⟩ : Store ls -> CTerm τ -> Program ls τ


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
               ⟨ s ∥ new p t ⟩ ⟼ ⟨ newˢ q s t ∥ Return (lengthᵐ (getMemory q s)) ⟩

    writeCtx :  ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Ref h α)} {c₃ : CTerm α} ->
                  (p : l ⊑ h) -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
                  ⟨ s₁ ∥ write p c₁ c₃ ⟩ ⟼ ⟨ s₂ ∥ write p c₂ c₃  ⟩

    write : ∀ {l h α} {s : Store ls} {n : CTerm Nat} {c : CTerm α} -> (p : l ⊑ h) (q : h ∈ ls) (r : TypedIx α n (getMemory q s)) ->
              ⟨ s ∥ write p (Res n) c ⟩ ⟼ ⟨ s [ q ][ r ]≔ c ∥ Return （） ⟩

    -- We need the proof h ∈ ls in distributivity, when erased the exception is silently ignored, the write rule applies.
    -- The write is harmless because Memory h is collpased to ∙, but to perform that operation I still need the proof h ∈ ls and  TypedIx τ n (getMemory q s)
    -- Furhtermore agda gives several problems in that proof if I explicitly use the same store s.
    -- One thing is that rewriting fails. The second problem is that not only the second store would be rewritten as s [ q ][ r ]≔ c, but also the first
    -- thus preventing to apply the rule write.
    writeEx : ∀ {l h α n} {s : Store ls} {c : CTerm α} {e : CTerm Exception} ->
              (p : l ⊑ h) (q : h ∈ ls) (r : TypedIx α n (getMemory q s)) ->
              ⟨ s ∥ write p (Resₓ e) c ⟩ ⟼ ⟨ s ∥ Return （） ⟩

    readCtx : ∀ {l h α} {s₁ : Store ls} {s₂ : Store ls} {c₁ c₂ : CTerm (Ref l α)} -> (p : l ⊑ h) ->
              ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ ->
              ⟨ s₁ ∥ (read {α = α} p c₁) ⟩ ⟼ ⟨ s₂ ∥ (read p c₂) ⟩

    read : ∀ {l h α n} {s : Store ls} {m : Memory l} -> (p : l ⊑ h) (q : l ∈ ls) -> (r : TypedIx α n (getMemory q s)) ->
              ⟨ s ∥ (read p (Res n)) ⟩ ⟼ ⟨ s ∥ unlabel p (s [ q ][ r ]) ⟩

    readEx : ∀ {l h α} {s : Store ls} {e : CTerm Exception} -> (p : l ⊑ h) ->
              ⟨ s ∥ (read {α = α} p (Resₓ e)) ⟩ ⟼ ⟨ s ∥ Throw e ⟩

  -- A program is a Redex if it can be reduced further in a certain memory configuration
  data Redex {ls : List Label} {τ : Ty} (s₁ : Store ls) (c₁ : CTerm τ) : Set where
    Step : {s₂ : Store ls} {c₂ : CTerm τ} -> ⟨ s₁ ∥ c₁ ⟩ ⟼ ⟨ s₂ ∥ c₂ ⟩ -> Redex s₁ c₁

  -- Normal forms
  -- A closed term is in normal form for a given store configuration if it cannot be reduced further
  NormalForm : ∀ {ls τ} -> Store ls -> CTerm τ -> Set
  NormalForm s₁ c = ¬ Redex s₁ c
