module Typed.Semantics where

open import Typed.Base public
import Data.List as L


-- TODO remove
data _≅ᵛ_ {α : Ty} {Δ : Context} (x : α ∈ Δ) : ∀ {β} -> (y : β ∈ Δ) -> Set where
  refl : x ≅ᵛ x

-- TODO remove
varEq? : ∀ {α β Δ} -> (x : α ∈ Δ) (y : β ∈ Δ) -> Dec (x ≅ᵛ y)
varEq? Here Here = yes refl
varEq? Here (There y) = no (λ ())
varEq? (There x) Here = no (λ ())
varEq? (There x) (There y) with varEq? x y
varEq? (There x) (There .x) | yes refl = yes refl
varEq? (There x) (There y) | no ¬p = no (aux ¬p)
  where aux : ∀ {α β γ Δ} {x : α ∈ Δ} {y : β ∈ Δ} -> ¬ (x ≅ᵛ y) -> ¬ ((There {β = γ} x) ≅ᵛ There y)
        aux ¬p₁ refl = ¬p₁ refl


--------------------------------------------------------------------------------
-- TODO move to types
-- subset
data _⊆ˡ_ : List Ty -> List Ty -> Set where
  base : [] ⊆ˡ [] 
  cons : ∀ {α Δ₁ Δ₂} -> Δ₁ ⊆ˡ Δ₂ -> (α ∷ Δ₁) ⊆ˡ (α ∷ Δ₂)
  drop : ∀ {α Δ₁ Δ₂} -> Δ₁ ⊆ˡ Δ₂ -> Δ₁ ⊆ˡ (α ∷ Δ₂)

refl-⊆ˡ : ∀ {Δ} -> Δ ⊆ˡ Δ
refl-⊆ˡ {[]} = base
refl-⊆ˡ {x ∷ Δ} = cons refl-⊆ˡ

wken-∈ : ∀ {τ Δ₁ Δ₂} -> τ ∈ Δ₁ -> Δ₁ ⊆ˡ Δ₂ -> τ ∈ Δ₂
wken-∈ () base
wken-∈ Here (cons p) = Here
wken-∈ (There x) (cons p) = There (wken-∈ x p)
wken-∈ x (drop p) = There (wken-∈ x p)

infixr 2 _⊆ˡ_
--------------------------------------------------------------------------------

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
wken (label x t) p = label x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
wken (join x t) p = join x (wken t p)
wken (Ref x) p = Ref x
wken (read x t) p = read x (wken t p)
wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
wken (new x t) p = new x (wken t p)
wken ∙ p = ∙

_↑¹ : ∀ {α β Δ} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

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
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (join x t) = join x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Ref x) = Ref x
tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {Δ α β} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ} v t = tm-subst [] Δ v t


data _⇝_ : ∀ {τ} -> CTerm τ -> CTerm τ -> Set where

  -- Reduces the function in an application
  AppL : ∀ {α β} {c₁ c₂ : CTerm (α => β)} {x : CTerm α} -> c₁ ⇝ c₂ -> App c₁ x ⇝ App c₂ x

  -- Pushes a term in the environment
  Beta : ∀ {α β} {t : Term (α ∷ []) β} {x : CTerm α} -> App (Abs t) x ⇝ subst x t
  
  -- Evaluates the condition term
  IfCond : ∀ {τ} {c c' : CTerm Bool} {t e : CTerm τ} -> c ⇝ c' ->
             (If c Then t Else e) ⇝ (If c' Then t Else e)

  -- Reduces to the Then branch if the condition is True
  IfTrue : ∀ {τ} {t e : CTerm τ} -> (If True Then t Else e) ⇝ t

  -- Reduces to the Else branch if the condition is False
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

  -- Bullet reduces to itself
  Hole : ∀ {τ : Ty} -> (∙ {{τ}}) ⇝ ∙


data Program (Δ : Context) (τ : Ty) : Set where
  ⟨_∥_⟩ : Memory Δ -> CTerm τ -> Program Δ τ


mutual
  infixr 1 _⟼_

--   -- The transitive reflexive closure of a small step
--   data _⟼⋆_ {τ : Ty} : ∀ {Δ₁ Δ₂} -> Program Δ₁ τ -> Program Δ₂ τ -> Set where
--     [] : ∀ {Δ} {m : Memory Δ} {c : CTerm τ} -> ⟨ m ∥ c ⟩ ⟼⋆ ⟨ m ∥ c ⟩ 
--     _∷_ : ∀ {Δ₁ Δ₂ Δ₃} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {m₃ : Memory Δ₃} {c₁ c₂ c₃ : CTerm τ} ->
--             ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> ⟨ m₂ ∥ c₂ ⟩ ⟼⋆ ⟨ m₃ ∥ c₃ ⟩ -> ⟨ m₁ ∥ c₁ ⟩ ⟼⋆ ⟨ m₃ ∥ c₃ ⟩

--   -- Big step, a finite number (possibly 0) of reduction steps of a term that reduces it to a value.
--   data _⇓_ {τ : Ty} : ∀ {Δ₁ Δ₂} -> Program Δ₁ τ -> Program Δ₂ τ -> Set where
--     BigStep : ∀ {Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c v : CTerm τ} -> IsValue v -> ⟨ m₁ ∥ c ⟩ ⟼⋆ ⟨ m₂ ∥ v ⟩ -> ⟨ m₁ ∥ c ⟩ ⇓ ⟨ m₂ ∥ v ⟩

  data _⟼_ : ∀ {Δ₁ Δ₂ τ} -> Program Δ₁ τ -> Program Δ₂ τ -> Set where
    Pure : ∀ {Δ₁ τ} {m₁ : Memory Δ₁} {c₁ c₂ : CTerm τ} -> c₁ ⇝ c₂ -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₁ ∥ c₂ ⟩

    BindCtx : ∀ {l α β Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Mac l α)} {k : CTerm (α => Mac l β)} ->
                ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                ⟨ m₁  ∥  c₁ >>= k ⟩ ⟼ ⟨ m₂ ∥ c₂ >>= k ⟩ 

    CatchCtx : ∀ {l α Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂}
                 {c₁ c₂ : CTerm (Mac l α)} {h : CTerm (Exception => Mac l α)} ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                 ⟨ m₁ ∥ Catch c₁ h ⟩ ⟼ ⟨ m₂ ∥ Catch c₂ h ⟩


    unlabelCtx : ∀ {l h α Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Labeled l α)} -> (p : l ⊑ h) ->
                   ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                   ⟨ m₁ ∥ unlabel p c₁ ⟩ ⟼ ⟨ m₂ ∥ unlabel p c₂ ⟩

    -- Let's what would break with small step semantics for context
    joinCtx : ∀ {l h α Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Mac h α)} (p : l ⊑ h) ->
                 ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                 ⟨ m₁ ∥ join p c₁ ⟩ ⟼ ⟨ m₂ ∥ join p c₂ ⟩
                 
    join : ∀ {l h α Δ₁} {m₁ : Memory Δ₁}  {t : CTerm α} (p : l ⊑ h) ->
--              ⟨ m₁ ∥ c ⟩ ⇓ ⟨ m₂ ∥ Γ , Mac t ⟩ ->
              ⟨ m₁ ∥ join p (Mac t) ⟩ ⟼ ⟨ m₁ ∥ (Return (Res t)) ⟩

    joinEx : ∀ {l h α Δ₁} {m₁ : Memory Δ₁} {e : CTerm Exception} (p : l ⊑ h) ->
--                ⟨ m₁ ∥ c ⟩ ⇓ ⟨ m₂ ∥ Γ , Macₓ e ⟩ ->
                ⟨ m₁ ∥ join {α = α} p (Macₓ e) ⟩ ⟼ ⟨ m₁ ∥ (Return (Resₓ e)) ⟩

--     -- In LIO values stored in memory are labeled

    new : ∀ {l h α Δ₁} {m₁ : Memory Δ₁} {t : CTerm α} -> (p : l ⊑ h) -> ⟨ m₁ ∥ new p t ⟩ ⟼ ⟨ m₁ ∷ʳ t ∥ Return (Ref (length Δ₁)) ⟩


    writeCtx :  ∀ {l h α Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Ref h α)} {c₃ : CTerm α} ->
                  (p : l ⊑ h) -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
                  ⟨ m₁ ∥ write p c₁ c₃ ⟩ ⟼ ⟨ m₂ ∥ write p c₂ c₃  ⟩

--     -- TODO to make the semantics deterministic we need to put references in the variables
--     -- otherwise the reference used in each step is existentially quantified and hence
--     -- different in general.
    write : ∀ {l h n α Δ₁} {m₁ : Memory Δ₁} {c : CTerm α} ->
              (p : l ⊑ h) -> (i : TypedIx α n Δ₁) ->
            ⟨ m₁ ∥ write p (Ref n) c ⟩ ⟼ ⟨ m₁ [ # i ]≔ c ∥ Return （） ⟩

    readCtx : ∀ {l h α Δ₁ Δ₂} {m₁ : Memory Δ₁} {m₂ : Memory Δ₂} {c₁ c₂ : CTerm (Ref l α)} -> (p : l ⊑ h) ->
              ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ ->
              ⟨ m₁ ∥ (read p c₁) ⟩ ⟼ ⟨ m₂ ∥ (read p c₂) ⟩

    read : ∀ {l h n α Δ₁} {m₁ : Memory Δ₁} -> (p : l ⊑ h) -> (i : TypedIx α n Δ₁) ->
              ⟨ m₁ ∥ (read p (Ref n)) ⟩ ⟼ ⟨ m₁ ∥ Return (m₁ [ # i ] ) ⟩

    Hole : ∀ {τ : Ty} {Δ₁ Δ₂ : Context} -> Δ₁ ⊆ Δ₂ -> ⟨ ∙ {{Δ₁}} ∥ ∙ {{τ}} ⟩ ⟼ ⟨ ∙ {{Δ₂}} ∥ ∙ ⟩


-- TODO maybe define Redex for Program instead of single term  

  -- A closed term is a Redex if it can be reduced further in a certain memory configuration
  data Redex {Δ₁ : Context} {τ : Ty} (m₁ : Memory Δ₁) (c₁ : CTerm τ) : Set where
    Step : ∀ {Δ₂} {m₂ : Memory Δ₂} {c₂ : CTerm τ} -> ⟨ m₁ ∥ c₁ ⟩ ⟼ ⟨ m₂ ∥ c₂ ⟩ -> Redex m₁ c₁

  -- Normal forms
  -- A closed term is in normal form for a given memory configuration
  -- if it cannot be reduced further
  NormalForm : ∀ {Δ₁ τ} -> Memory Δ₁ -> CTerm τ -> Set
  NormalForm m₁ c = ¬ Redex m₁ c
