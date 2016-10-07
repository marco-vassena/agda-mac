-- This module defines the erasure function, auxiliary lemmas and definitions.

open import Lattice

module Sequential.Security.Erasure.Base (𝓛 : Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Relation.Binary.PropositionalEquality hiding (subst)
import Data.List as L

εˢ : ∀ {ls} -> (lₐ : Label) -> Store ls -> Store ls

-- Erasure function for open terms.
ε : ∀ {τ Δ} -> Label -> Term Δ τ -> Term Δ τ

-- Erasure function for open Mac terms.
-- Non-visible closed terms computations are collapsed to ∙ (variables are instead preserved to allow subtitution).
-- Visible computations are erased applying the erasure function homomorphically except for label and join.
-- The term wrapped by label represent sensitive information which is not reflected by its
-- type, that is why we need to explicitly check and erased that.
-- In the join case we collapse the sensitive computation directly to (Mac ∙).
-- In order for one of the join steps to apply we need to retain the constructor.
-- We can arbitrarily choose either Mac or Macₓ because the attacker won't be able to distinguish between them
-- at this sensitive level.

-- Note that it is not possible to define a satisfactory homomorphic erasure for sensitive computations, i.e.
-- an erasure function that preserves the structure of the computation.
-- Consider for instance:

  -- Mac t >>= k       ⇝   App k t
  
  -- Mac ∙ >>= ε lₐ k‌  ⇝   App k *
  
  -- We cannot fill * while retaining distributivity.
  -- When erased, t :: CTerm α, will be in general different from ∙ demanded by the erased reduction 
  -- ε lₐ t ≠ ∙

ε-Mac : ∀ {τ Δ lᵈ} -> (lₐ : Label) -> Dec (lᵈ ⊑ lₐ) -> Term Δ (Mac lᵈ τ) -> Term Δ (Mac lᵈ τ)
ε-Mac lₐ (yes p) (Var x) = Var x
ε-Mac lₐ (yes p) (App f x) = App (ε lₐ f) (ε lₐ x)
ε-Mac lₐ (yes p) (If c Then t Else e) = If (ε lₐ c) Then (ε-Mac lₐ (yes p) t) Else (ε-Mac lₐ (yes p) e)
ε-Mac lₐ (yes p) (Return t) = Return (ε lₐ t)
ε-Mac lₐ (yes p) (m >>= k) = (ε-Mac lₐ (yes p) m) >>= (ε lₐ k)
ε-Mac lₐ (yes p) (Throw t) = Throw (ε lₐ t)
ε-Mac lₐ (yes p) (Catch m h) = Catch (ε-Mac lₐ (yes p) m) (ε lₐ h)
ε-Mac lₐ (yes p) (Mac t) = Mac (ε lₐ t)
ε-Mac lₐ (yes p) (Macₓ t) = Macₓ (ε lₐ t)
ε-Mac lₐ (yes p) (label {l = lᵈ} {h = lʰ} x t) with lʰ ⊑? lₐ
ε-Mac lₐ (yes p₁) (label x t) | yes p = label x (ε lₐ t)
ε-Mac lₐ (yes p) (label x t) | no ¬p = label∙ x (ε lₐ t)
ε-Mac lₐ (yes p) (label∙ x t) = label∙ x (ε lₐ t)
ε-Mac lₐ (yes p) (unlabel x t) = unlabel x (ε lₐ t)
ε-Mac lₐ (yes p) (join {l = lᵈ} {h = lʰ} x t) with lʰ ⊑? lₐ
ε-Mac lₐ (yes p₁) (join x t) | yes p = join x (ε-Mac lₐ (yes p) t)
ε-Mac lₐ (yes p) (join x t) | no ¬p = join∙ x (ε-Mac lₐ (no ¬p) t)
ε-Mac lₐ (yes p) (join∙ {l = lᵈ} {h = lʰ} x t) = join∙ x (ε-Mac lₐ (lʰ ⊑? lₐ) t)
ε-Mac lₐ (yes _) (read {l = l} p r) =  read p (ε lₐ r)
ε-Mac lₐ (yes _) (write {h = h} p r t) = write p (ε lₐ r) (ε lₐ t)
ε-Mac lₐ (yes _) (new {h = lʰ} p t) = new p (ε lₐ t)
ε-Mac lₐ (yes _) (fork {h = h} x t) = fork x (ε-Mac lₐ (h ⊑? lₐ) t)
ε-Mac lₐ (yes _) (newMVar {α = α} x) = newMVar {α = α} x
ε-Mac lₐ (yes _) (takeMVar t) = takeMVar (ε lₐ t)
ε-Mac lₐ (yes _) (putMVar t₁ t₂) = putMVar (ε lₐ t₁) (ε lₐ t₂)
ε-Mac lₐ (yes p) (unId t) = unId (ε lₐ t)
ε-Mac lₐ (yes p) ∙ = ∙
ε-Mac lₐ (no ¬p) (Var x) = Var x  -- We don't want to erase variables, because this would prevent substitution of the actually erased term.
ε-Mac lₐ (no ¬p) t = ∙

ε {Mac lᵈ τ} lₐ t = ε-Mac lₐ (lᵈ ⊑? lₐ) t
ε lₐ （） = （）
ε lₐ True = True
ε lₐ False = False
ε lₐ (Var x) = Var x
ε lₐ (Abs t) = Abs (ε lₐ t)
ε lₐ (App f x) = App (ε lₐ f) (ε lₐ x)
ε lₐ (If t Then t₁ Else t₂) = If (ε lₐ t) Then (ε lₐ t₁) Else (ε lₐ t₂)
ε lₐ (Id t) = Id (ε lₐ t)
ε lₐ (unId t) = unId (ε lₐ t)
ε lₐ (f <*>ᴵ x) = (ε lₐ f) <*>ᴵ (ε lₐ x)
ε {Res lᵈ (Id τ)} lₐ (f <*> x) with lᵈ ⊑? lₐ
ε {Res lᵈ (Id τ)} lₐ (f <*> x) | yes p = (ε lₐ f) <*> (ε lₐ x)
ε {Res lᵈ (Id τ)} lₐ (f <*> x) | no ¬p = (ε lₐ f) <*>∙ (ε lₐ x)
ε {Res lᵈ (Id τ)} lₐ (f <*>∙ x) = (ε lₐ f) <*>∙ (ε lₐ x)
ε {Res lᵈ τ} lₐ (Res t) with lᵈ ⊑? lₐ
ε {Res lᵈ τ} lₐ (Res t) | yes p = Res (ε lₐ t)
ε {Res lᵈ τ} lₐ (Res t) | no ¬p = Res ∙
ε {Res lᵈ τ} lₐ (Resₓ t) with lᵈ ⊑? lₐ
ε {Res lᵈ τ} lₐ (Resₓ t) | yes p = Resₓ (ε lₐ t)
-- It is not possible to distinguish between Res and Resₓ when they are sensitive,
-- because you would need to be in a high computation to unlabel them,
-- which would get collapsed.
ε {Res lᵈ τ} lₐ (Resₓ t) | no ¬p = Res ∙
ε {Res lᵈ (Id τ)} lₐ (relabel p t) with lᵈ ⊑? lₐ
ε {Res lᵈ (Id τ)} lₐ (relabel p₁ t) | yes p = relabel p₁ (ε lₐ t)
ε {Res lᵈ (Id τ)} lₐ (relabel p t) | no ¬p = relabel∙ p (ε lₐ t)
ε {Res lᵈ (Id τ)} lₐ (relabel∙ p t) = relabel∙ p (ε lₐ t)
-- I don't think we need to distinguish here
-- with lᵈ ⊑? lₐ
-- ε {Res lᵈ τ} lₐ (relabel∙ p₁ t) | yes p = relabel p₁ (ε lₐ t)
-- ε {Res lᵈ τ} lₐ (relabel∙ p t) | no ¬p = relabel∙ p (ε lₐ t)
ε lₐ ξ = ξ
ε {Nat} lₐ zero = zero
ε {Nat} lₐ (suc n) = suc (ε lₐ n)
ε lₐ ∙ = ∙

-- Erasure of cell
εᶜ : ∀ {τ p} -> Label -> Cell p τ -> Cell p τ
εᶜ lₐ ⊞ = ⊞
εᶜ lₐ ⟦ x ⟧ = ⟦ ε lₐ x ⟧

εᵐ : ∀ {l} -> (lₐ : Label) -> Dec (l ⊑ lₐ) -> Memory l -> Memory l
εᵐ lₐ (yes p) ∙ = ∙
εᵐ lₐ (yes p) [] = []
εᵐ lₐ (yes p) (c ∷ m) = εᶜ lₐ c ∷ εᵐ lₐ (yes p) m
εᵐ lₐ (no ¬p) m = ∙

-- A store is erased by erasing visible memory and collapsing sensitive memories.
εˢ lₐ [] = []
εˢ lₐ (_∷_ {l = l} m s) = εᵐ lₐ (l ⊑? lₐ) m ∷ εˢ lₐ s

-- Programs are erased, by erasing its store and its closed term.
εᵖ : ∀ {ls τ} -> Label -> Program ls τ -> Program ls τ
εᵖ lₐ ⟨ s ∥ c ⟩ = ⟨ εˢ lₐ s ∥ ε lₐ c ⟩

--------------------------------------------------------------------------------

ε-Mac-extensional : ∀ {τ Δ lᵈ lₐ} -> (x y : Dec (lᵈ ⊑ lₐ)) (t : Term Δ (Mac lᵈ τ)) -> ε-Mac lₐ x t ≡ ε-Mac lₐ y t
ε-Mac-extensional (yes p) (yes p₁) (Var x₁) = refl
ε-Mac-extensional (yes p) (no ¬p) (Var x₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Var x₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Var x₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (App t t₁) = refl
ε-Mac-extensional (yes p) (no ¬p) (App t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (App t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (App t t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (If t Then t₁ Else t₂)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t₁ | ε-Mac-extensional (yes p) (yes p₁) t₂ = refl
ε-Mac-extensional (yes p) (no ¬p) (If t Then t₁ Else t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (If t Then t₁ Else t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (If t Then t₁ Else t₂) = refl
ε-Mac-extensional (yes p) (yes p₁) (Return t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Return t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Return t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Return t) = refl
ε-Mac-extensional (yes p) (yes p₁) (t >>= t₁)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t = refl
ε-Mac-extensional (yes p) (no ¬p) (t >>= t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (t >>= t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (t >>= t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (Throw t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Throw t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Throw t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Throw t) = refl
ε-Mac-extensional (yes p) (yes p₁) (Catch t t₁)
  rewrite ε-Mac-extensional (yes p) (yes p₁) t = refl
ε-Mac-extensional (yes p) (no ¬p) (Catch t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Catch t t₁) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Catch t t₁) = refl
ε-Mac-extensional (yes p) (yes p₁) (Mac t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Mac t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Mac t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Mac t) = refl
ε-Mac-extensional (yes p) (yes p₁) (Macₓ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (Macₓ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (Macₓ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (Macₓ t) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (label {h = lʰ} x₁ t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (label x₁ t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (label x₁ t) | no ¬p = refl
ε-Mac-extensional (yes p) (no ¬p) (label x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (label x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (label x₁ t) = refl
ε-Mac-extensional (yes p) (yes p₁) (label∙ p₂ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (label∙ p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (label∙ p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (label∙ p t) = refl
ε-Mac-extensional (yes p) (yes p₁) (unlabel x₁ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (unlabel x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (unlabel x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (unlabel x₁ t) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (join {h = lʰ} x₁ t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (join x₁ t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (join x₁ t) | no ¬p = refl
ε-Mac-extensional (yes p) (yes p₁) (join∙ x₁ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (join∙ x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (join∙ x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (join∙ x₁ t) = refl
ε-Mac-extensional (yes p) (no ¬p) (join x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (join x₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (join x₁ t) = refl
ε-Mac-extensional (yes p) (yes p₁) (read p₂ r) = refl
ε-Mac-extensional (yes p) (no ¬p) (read p₁ r) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (read p₁ r) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (read p r) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (write {h = lʰ} p₂ r t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (write p₃ r t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (write p₂ r t) | no ¬p = refl
ε-Mac-extensional (yes p) (no ¬p) (write p₁ r t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (write p₁ r t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (write p r t) = refl
ε-Mac-extensional {lₐ = lₐ} (yes p) (yes p₁) (new {h = lʰ} p₂ t) with lʰ ⊑? lₐ
ε-Mac-extensional (yes p₁) (yes p₂) (new p₃ t) | yes p = refl
ε-Mac-extensional (yes p) (yes p₁) (new p₂ t) | no ¬p = refl
ε-Mac-extensional (yes p) (no ¬p) (new p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (new p₁ t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (new p t) = refl
ε-Mac-extensional (yes p) (yes p₁) (fork x t) = refl
ε-Mac-extensional (yes p) (no ¬p) (fork x t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (fork x t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (fork x t) = refl
ε-Mac-extensional (yes p) (yes p₁) (newMVar t) = refl
ε-Mac-extensional (yes p) (no ¬p) (newMVar t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (newMVar t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (newMVar t) = refl
ε-Mac-extensional (yes p) (yes p₁) (takeMVar t) = refl
ε-Mac-extensional (yes p) (no ¬p) (takeMVar t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (takeMVar t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (takeMVar t) = refl 
ε-Mac-extensional (yes p) (yes p₁) (putMVar t₁ t₂) = refl
ε-Mac-extensional (yes p) (no ¬p) (putMVar t₁ t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (putMVar t₁ t₂) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (putMVar t₁ t₂) = refl
ε-Mac-extensional (yes p) (yes p₁) (unId t) = refl
ε-Mac-extensional (yes p) (no ¬p) (unId t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (yes p) (unId t) = ⊥-elim (¬p p)
ε-Mac-extensional (no ¬p) (no ¬p₁) (unId t) = refl
ε-Mac-extensional (yes p) (yes p₁) ∙ = refl
ε-Mac-extensional (yes p) (no ¬p) ∙ = refl
ε-Mac-extensional (no ¬p) (yes p) ∙ = refl
ε-Mac-extensional (no ¬p) (no ¬p₁) ∙ = refl

-- Bullet are always erased to bullet.
ε∙≡∙ : ∀ {τ : Ty} {Δ : Context} -> (lₐ : Label) -> ε {τ} {Δ} lₐ ∙ ≡ ∙
ε∙≡∙ {（）} lₐ = refl
ε∙≡∙ {Bool} lₐ = refl
ε∙≡∙ {τ => τ₁} lₐ = refl
ε∙≡∙ {Mac lᵈ τ} lₐ with lᵈ ⊑? lₐ
ε∙≡∙ {Mac lᵈ τ} lₐ | yes p = refl
ε∙≡∙ {Mac lᵈ τ} lₐ | no ¬p = refl
ε∙≡∙ {Res x τ} lₐ = refl
ε∙≡∙ {Exception} lₐ = refl
ε∙≡∙ {Nat} lₐ = refl
ε∙≡∙ {Id τ} lₐ = refl

-- Var are left untouched by the erasure function.
εVar≡Var : ∀ {α Δ} -> (lₐ : Label) (p : α ∈ Δ) -> ε lₐ (Var p) ≡ Var p
εVar≡Var {（）} lₐ p = refl
εVar≡Var {Bool} lₐ p = refl
εVar≡Var {α => α₁} lₐ p = refl
εVar≡Var {Mac lᵈ α} lₐ p with lᵈ ⊑? lₐ
εVar≡Var {Mac lᵈ α} lₐ p₁ | yes p = refl
εVar≡Var {Mac lᵈ α} lₐ p | no ¬p = refl
εVar≡Var {Res x α} lₐ p = refl
εVar≡Var {Exception} lₐ p = refl
εVar≡Var {Nat} lₐ p = refl
εVar≡Var {Id τ} lₐ p = refl

εVar≡Var' : ∀ {α Δ} -> (lₐ : Label) (p : α ∈ Δ) ->  Var p ≡ ε lₐ (Var p)
εVar≡Var' lₐ p = sym (εVar≡Var lₐ p)

--------------------------------------------------------------------------------
-- Lemmas about erasure function and substitution of variables in function application.
-- Roughly speaking erasing the result of a substitution is the same as substituting an erased
-- term in an earsed function.
--------------------------------------------------------------------------------

ε-wken : ∀ {α Δ₁ Δ₂} -> (lₐ : Label) -> (t : Term Δ₁ α) (p : Δ₁ ⊆ˡ Δ₂) -> ε lₐ (wken t p) ≡ wken (ε lₐ t) p

ε-Mac-wken : ∀ {lᵈ α Δ₁ Δ₂} -> (lₐ : Label) (x : Dec (lᵈ ⊑ lₐ)) (t : Term Δ₁ (Mac lᵈ α)) (p : Δ₁ ⊆ˡ Δ₂) -> ε-Mac lₐ x (wken t p) ≡ wken (ε-Mac lₐ x t) p
ε-Mac-wken lₐ (yes p) (Var x₁) p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Var x₁) p = refl
ε-Mac-wken lₐ (yes x) (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-Mac-wken lₐ (no x) (App t t₁) p = refl
ε-Mac-wken lₐ (yes p) (If t Then t₁ Else t₂) p₁
  rewrite ε-wken lₐ t p₁ | ε-Mac-wken lₐ (yes p) t₁ p₁ | ε-Mac-wken lₐ (yes p) t₂ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (If t Then t₁ Else t₂) p = refl
ε-Mac-wken lₐ (yes p) (Return t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Return t) p = refl
ε-Mac-wken lₐ (yes p) (t >>= t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (t >>= t₁) p = refl
ε-Mac-wken lₐ (yes p) (Throw t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Throw t) p = refl
ε-Mac-wken lₐ (yes p) (Catch t t₁) p₁
  rewrite ε-Mac-wken lₐ (yes p) t p₁ | ε-wken lₐ t₁ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Catch t t₁) p = refl
ε-Mac-wken lₐ (yes p) (Mac t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Mac t) p = refl
ε-Mac-wken lₐ (yes p) (Macₓ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (Macₓ t) p = refl
ε-Mac-wken lₐ (yes p) (label {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (label x₁ t) p₂ | yes p rewrite ε-wken lₐ t p₂ = refl
ε-Mac-wken lₐ (yes p) (label x₁ t) p₁ | no ¬p rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (label x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (label∙ x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (label∙ x₁ t) p rewrite ε-wken lₐ t p = refl
ε-Mac-wken lₐ (yes p) (unlabel x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (unlabel x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (join {h = lʰ} x₁ t) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (join x₁ t) p₂ | yes p rewrite ε-Mac-wken lₐ (yes p) t p₂ = refl
ε-Mac-wken lₐ (yes p) (join x₁ t) p₁ | no ¬p rewrite ε-Mac-wken lₐ (no ¬p) t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (join x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (join∙ {h = h} x₁ t) p₁ rewrite ε-Mac-wken lₐ (h ⊑? lₐ) t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (join∙ {h = h} x₁ t) p₁ rewrite ε-Mac-wken lₐ (h ⊑? lₐ) t p₁ = refl 
ε-Mac-wken lₐ (yes p) (read {l = l} x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
-- with l ⊑? lₐ
-- ε-Mac-wken lₐ (yes p₁) (read x₁ t) p₂ | yes p rewrite ε-wken lₐ t p₂ = refl
-- ε-Mac-wken lₐ (yes p) (read x₁ t) p₁ | no ¬p = refl 
ε-Mac-wken lₐ (no ¬p) (read x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (write {h = lʰ} x₁ t t₁) p₁ with lʰ ⊑? lₐ
ε-Mac-wken lₐ (yes p₁) (write x₁ t t₁) p₂ | yes p rewrite ε-wken lₐ t p₂ | ε-wken lₐ t₁ p₂ = refl
ε-Mac-wken lₐ (yes p) (write x₁ t t₁) p₁ | no ¬p rewrite ε-wken lₐ t p₁ | ε-wken lₐ t₁ p₁ = refl 
ε-Mac-wken lₐ (no ¬p) (write x₁ t t₁) p = refl
ε-Mac-wken lₐ (yes p) (new {h = lʰ} x₁ t) p₁ rewrite ε-wken lₐ t p₁ = refl
-- with lʰ ⊑? lₐ
-- ε-Mac-wken lₐ (yes p₁) (new x₁ t r) p₂ | yes p rewrite ε-wken lₐ t p₂ = refl
-- ε-Mac-wken lₐ (yes p) (new x₁ t r) p₁ | no ¬p = refl
ε-Mac-wken lₐ (no ¬p) (new x₁ t) p = refl
ε-Mac-wken lₐ (yes p) (fork {h = h} x t) p₁
  rewrite ε-Mac-wken lₐ (h ⊑? lₐ) t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (fork x t) p = refl
ε-Mac-wken lₐ (yes p) (newMVar x) p₁ = refl
ε-Mac-wken lₐ (no ¬p) (newMVar x) p = refl 
ε-Mac-wken lₐ (yes p) (takeMVar t) p₁
  rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (takeMVar t) p = refl
ε-Mac-wken lₐ (yes p) (putMVar t₁ t₂) p₁
  rewrite ε-wken lₐ t₁ p₁ | ε-wken lₐ t₂ p₁ = refl
ε-Mac-wken lₐ (no ¬p) (putMVar t₁ t₂) p = refl
ε-Mac-wken lₐ (yes p) (unId t) p₁ rewrite ε-wken lₐ t p₁ = refl
ε-Mac-wken lₐ (no ¬p) (unId t) p = refl
ε-Mac-wken lₐ (yes p) ∙ p₁ = refl
ε-Mac-wken lₐ (no ¬p) ∙ p = refl

ε-wken {（）} lₐ （） p = refl
ε-wken {（）} lₐ (Var x) p = refl
ε-wken {（）} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {（）} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {（）} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {（）} lₐ ∙ p = refl
ε-wken {Id τ} lₐ (Id t) p rewrite ε-wken lₐ t p = refl
ε-wken {Id τ} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {Id τ} lₐ (f <*>ᴵ x) p rewrite ε-wken lₐ f p | ε-wken lₐ x p = refl
ε-wken {Id τ} lₐ (Var x) p = refl
ε-wken {Id τ} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Id τ} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Id τ} lₐ ∙ p = refl
ε-wken {Bool} lₐ True p = refl
ε-wken {Bool} lₐ False p = refl
ε-wken {Bool} lₐ (Var x) p = refl
ε-wken {Bool} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Bool} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Bool} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {Bool} lₐ ∙ p = refl
ε-wken {α => α₁} lₐ (Var x) p = refl
ε-wken {α => α₁} lₐ (Abs t) p with ε-wken lₐ t (cons p)  -- Strangely just rewrite leads to unsolved unification about 𝓛
... | eq rewrite eq = refl 
ε-wken {α => α₁} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {α => α₁} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {α => β} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {α => α₁} lₐ ∙ p = refl
ε-wken {Mac lᵈ α} lₐ t p rewrite ε-Mac-wken lₐ (lᵈ ⊑? lₐ) t p = refl
ε-wken {Res x α} lₐ (Var x₁) p = refl
ε-wken {Res x α} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Res x α} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Res lᵈ (Id α)} lₐ (f <*> x) p with lᵈ ⊑? lₐ
... | yes _ rewrite ε-wken lₐ f p | ε-wken lₐ x p = refl
... | no ¬p rewrite ε-wken lₐ f p | ε-wken lₐ x p = refl
ε-wken {Res lᵈ (Id α)} lₐ (f <*>∙ x) p rewrite ε-wken lₐ f p | ε-wken lₐ x p = refl
ε-wken {Res lᵈ α} lₐ (Res t) p with lᵈ ⊑? lₐ
ε-wken {Res lᵈ α} lₐ (Res t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Res lᵈ α} lₐ (Res t) p | no ¬p = refl
ε-wken {Res lᵈ α} lₐ (Resₓ t) p with lᵈ ⊑? lₐ
ε-wken {Res lᵈ α} lₐ (Resₓ t) p₁ | yes p
  rewrite ε-wken lₐ t p₁ = refl
ε-wken {Res lᵈ α} lₐ (Resₓ t) p | no ¬p = refl
ε-wken {Res lᵈ (Id α)} lₐ (relabel x t) p with lᵈ ⊑? lₐ
ε-wken {Res lᵈ (Id α)} lₐ (relabel x t) p₁ | yes p rewrite ε-wken lₐ t p₁ = refl
ε-wken {Res lᵈ (Id α)} lₐ (relabel x t) p | no ¬p rewrite ε-wken lₐ t p = refl
ε-wken {Res lᵈ (Id α)} lₐ (relabel∙ x t) p rewrite ε-wken lₐ t p = refl
ε-wken {Res lᵈ α} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {Res x α} lₐ ∙ p = refl
ε-wken {Exception} lₐ (Var x) p = refl
ε-wken {Exception} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Exception} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Exception} lₐ ξ p = refl
ε-wken {Exception} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {Exception} lₐ ∙ p = refl
ε-wken {Nat} lₐ (Var x₁) p = refl
ε-wken {Nat} lₐ (App t t₁) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p = refl
ε-wken {Nat} lₐ (If t Then t₁ Else t₂) p
  rewrite ε-wken lₐ t p | ε-wken lₐ t₁ p | ε-wken lₐ t₂ p = refl
ε-wken {Nat} lₐ zero p = refl
ε-wken {Nat} lₐ (suc n) p rewrite ε-wken lₐ n p = refl
ε-wken {Nat} lₐ (unId t) p rewrite ε-wken lₐ t p = refl
ε-wken {Nat} lₐ ∙ p = refl

ε-subst : ∀ {Δ α β} (lₐ : Label) (x : Term Δ α) (t : Term (α ∷ Δ) β) -> subst (ε lₐ x) (ε lₐ t) ≡ ε lₐ (subst x t)
ε-subst lₐ x t = ε-tm-subst [] _ x t
  where
        ε-tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ) ->
               tm-subst Δ₁ Δ₂ (ε lₐ x) (ε lₐ t) ≡ ε lₐ (tm-subst Δ₁ Δ₂ x t)

        ε-Mac-tm-subst : ∀ {lᵈ α  τ} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (t : Term (Δ₁ ++ L.[ α ] ++ Δ₂) (Mac lᵈ τ)) (p : Dec (lᵈ ⊑ lₐ)) ->
                         tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ p t) ≡ ε-Mac lₐ p (tm-subst Δ₁ Δ₂ x t)


        ε-var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) -> (p : β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                      var-subst Δ₁ Δ₂ (ε lₐ x) p ≡ ε lₐ (var-subst Δ₁ Δ₂ x p)
        ε-var-subst [] Δ₂ t₁ Here = refl
        ε-var-subst [] Δ t₁ (There p) rewrite εVar≡Var lₐ p = refl
        ε-var-subst (（） ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Bool ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst ((β => β₁) ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Id α ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here with lᵈ ⊑? lₐ
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | yes p = refl
        ε-var-subst (Mac lᵈ β ∷ Δ₁) Δ₂ t₁ Here | no ¬p = refl
        ε-var-subst (Res x₁ β ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Exception ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (Nat ∷ Δ₁) Δ₂ t₁ Here = refl
        ε-var-subst (x₁ ∷ Δ₁) Δ₂ t₁ (There p)
          rewrite ε-var-subst Δ₁ Δ₂ t₁ p | ε-wken lₐ (var-subst Δ₁ Δ₂ t₁ p) (drop {x₁} refl-⊆ˡ) = refl

        ε-Mac-var-subst : ∀ {lᵈ α β} (Δ₁ Δ₂ : Context) (x : Term Δ₂ α) (y : Dec (lᵈ ⊑ lₐ)) -> (p : (Mac lᵈ β) ∈ (Δ₁ ++ L.[ α ] ++ Δ₂)) ->
                          tm-subst Δ₁ Δ₂ (ε lₐ x) (ε-Mac lₐ y (Var p)) ≡ ε-Mac lₐ y (var-subst Δ₁ Δ₂ x p)

        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (yes p) Here rewrite ε-Mac-extensional (yes p) (lᵈ ⊑? lₐ) x₁ = refl
        ε-Mac-var-subst {lᵈ} [] Δ₂ x₁ (no ¬p) Here rewrite ε-Mac-extensional (no ¬p) (lᵈ ⊑? lₐ) x₁ =  refl
        ε-Mac-var-subst [] Δ x₁ (yes p) (There p₁) = refl
        ε-Mac-var-subst [] Δ x₁ (no ¬p) (There p) = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (yes p) Here = refl
        ε-Mac-var-subst (._ ∷ Δ₁) Δ₂ x₂ (no ¬p) Here = refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (yes p) (There p₁)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (yes p) p₁ | ε-Mac-wken lₐ (yes p) (var-subst Δ₁ Δ₂ x₂ p₁) (drop {x₁} refl-⊆ˡ) =  refl
        ε-Mac-var-subst (x₁ ∷ Δ₁) Δ₂ x₂ (no ¬p) (There p)
          rewrite ε-Mac-var-subst Δ₁ Δ₂ x₂ (no ¬p) p | ε-Mac-wken lₐ (no ¬p) (var-subst Δ₁ Δ₂ x₂ p) (drop {x₁} refl-⊆ˡ) =  refl

        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ （） = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl          
        ε-tm-subst {τ = （）} Δ₁ Δ₂ x₁ ∙ = refl

        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ True = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ False = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-tm-subst {τ = Bool} Δ₁ Δ₂ x₁ ∙ = refl
        
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (Abs t₁)
          rewrite ε-tm-subst (_ ∷ Δ₁) Δ₂ x₁ t₁ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = α => β} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-tm-subst {τ = τ => τ₁} Δ₁ Δ₂ x₁ ∙ = refl
        
        ε-tm-subst {τ = Mac lᵈ τ} Δ₁ Δ₂ x₂ t₁ = ε-Mac-tm-subst Δ₁ Δ₂ x₂ t₁ (lᵈ ⊑? lₐ)
        
        ε-tm-subst {τ = Res x₁ τ} Δ₁ Δ₂ x₂ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₂ x₃ = refl
        ε-tm-subst {τ = Res l τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Res l τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {α} {Res lᵈ (Id τ)} Δ₁ Δ₂ x₁ (f <*> x) with lᵈ ⊑? lₐ
        ... | yes _  rewrite ε-tm-subst Δ₁ Δ₂ x₁ f | ε-tm-subst Δ₁ Δ₂ x₁ x = refl
        ... | no _  rewrite ε-tm-subst Δ₁ Δ₂ x₁ f | ε-tm-subst Δ₁ Δ₂ x₁ x = refl               
        ε-tm-subst {α} {Res l (Id τ)} Δ₁ Δ₂ x₁ (f <*>∙ x) rewrite ε-tm-subst Δ₁ Δ₂ x₁ f | ε-tm-subst Δ₁ Δ₂ x₁ x = refl       
        ε-tm-subst {τ = Res lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Res lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Res lᵈ τ} Δ₁ Δ₂ x₂ (Res t₁) | no ¬p = refl
        ε-tm-subst {τ = Res lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Res lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Res lᵈ τ} Δ₁ Δ₂ x₂ (Resₓ t₁) | no ¬p = refl
        ε-tm-subst {α} {Res lᵈ (Id τ)} Δ₁ Δ₂ x₂ (relabel x t) with lᵈ ⊑? lₐ
        ε-tm-subst {α} {Res lᵈ (Id τ)} Δ₁ Δ₂ x₂ (relabel x₁ t₁) | yes p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Res lᵈ (Id τ)} Δ₁ Δ₂ x₂ (relabel x₁ t₁) | no ¬p
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t₁ = refl
        ε-tm-subst {α} {Res lᵈ (Id τ)} Δ₁ Δ₂ x₂ (relabel∙ x t)
          rewrite ε-tm-subst Δ₁ Δ₂ x₂ t = refl
        ε-tm-subst {τ = Res lᵈ τ} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl       
        ε-tm-subst {τ = Res x₁ τ} Δ₁ Δ₂ x₂ ∙ = refl
        
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ξ = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-tm-subst {τ = Exception} Δ₁ Δ₂ x₁ ∙ = refl
        
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ (Var x₃) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₃ = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁  | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ zero = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ (suc n) rewrite ε-tm-subst Δ₁ Δ₂ x₁ n = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₁ (unId t) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-tm-subst {τ = Nat} Δ₁ Δ₂ x₂ ∙ = refl

        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (Id t₁) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (unId t₁) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (f <*>ᴵ x) rewrite ε-tm-subst Δ₁ Δ₂ x₁ f | ε-tm-subst Δ₁ Δ₂ x₁ x  = refl       
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (Var x₂) rewrite ε-var-subst Δ₁ Δ₂ x₁ x₂ = refl
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (App t₁ t₂)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ | ε-tm-subst Δ₁ Δ₂ x₁ t₃ = refl
        ε-tm-subst {τ = Id τ} Δ₁ Δ₂ x₁ ∙ = refl

        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Var p) x rewrite ε-Mac-var-subst Δ₁ Δ₂ x₁ x p = refl         
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (yes p)
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₂ (yes p) | ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₃ (yes p) = refl                        
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (yes p)
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p₁) | yes p 
          rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (yes p) | no ¬p rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label∙ {h = h} x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join {h = h} x₂ t₁) (yes p) with h ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p₁) | yes p
          rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (yes p) | no ¬p rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (no ¬p)  = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join∙ {h = h} x₂ t₁) (yes p) rewrite ε-Mac-tm-subst Δ₁ Δ₂ x₁ t₁ (h ⊑? lₐ) = refl 
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read {l = l} x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        -- with l ⊑? lₐ
        -- ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (yes p₁) | yes p rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        -- ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (yes p) | no ¬p = refl 
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write {h = lʰ} x₂ t₁ t₂) (yes p) with lʰ ⊑? lₐ
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (yes p₁) | yes p rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (yes p) | no ¬p rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new {h = lʰ} x₂ t₁) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t₁ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (fork x t) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (newMVar {α = α} x) (yes p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (takeMVar t) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (putMVar t₁ t₂) (yes p) rewrite
            ε-tm-subst Δ₁ Δ₂ x₁ t₁ | ε-tm-subst Δ₁ Δ₂ x₁ t₂ = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unId t) (yes p) rewrite ε-tm-subst Δ₁ Δ₂ x₁ t = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (yes p) = refl
        
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (App t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (If t₁ Then t₂ Else t₃) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Return t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (t₁ >>= t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Throw t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Catch t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Mac t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (Macₓ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (label∙ x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unlabel x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (join∙ {h = h} x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (read x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (write x₂ t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (new x₂ t₁) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (fork x t) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (newMVar {α = α} x) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (takeMVar t) (no ¬p) = refl 
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (putMVar t₁ t₂) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ (unId t) (no ¬p) = refl
        ε-Mac-tm-subst Δ₁ Δ₂ x₁ ∙ (no ¬p) = refl

ε-Mac-subst : ∀ {lᵈ Δ α β} (lₐ : Label) (y : Dec (lᵈ ⊑ lₐ)) (x : Term Δ α) (t : Term (α ∷ Δ) (Mac lᵈ β))
              -> subst (ε lₐ x) (ε-Mac lₐ (lᵈ ⊑? lₐ) t) ≡ (ε-Mac lₐ y (subst x t))
ε-Mac-subst {lᵈ} lₐ y x t rewrite ε-Mac-extensional y (lᵈ ⊑? lₐ) (subst x t) = ε-subst lₐ x t

ε-Mac-CTerm≡∙ : ∀ {lᵈ τ} (lₐ : Label) (c : CTerm (Mac lᵈ τ)) (x : ¬ (lᵈ ⊑ lₐ)) -> ε-Mac lₐ (no x) c ≡ ∙
ε-Mac-CTerm≡∙ lₐ (Var ()) x₁
ε-Mac-CTerm≡∙ lₐ (App c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (If c Then c₁ Else c₂) x = refl
ε-Mac-CTerm≡∙ lₐ (Return c) x = refl
ε-Mac-CTerm≡∙ lₐ (c >>= c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Throw c) x = refl
ε-Mac-CTerm≡∙ lₐ (Catch c c₁) x = refl
ε-Mac-CTerm≡∙ lₐ (Mac c) x = refl
ε-Mac-CTerm≡∙ lₐ (Macₓ c) x = refl
ε-Mac-CTerm≡∙ lₐ (label x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (label∙ x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (unlabel x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (join x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (join∙ x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (read x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (write x c c₁) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (new x c) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (fork x t) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (newMVar {α = α} x) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (takeMVar t) x₁ = refl 
ε-Mac-CTerm≡∙ lₐ (putMVar t₁ t₂) x₁ = refl
ε-Mac-CTerm≡∙ lₐ (unId t) x = refl
ε-Mac-CTerm≡∙ lₐ ∙ x = refl
