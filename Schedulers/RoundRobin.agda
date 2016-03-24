module Schedulers.RoundRobin where

open import Types
open import Typed.Communication renaming (_,_,_ to ⟪_,_,_⟫)
open import Data.Product
open import Data.Nat
open import Data.List

State : Set
State = List (Label × ℕ)

εˢ : Label -> State -> State
εˢ lₐ [] = []
εˢ lₐ ((l , n) ∷ s) with l ⊑? lₐ
εˢ lₐ ((l , n) ∷ s) | yes p = (l , n) ∷ (εˢ lₐ s)
εˢ lₐ ((l , n) ∷ s) | no ¬p = εˢ lₐ s

data _⟶_↑_ : ∀ {l} -> State -> State -> Message l -> Set where
  step : ∀ {s l n} -> ((l , n) ∷ s) ⟶ s ++ [ (l , n) ] ↑ ⟪ l , n , Step ⟫
  fork : ∀ {s l n h m} -> (p : l ⊑ h) -> ((l , n) ∷ s) ⟶ ((h , m) ∷ s) ++ [ (l , n) ] ↑ ⟪ l , n , Fork h m ⟫
  done : ∀ {s l n} -> ((l , n) ∷ s) ⟶ s ↑ ⟪ l , n , Done ⟫
  skip : ∀ {s l n} -> ((l , n) ∷ s) ⟶ s ++ [ (l , n) ] ↑ ⟪ l , n , NoStep ⟫
  hole : ∀ {s l n} -> s ⟶ s ↑ ⟪ l , n , ∙ ⟫

open import Security.Base hiding (εˢ)
open import Relation.Binary.PropositionalEquality hiding ([_])

εˢ-append-yes : ∀ {l lₐ} {{n}} -> (xs : State) -> l ⊑ lₐ -> εˢ lₐ xs ++ [ l , n ] ≡ εˢ lₐ (xs ++ [ l , n ])
εˢ-append-yes {l} {lₐ} [] ¬p with l ⊑? lₐ
εˢ-append-yes [] p' | yes p = refl
εˢ-append-yes [] p | no ¬p = ⊥-elim (¬p p)
εˢ-append-yes {lₐ = lₐ} {{n}} ((l' , n') ∷ xs) p with l' ⊑? lₐ
... | yes p' rewrite εˢ-append-yes {{n}} xs p = refl
... | no ¬p rewrite εˢ-append-yes {{n}} xs p = refl


εˢ-append-no : ∀ {l lₐ} {{n}} -> (xs : State) -> ¬ (l ⊑ lₐ) -> εˢ lₐ xs ≡ εˢ lₐ (xs ++ [ l , n ])
εˢ-append-no {l} {lₐ} [] ¬p with l ⊑? lₐ
εˢ-append-no [] ¬p | yes p = ⊥-elim (¬p p)
εˢ-append-no [] ¬p₁ | no ¬p = refl
εˢ-append-no {lₐ = lₐ} {{n}} ((l' , n') ∷ xs) ¬p with l' ⊑? lₐ
... | yes p rewrite εˢ-append-no {{n}} xs ¬p  = refl
... | no ¬p' rewrite εˢ-append-no {{n}} xs ¬p  = refl

ε-sch-dist : ∀ {l lₐ s₁ s₂} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m -> (εˢ lₐ s₁) ⟶ (εˢ lₐ s₂) ↑ (εᴹ x m)
ε-sch-dist {lₐ = lₐ} {s₁ = (l , n) ∷ s} (yes p) step with l ⊑? lₐ
ε-sch-dist {s₁ = (l , n) ∷ s} (yes p₁) step | yes p rewrite sym (εˢ-append-yes {{n}} s p) = step
ε-sch-dist {s₁ = (l , n) ∷ s} (yes p) step | no ¬p = ⊥-elim (¬p p)
ε-sch-dist {lₐ = lₐ} {s₁ = (l , n) ∷ s₁} (no ¬p) step with l ⊑? lₐ
ε-sch-dist {s₁ = (l , n) ∷ s₁} (no ¬p) step | yes p = ⊥-elim (¬p p)
ε-sch-dist {s₁ = (l , n) ∷ s₁} (no ¬p₁) step | no ¬p rewrite εˢ-append-no {{n}} s₁ ¬p = hole
ε-sch-dist {lₐ = lₐ} (yes p) (fork {s} {l} {n} p') with l ⊑? lₐ
ε-sch-dist {lₐ = lₐ} (yes p₁) (fork {h = h} p') | yes p with h ⊑? lₐ
ε-sch-dist (yes p₂) (fork {s} {_} {n} p') | yes p₁ | yes p rewrite sym (εˢ-append-yes {{n}} s p₁) = fork p'
ε-sch-dist (yes p₁) (fork {s} {_} {n} p') | yes p | no ¬p rewrite sym (εˢ-append-yes {{n}} s p₁) = step
ε-sch-dist (yes p) (fork  p')| no ¬p = ⊥-elim (¬p p) 
ε-sch-dist {lₐ = lₐ} (no ¬p) (fork {s} {l} {n} p') with l ⊑? lₐ
ε-sch-dist (no ¬p) (fork p') | yes p = ⊥-elim (¬p p)
ε-sch-dist {lₐ = lₐ} (no ¬p₁) (fork {h = h} p') | no ¬p with h ⊑? lₐ
ε-sch-dist (no ¬p₁) (fork p') | no ¬p | yes p = ⊥-elim (trans-⋢ p' ¬p₁ p) 
ε-sch-dist (no ¬p₂) (fork {s} {l} {n} p') | no ¬p₁ | no ¬p rewrite εˢ-append-no {{n}} s ¬p₁ = hole
ε-sch-dist {l} {lₐ} (yes p) done with l ⊑? lₐ
ε-sch-dist (yes p₁) done | yes p = done
ε-sch-dist (yes p) done | no ¬p = ⊥-elim (¬p p)
ε-sch-dist {l} {lₐ} (no ¬p) done with l ⊑? lₐ
ε-sch-dist (no ¬p) done | yes p = ⊥-elim (¬p p)
ε-sch-dist (no ¬p₁) done | no ¬p = hole
ε-sch-dist {l} {lₐ} (yes p) skip with l ⊑? lₐ
ε-sch-dist (yes p₁) (skip {s = s} {n = n}) | yes p rewrite sym (εˢ-append-yes {{n}} s p) = skip
ε-sch-dist (yes p) (skip {s = s} {n = n}) | no ¬p = ⊥-elim (¬p p)
ε-sch-dist {l} {lₐ} (no ¬p) skip with l ⊑? lₐ
ε-sch-dist (no ¬p) skip | yes p = ⊥-elim (¬p p)
ε-sch-dist (no ¬p₁) (skip {s = s} {n = n}) | no ¬p rewrite εˢ-append-no {{n}} s ¬p = hole
ε-sch-dist (yes p) hole = hole
ε-sch-dist (no ¬p) hole = hole

ε-sch-≡ : ∀ {l lₐ s₁ s₂} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (εˢ lₐ s₁) ≡ (εˢ lₐ s₂)
ε-sch-≡ {l} {lₐ} ¬p step with l ⊑? lₐ
ε-sch-≡ ¬p step | yes p = ⊥-elim (¬p p)
ε-sch-≡ ¬p₁ (step {s = s} {n = n}) | no ¬p rewrite εˢ-append-no {{n}} s ¬p = refl
ε-sch-≡ {lₐ = lₐ} ¬p (fork {s} {l} {n} p')  with l ⊑? lₐ
ε-sch-≡ ¬p (fork p') | yes p = ⊥-elim (¬p p)
ε-sch-≡ {lₐ = lₐ} ¬p₁ (fork {h = h} p') | no ¬p with h ⊑? lₐ
ε-sch-≡ ¬p₁ (fork p') | no ¬p | yes p = ⊥-elim (trans-⋢ p' ¬p₁ p) 
ε-sch-≡ ¬p₂ (fork {s} {l} {n} p') | no ¬p₁ | no ¬p rewrite εˢ-append-no {{n}} s ¬p₁ =  refl
ε-sch-≡ {l} {lₐ} ¬p (done {s = s} {n = n}) with l ⊑? lₐ
ε-sch-≡ ¬p (done {s = s} {n = n}) | yes p = ⊥-elim (¬p p)
ε-sch-≡ ¬p₁ (done {s = s} {n = n}) | no ¬p rewrite εˢ-append-no {{n}} s ¬p = refl
ε-sch-≡ {l} {lₐ} ¬p skip with l ⊑? lₐ
ε-sch-≡ ¬p skip | yes p = ⊥-elim (¬p p)
ε-sch-≡ ¬p₁ (skip {s = s} {n = n}) | no ¬p rewrite εˢ-append-no {{n}} s ¬p =  refl
ε-sch-≡ ¬p hole = refl


-- Determinism
determinism : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃
determinism step step = refl
determinism (fork p₁) (fork p₂) = refl
determinism done done = refl
determinism skip skip = refl
determinism hole hole = refl


open import Typed.Determinism.Concurrent (State) (_⟶_↑_) (determinism)
open import Security.Concurrent State _⟶_↑_ εˢ ε-sch-dist ε-sch-≡

