module Schedulers.RoundRobin where

open import Types
open import Concurrent.Communication renaming (_,_,_ to ⟪_,_,_⟫)
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

open import Concurrent.Security.Erasure
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


-- structural low-equivalence

mutual
  data _≈ˢ_ {{lₐ : Label}} : State -> State -> Set where
    nil : [] ≈ˢ []
    consᴸ : ∀ {l n s₁ s₂} -> (p : l ⊑ lₐ) ->  s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ((l , n) ∷ s₁) ≈ˢ ((l , n) ∷ s₂)
    cons₁ᴴ : ∀ {h n s₁ s₂ } -> (¬p  : ¬ (h ⊑ lₐ)) -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ((h , n) ∷ s₁) ≈ˢ s₂
    cons₂ᴴ : ∀ {h n s₁ s₂} -> (¬p  : ¬ (h ⊑ lₐ)) -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> s₁ ≈ˢ ((h , n) ∷ s₂)

  _≈ˢ-⟨_⟩_ : State -> Label -> State -> Set
  s₁ ≈ˢ-⟨ lₐ ⟩ s₂ = s₁ ≈ˢ s₂

≈ˢ-≡ : ∀ {lₐ s₁ s₂} -> s₁ ≈ˢ s₂ -> εˢ lₐ s₁ ≡ εˢ lₐ s₂
≈ˢ-≡ nil = refl
≈ˢ-≡ {lₐ} (consᴸ {l} p x) with l ⊑? lₐ
≈ˢ-≡ (consᴸ p₁ x) | yes p rewrite ≈ˢ-≡ x = refl
≈ˢ-≡ (consᴸ p x) | no ¬p = ⊥-elim (¬p p)
≈ˢ-≡ {lₐ} (cons₁ᴴ {h} ¬p x) with h ⊑? lₐ
≈ˢ-≡ (cons₁ᴴ ¬p x) | yes p = ⊥-elim (¬p p)
≈ˢ-≡ (cons₁ᴴ ¬p₁ x) | no ¬p =  ≈ˢ-≡ x
≈ˢ-≡ {lₐ} (cons₂ᴴ {h} ¬p x) with h ⊑? lₐ
≈ˢ-≡ (cons₂ᴴ ¬p x) | yes p = ⊥-elim (¬p p)
≈ˢ-≡ (cons₂ᴴ ¬p₁ x) | no ¬p = ≈ˢ-≡ x

∷-≡ : ∀ {x y : Label × ℕ} {s₁ s₂ : State} -> _≡_ {A = State} (x ∷ s₁) (y ∷ s₂) -> x ≡ y × s₁ ≡ s₂
∷-≡ refl = refl , refl

≡-≈ˢ : ∀ {lₐ s₁ s₂} -> εˢ lₐ s₁ ≡ εˢ lₐ s₂ -> s₁ ≈ˢ s₂

≡-≈ˢ₁ : ∀ {lₐ l n s₁ s₂} -> l ⊑ lₐ -> (l , n) ∷ εˢ lₐ s₁ ≡ εˢ lₐ s₂ -> ((l , n) ∷ s₁) ≈ˢ-⟨ lₐ ⟩ s₂
≡-≈ˢ₁ {s₂ = []} p ()
≡-≈ˢ₁ {lₐ} {s₂ = (l' , n') ∷ s₂} p eq with l' ⊑? lₐ
≡-≈ˢ₁ {lₐ} {l} {n} {s₁} {(l' , n') ∷ s₂} p₁ eq | yes p with ∷-≡ eq
≡-≈ˢ₁ {lₐ} {l'} {n'} {s₁} {(.l' , .n') ∷ s₂} p₁ eq | yes p | refl , eq₂ = consᴸ p₁ (≡-≈ˢ eq₂)
≡-≈ˢ₁ {lₐ} {l} {n} {s₁} {(l' , n') ∷ s₂} p eq | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ₁ p eq)

≡-≈ˢ {s₁ = []} {[]} eq = nil
≡-≈ˢ {lₐ} {s₁ = []} {(l , n) ∷ s₂} eq with l ⊑? lₐ
≡-≈ˢ {lₐ} {[]} {(l , n) ∷ s₂} () | yes p
≡-≈ˢ {lₐ} {[]} {(l , n) ∷ s₂} eq | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ eq)
≡-≈ˢ {lₐ} {s₁ = (l , n) ∷ s₁} {[]} eq with l ⊑? lₐ
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {[]} () | yes p
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {[]} eq | no ¬p = cons₁ᴴ ¬p (≡-≈ˢ eq)
≡-≈ˢ {lₐ} {s₁ = (l , n) ∷ s₁} {(l' , n') ∷ s₂} eq with l ⊑? lₐ
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p with l' ⊑? lₐ
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p₁ | yes p with ∷-≡ eq
≡-≈ˢ {lₐ} {(l' , n) ∷ s₁} {(.l' , .n) ∷ s₂} eq | yes p₁ | yes p | refl , eq₂ = consᴸ p₁ (≡-≈ˢ eq₂)
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ₁ p eq)
≡-≈ˢ {lₐ} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | no ¬p = cons₁ᴴ ¬p (≡-≈ˢ eq)

open import Function

open import Concurrent.Security.Scheduler State _⟶_↑_ εˢ hiding  ( _≈ˢ-⟨_⟩_  ; _≈ˢ_)

++-≈ˢ : ∀ {s₁ s₂ lₐ x} -> s₁ ≈ˢ s₂ -> (s₁ ++ x) ≈ˢ (s₂ ++ x)
++-≈ˢ {x = x} nil = ≡-≈ˢ refl
++-≈ˢ (consᴸ p x₁) = consᴸ p (++-≈ˢ x₁)
++-≈ˢ (cons₁ᴴ ¬p x₁) = cons₁ᴴ ¬p (++-≈ˢ x₁)
++-≈ˢ (cons₂ᴴ ¬p x₁) = cons₂ᴴ ¬p (++-≈ˢ x₁)

lemma' : ∀ {s₁ s₂ n l h} {m : Message l} -> s₁ ⟶ s₂ ↑ m -> (s₁ ++ [ h , n ]) ⟶ s₂ ↑ m
lemma' {s₁ = (l , n) ∷ s} {s₂ = .(s ++ [ l , n ])} step = {!step!}
lemma' (fork p) = {!!}
lemma' done = {!!}
lemma' skip = {!!}
lemma' hole = {!!}

lemma : ∀ {n lₐ s₁ s₂ h n' l} {m : Message l} -> n , lₐ ⊢ s₁ ⟶⋆ s₂ ↑ m -> n , lₐ ⊢ (s₁ ++ [ h , n' ]) ⟶⋆ s₂ ↑ m
lemma (aligned x) = aligned (lemma' x)
lemma (high x x₁) = high x {!!}
--  where aux : (e : Event) -> 
scheduler-ni : ∀ {s₁ s₁' s₂ l lₐ} {m : Message l} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ m -> s₁ ≈ˢ-⟨ lₐ ⟩ s₁' ->
                           ∃ λ s₂' -> ∃ λ n -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' × n , lₐ ⊢ s₁' ⟶⋆ s₂' ↑ m
scheduler-ni p hole nil = [] , (zero , (nil , (aligned hole)))
scheduler-ni p step (consᴸ p' eq) = _ , (zero , (++-≈ˢ eq , (aligned step)))
scheduler-ni p (fork p') (consᴸ p₁ eq) = _ , (0 , ({!!}  , (aligned (fork p')))) -- induction
scheduler-ni p done (consᴸ p' eq) = _ , (zero , (eq , (aligned done)))
scheduler-ni p skip (consᴸ p' eq) = _ , (zero , (++-≈ˢ eq , (aligned skip)))
scheduler-ni p hole (consᴸ p' eq) = _ , (zero , (consᴸ p' eq , (aligned hole))) -- {!!} , ({!!} , ({!!} , (aligned {!s!})))
scheduler-ni p step (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
scheduler-ni p (fork p₁) (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
scheduler-ni p done (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
scheduler-ni p skip (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
scheduler-ni p hole (cons₁ᴴ ¬p x) = _ , (zero , ((cons₁ᴴ ¬p x) , (aligned hole))) 
scheduler-ni {s₁' = (h , n') ∷ s₁'} p s (cons₂ᴴ ¬p x) with scheduler-ni p s x
scheduler-ni {s₁} {s₁' = (h , n') ∷ s₁'} {s₂} {l} {lₐ} {m = m} p s (cons₂ᴴ ¬p x) | s₃ , n , eq' , ss = s₃ , (suc n , (eq' , high ¬p aux))
  where aux : (e : Event) -> ∃ λ s₂ -> ((h , n') ∷ s₁') ⟶ s₂ ↑ ⟪ h , n' , e ⟫  × n , lₐ ⊢ s₂ ⟶⋆ s₃ ↑ m
        aux NoStep = {!!} , (skip , {!ss!}) -- Here it doesn't work because ss is s₁' ⟶ s₃, but now I have also to take care of (h , n) in the end
        -- In other words s₁' ⟶ s₃' does not imply that s₁' ++ [ h , n ] ⟶ s₃
        aux Step = {!!} , (step , {!ss!})
        aux Done = {!!} , (done , ss)
        aux (Fork h₁ n₁) = {!!} , ({!fork!} , {!!})
        aux ∙ = {!!} , (hole , {!!}) -- Here I don't make any progress
        
open import Concurrent.Determinism (State) (_⟶_↑_) (determinism)
-- open import Concurrent.Security.NonInterference State _⟶_↑_ εˢ ε-sch-dist ε-sch-≡
