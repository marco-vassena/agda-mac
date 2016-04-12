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

++-≡ˢ :  ∀ {s₁ s₂ lₐ x} -> s₁ ≈ˢ s₂ -> εˢ lₐ (s₁ ++ x) ≡ εˢ lₐ (s₂ ++ x)
++-≡ˢ eq = ≈ˢ-≡ (++-≈ˢ eq)

++'-≈ˢ : ∀ {s₁ s₂ lₐ h} {{n}} -> ¬ (h ⊑ lₐ) -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> s₁ ≈ˢ-⟨ lₐ ⟩ (s₂ ++ [ h , n ])
++'-≈ˢ ¬p nil = cons₂ᴴ ¬p nil
++'-≈ˢ ¬p (consᴸ p x) = consᴸ p (++'-≈ˢ ¬p x)
++'-≈ˢ ¬p (cons₁ᴴ ¬p₁ x) = cons₁ᴴ ¬p₁ (++'-≈ˢ ¬p x)
++'-≈ˢ ¬p (cons₂ᴴ ¬p₁ x) = cons₂ᴴ ¬p₁ (++'-≈ˢ ¬p x)

-- I don't need the offset, but the number of rounds to wait
offset : ∀ {s₁ s₂ lₐ} -> s₁ ≈ˢ-⟨ lₐ ⟩ s₂ -> ℕ
offset nil = 0
offset (consᴸ p x) = 0
offset (cons₁ᴴ ¬p x) = suc (offset x)
offset (cons₂ᴴ ¬p x) = suc (offset x) 

≤-offset-++ : ∀ {s₁ s₂ l m h lₐ} {{n : ℕ}} -> (¬p : ¬ (h ⊑ lₐ)) (p : l ⊑ lₐ) -> (eq : ((l , m) ∷ s₁) ≈ˢ-⟨ lₐ ⟩ s₂) -> offset (++'-≈ˢ {{n}} ¬p eq) ≤ offset eq
≤-offset-++ ¬p p (consᴸ p₁ x) = z≤n
≤-offset-++ ¬p p (cons₁ᴴ ¬p₁ x) = ⊥-elim (¬p₁ p)
≤-offset-++ ¬p p (cons₂ᴴ ¬p₁ x) = s≤s (≤-offset-++ ¬p p x)

refl-≤ : ∀ {n} -> n ≤ n
refl-≤ {zero} = z≤n
refl-≤ {suc n} = s≤s refl-≤

open import Data.Sum

--------------------------------------------------------------------------------
-- TODO move to Concurrent.Security.Scheduler

data CloseUpStep {h lₐ s₁ s₁'} (m : Message h) (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₁') : Set where
  cus : ∀ {s₂'} -> s₁' ⟶ s₂' ↑ m -> (eq' : s₁ ≈ˢ-⟨ lₐ ⟩ s₂' ) -> offset eq > offset eq' -> CloseUpStep m eq

data Aligner {l lₐ s₁ s₁'} (m : Message l) (s₂ : State) (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₁') : Set where
  aligned : ∀ {s₂'} ->  s₁' ⟶ s₂' ↑ m -> Aligner m s₂ eq
  high : ∀ {h n} -> ¬ (h ⊑ lₐ) -> ({e : Event} -> e ≢ ∙ -> CloseUpStep ⟪ h , n , e ⟫ eq) -> Aligner m s₂ eq

--------------------------------------------------------------------------------

aux : ∀ {s h l n n' s₁' lₐ} -> (eq : ((l , n') ∷ s) ≈ˢ-⟨ lₐ ⟩ s₁') -> l ⊑ lₐ -> (¬p : ¬ (h ⊑ lₐ)) ->
           {e : Event} -> e ≢ ∙ -> CloseUpStep {s₁' = (h , n) ∷ s₁'} ⟪ h , n , e ⟫ (cons₂ᴴ ¬p eq)
aux eq p ¬p {NoStep} e≠∙ = cus skip (++'-≈ˢ ¬p eq) (s≤s (≤-offset-++ ¬p p eq)) -- (≤-offset-++ ¬p p (cons₂ᴴ ¬p eq))
aux eq p ¬p {Step} e≠∙ = cus step (++'-≈ˢ ¬p eq) (s≤s (≤-offset-++ ¬p p eq))
aux eq p ¬p {Done} e≠∙ = cus done eq (s≤s refl-≤)
aux eq p ¬p {Fork h₁ n₁} e≠∙ = cus (fork {!!}) (cons₂ᴴ {!!} ((++'-≈ˢ ¬p eq))) (s≤s {!!}) -- This won't hold we need the position of the spawned threads
aux eq p ¬p {∙} e≠∙ = ⊥-elim (e≠∙ refl) -- Here we are not making any progress (i.e. consuming s₁', hence we need to rule out ∙


align : ∀ {s₁ s₂ s₁' l lₐ} {m : Message l} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ m -> (eq : s₁ ≈ˢ-⟨ lₐ ⟩ s₁') -> Aligner m s₂ eq
align p hole nil = aligned hole
align p step (consᴸ p₁ x) = aligned step
align p (fork p₁) (consᴸ p₂ x) = aligned (fork p₁)
align p done (consᴸ p₁ x) = aligned done
align p skip (consᴸ p₁ x) = aligned skip
align p hole (consᴸ p₁ x) = aligned hole
align p step (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
align p (fork p₁) (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
align p done (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
align p skip (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
align p hole (cons₁ᴴ ¬p x) = aligned hole
align {s₁' = (h , n) ∷ s₁'} p step (cons₂ᴴ ¬p eq) = high ¬p (aux eq p ¬p )
align {s₁' = (h , n) ∷ s₁'} p (fork p₁) (cons₂ᴴ ¬p eq) = high ¬p (aux eq p ¬p)
align {s₁' = (h , n) ∷ s₁'} p done (cons₂ᴴ ¬p eq) = high ¬p (aux eq p ¬p )
align {s₁' = (h , n) ∷ s₁'} p skip (cons₂ᴴ ¬p eq) = high ¬p (aux eq p ¬p )
align {s₁' = (h , n) ∷ s₁'} p hole (cons₂ᴴ ¬p eq) = aligned hole

-- confluent : ∀ {s₁ s₁' s₂ l lₐ } {m : Message l} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ m -> s₁ ≈ˢ-⟨ lₐ ⟩ s₁' ->
--                   ∃ λ n -> Confluent m lₐ s₁' s₂ n
                  
--                   -- s₂ ≈ˢ-⟨ lₐ ⟩ s₂' × n , lₐ ⊢ s₁' ⟶⋆ s₂' ↑ m
-- confluent p hole nil = zero , aligned hole refl
-- confluent p step (consᴸ p₁ eq) = zero , aligned step (++-≡ˢ eq)
-- confluent p (fork p₁) (consᴸ p₂ eq) = zero , (aligned (fork p₁) {!!}) -- lemma
-- confluent p done (consᴸ p₁ eq) = 0 , aligned done (≈ˢ-≡ eq)
-- confluent p skip (consᴸ p₁ eq) = 0 , (aligned skip (++-≡ˢ eq))
-- confluent p hole (consᴸ p₁ eq) = 0 , (aligned hole (≈ˢ-≡ (consᴸ p₁ eq)))
-- confluent p step (cons₁ᴴ ¬p eq) = ⊥-elim (¬p p)
-- confluent p (fork p₁) (cons₁ᴴ ¬p eq) = ⊥-elim (¬p p)
-- confluent p done (cons₁ᴴ ¬p eq) = ⊥-elim (¬p p)
-- confluent p skip (cons₁ᴴ ¬p eq) = ⊥-elim (¬p p)
-- confluent p hole (cons₁ᴴ ¬p eq) = 0 , (aligned hole (≈ˢ-≡ (cons₁ᴴ ¬p eq)))
-- confluent {s₁} {s₁' = (h , n') ∷ s₁'} {s₂} {l} {lₐ} {m = m} p s (cons₂ᴴ ¬p eq) with confluent p s eq
-- ... | n , x = {!!} , (high ¬p {!aux!}) --  (suc n) , (high ¬p aux)
--   where aux : {e : Event} -> e ≢ ∙ -> ∃ (λ s₃ → ((h , n') ∷ s₁') ⟶ s₃ ↑ ⟪ h , n' , e ⟫ × Confluent m lₐ s₃ s₂ n)
--         aux {e} e≠∙ = {!!}
        
-- scheduler-ni : ∀ {s₁ s₁' s₂ l lₐ} {m : Message l} -> l ⊑ lₐ -> s₁ ⟶ s₂ ↑ m -> s₁ ≈ˢ-⟨ lₐ ⟩ s₁' ->
--                            ∃ λ s₂' -> ∃ λ n -> s₂ ≈ˢ-⟨ lₐ ⟩ s₂' × n , lₐ ⊢ s₁' ⟶⋆ s₂' ↑ m
-- scheduler-ni p hole nil = [] , (zero , (nil , (aligned hole)))
-- scheduler-ni p step (consᴸ p' eq) = _ , (zero , (++-≈ˢ eq , (aligned step)))
-- scheduler-ni p (fork p') (consᴸ p₁ eq) = _ , (0 , ({!!}  , (aligned (fork p')))) -- induction
-- scheduler-ni p done (consᴸ p' eq) = _ , (zero , (eq , (aligned done)))
-- scheduler-ni p skip (consᴸ p' eq) = _ , (zero , (++-≈ˢ eq , (aligned skip)))
-- scheduler-ni p hole (consᴸ p' eq) = _ , (zero , (consᴸ p' eq , (aligned hole))) -- {!!} , ({!!} , ({!!} , (aligned {!s!})))
-- scheduler-ni p step (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- scheduler-ni p (fork p₁) (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- scheduler-ni p done (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- scheduler-ni p skip (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- scheduler-ni p hole (cons₁ᴴ ¬p x) = _ , (zero , ((cons₁ᴴ ¬p x) , (aligned hole))) 
-- scheduler-ni {s₁' = (h , n') ∷ s₁'} p s (cons₂ᴴ ¬p x) with scheduler-ni p s x
-- scheduler-ni {s₁} {s₁' = (h , n') ∷ s₁'} {s₂} {l} {lₐ} {m = m} p s (cons₂ᴴ ¬p x) | s₃ , n , eq' , ss = s₃ , (suc n , (eq' , high ¬p aux))
--   where aux : (e : Event) -> ∃ λ s₂ -> ((h , n') ∷ s₁') ⟶ s₂ ↑ ⟪ h , n' , e ⟫  × n , lₐ ⊢ s₂ ⟶⋆ s₃ ↑ m
--         aux NoStep = {!2!} , (skip , {!ss!}) -- Here it doesn't work because ss is s₁' ⟶ s₃, but now I have also to take care of (h , n) in the end
--         -- In other words s₁' ⟶ s₃' does not imply that s₁' ++ [ h , n ] ⟶ s₃
--         aux Step = {!!} , (step , {!ss!})
--         aux Done = {!!} , (done , ss)
--         aux (Fork h₁ n₁) = {!!} , ({!fork!} , {!!})
--         aux ∙ = {!!} , (hole , {!!}) -- Here I don't make any progress
        
open import Concurrent.Determinism (State) (_⟶_↑_) (determinism)
-- open import Concurrent.Security.NonInterference State _⟶_↑_ εˢ ε-sch-dist ε-sch-≡
