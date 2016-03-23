open import Types
open import Typed.Communication renaming (Event to Eventˢ)
open import Security.Base
open import Relation.Binary.PropositionalEquality

module Security.Concurrent (State : Set) (_⟶_↑_ :  ∀ {l} -> State -> State -> Message l -> Set)
                           (ε-state : Label -> State -> State) -- Erasure function of the scheduler state
                           (ε-sch-dist : ∀ {s₁ s₂ l lₐ} {m : Message l} -> (x : Dec (l ⊑ lₐ)) -> s₁ ⟶ s₂ ↑ m ->
                                                                        (ε-state lₐ s₁) ⟶ (ε-state lₐ s₂) ↑ (εᴹ x m))
                           (ε-sch-≡ : ∀ {s₁ s₂ l lₐ} {m : Message l} -> ¬ (l ⊑ lₐ) -> s₁ ⟶ s₂ ↑ m -> (ε-state lₐ s₁) ≡ (ε-state lₐ s₂))
                           where

open import Typed.Base
open import Typed.Semantics
open import Security.Distributivity
open import Typed.Concurrent State _⟶_↑_

-- Erasure of global configuration
εᵍ : ∀ {ls} -> Label -> Global ls -> Global ls
εᵍ lₐ ⟨ s , Σ , ps ⟩ = ⟨ ε-state lₐ s , εˢ lₐ Σ , ε-pools lₐ ps ⟩

--------------------------------------------------------------------------------

open import Data.Sum

εᵗ-extensional : ∀ {n l lₐ} (x y : Dec (l ⊑ lₐ)) (ts : Pool l n) -> εᵗ x ts ≡ εᵗ y ts
εᵗ-extensional (yes p) (yes p₁) [] = refl
εᵗ-extensional (yes p) (yes p₁) (x ◅ ts)
  rewrite ε-Mac-extensional (yes p) (yes p₁) x | εᵗ-extensional (yes p) (yes p₁) ts = refl
εᵗ-extensional (yes p) (yes p₁) ∙ = refl
εᵗ-extensional (yes p) (no ¬p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (yes p) ts = ⊥-elim (¬p p)
εᵗ-extensional (no ¬p) (no ¬p₁) ts = refl

εᵗ∙≡∙ : ∀ {l lₐ} -> (x : Dec (l ⊑ lₐ)) -> (n : ℕ) -> εᵗ x ∙ ≡ (∙ {n = n})
εᵗ∙≡∙ (yes p) _ = refl
εᵗ∙≡∙ (no ¬p) _ = refl

ε-▻-≡ : ∀ {n l lₐ} (p : l ⊑ lₐ) (t : Thread l) (ts : Pool l n) -> εᵗ (yes p) (ts ▻ t) ≡ (εᵗ (yes p) ts ▻ ε-Mac lₐ (yes p) t)
ε-▻-≡ p t [] = refl
ε-▻-≡ p t (x ◅ ts) rewrite ε-▻-≡ p t ts = refl
ε-▻-≡ p t ∙ = refl

ε-IsValue : ∀ {τ l lₐ} {t : CTerm (Mac l τ)} -> (p : l ⊑ lₐ) -> IsValue t -> IsValue (ε-Mac lₐ (yes p) t)
ε-IsValue p (Mac t) = Mac (ε _ t)
ε-IsValue p (Macₓ e) = Macₓ (ε _ e)

ε-Blocked : ∀ {l lₐ τ ls} {t : CTerm (Mac l τ)} {Σ : Store ls} -> (p : l ⊑ lₐ) -> Blocked Σ t -> Blocked (εˢ lₐ Σ) (ε-Mac lₐ (yes p) t)
ε-Blocked {l} {lₐ} p (onPut q r) with l ⊑? lₐ
ε-Blocked p₁ (onPut q r) | yes p = onPut q (ε-TypedIx p₁ _ q r)
ε-Blocked p (onPut q r) | no ¬p = ⊥-elim (¬p p)
ε-Blocked {l} {lₐ} p (onTake q r) with l ⊑? lₐ
ε-Blocked p₁ (onTake q r) | yes p = onTake q (ε-TypedIx p₁ _ q r)
ε-Blocked p (onTake q r) | no ¬p = ⊥-elim (¬p p)

fork-⊑ : ∀ {ls τ l h} {p₁ p₂ : Program ls (Mac l τ)} {t : Thread h }  -> p₁ ⟼ p₂ ↑ fork t -> l ⊑ h
fork-⊑ (fork p t s) = p

εᵗ-yes-≡ : ∀ {n l lₐ} -> (p : l ⊑ lₐ) (ts : Pool l n) (t : Thread l) -> εᵗ (yes p) (ts ▻ t) ≡ (εᵗ (yes p) ts ▻ ε-Mac _ (yes p) t)
εᵗ-yes-≡ p [] t = refl
εᵗ-yes-≡ p (x ◅ ts) t rewrite εᵗ-yes-≡ p ts t = refl
εᵗ-yes-≡ p ∙ t = refl

εᵉ : Label -> Event -> Event
εᵉ lₐ ∅ = ∅
εᵉ lₐ (fork t) = fork (ε lₐ t)

open Program

ε-IsFork : ∀ {lₐ τ l} {t : CTerm (Mac l τ)}(x : Dec (l ⊑ lₐ)) -> ¬ (IsFork t) -> ¬ (IsFork (ε-Mac lₐ x t))
ε-IsFork {t = t} x nF y = aux x t nF y
  where aux : ∀ {lₐ τ l} (x : Dec (l ⊑ lₐ)) (t : CTerm (Mac l τ)) -> ¬ (IsFork t) -> ¬ (IsFork (ε-Mac lₐ x t))
        aux (yes p) (Var x) nF ()
        aux (yes p) (App t t₁) nF ()
        aux (yes p) (If t Then t₁ Else t₂) nF ()
        aux (yes p) (Return t) nF ()
        aux (yes p) (t >>= t₁) nF ()
        aux (yes p) (Throw t) nF ()
        aux (yes p) (Catch t t₁) nF ()
        aux (yes p) (Mac t) nF ()
        aux (yes p) (Macₓ t) nF ()
        aux (yes p) (label x t) nF ()
        aux (yes p) (unlabel x t) nF ()
        aux (yes p) (join x t) nF ()
        aux (yes p) (read x t) nF ()
        aux (yes p) (write x t t₁) nF ()
        aux (yes p) (new x t) nF ()
        aux (yes p) (fork x t) nF _ = ⊥-elim (nF (fork x t))
        aux (yes p) (newMVar x) nF ()
        aux (yes p) (takeMVar t) nF ()
        aux (yes p) (putMVar t t₁) nF ()
        aux (yes p) ∙ nF ()
        aux {lₐ} (no ¬p) t nF x with ε-Mac _ (no ¬p) t | ε-Mac-CTerm≡∙ lₐ t ¬p
        aux (no ¬p) t nF () | .∙ | refl

ε-↑ : ∀ {l lₐ τ ls e} {p₁ p₂ : Program ls (Mac l τ)} -> (p : l ⊑ lₐ) -> p₁ ⟼ p₂ ↑ e ->
        let ⟨ Σ₁ ∥ t₁ ⟩ = p₁
            ⟨ Σ₂ ∥ t₂ ⟩ = p₂ in
        ⟨ εˢ lₐ Σ₁ ∥ ε-Mac lₐ (yes p) t₁ ⟩ ⟼ ⟨ εˢ lₐ Σ₂ ∥ ε-Mac lₐ (yes p) t₂ ⟩ ↑ (εᵉ lₐ e)
ε-↑ {lₐ = lₐ} p (fork {h = h} p₁ t s) = fork p₁ (ε-Mac lₐ (h ⊑? lₐ) t) (ε-Mac-dist lₐ (yes p) s)
ε-↑ {l} {lₐ} {p₁ = ⟨ Σ₁ ∥ t₁ ⟩} {⟨ Σ₂ ∥ t₂ ⟩ } p (none nF s) = none (ε-IsFork (yes p) nF) (ε-Mac-dist _ (yes p) s)

--------------------------------------------------------------------------------

ε-write-≡ : ∀ {l lₐ n ls} {ts : Pool l n} {ps₁ ps₂ : Pools ls} -> ¬ (l ⊑ lₐ) -> ps₂ ← ps₁ [ l ]≔ ts -> ε-pools lₐ ps₁ ≡ ε-pools lₐ ps₂
ε-write-≡ {l} {lₐ} ¬p Here with l ⊑? lₐ
ε-write-≡ ¬p Here | yes p = ⊥-elim (¬p p)
ε-write-≡ ¬p₁ Here | no ¬p = refl
ε-write-≡ ¬p (There x) rewrite ε-write-≡ ¬p x = refl

--------------------------------------------------------------------------------

-- Here n is implicit! we should expose it somehow
ε-read∙  : ∀ {l lₐ ls n} {ps : Pools ls} {ts : Pool l n} -> ¬ ( l ⊑ lₐ) -> ps [ l ]= ts -> ε-pools lₐ ps [ l ]= (∙ {n = n})
ε-read∙ {l} {lₐ} {ps = x ◅ ps} ¬p Here with l ⊑? lₐ
ε-read∙ {l} {lₐ} {._} {n'} {x ◅ ps} ¬p Here | yes p = ⊥-elim (¬p p)
ε-read∙ {l} {lₐ} {._} {n'} {x ◅ ps} ¬p₁ Here | no ¬p = Here
ε-read∙ {ps = x ◅ ps} ¬p (There q) = There (ε-read∙ ¬p q)

ε-readᵖ : ∀ {l lₐ n ls} {ps : Pools ls} {ts : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> ps [ l ]= ts -> ε-pools lₐ ps [ l ]= (εᵗ x ts)
ε-readᵖ {l} {lₐ} {ts = ts} x (Here ) rewrite εᵗ-extensional x (l ⊑? lₐ) ts = Here
ε-readᵖ x (There y) = There (ε-readᵖ x y)

ε-readᵗ : ∀ {l lₐ n n'} {ts : Pool l n'} {t : Thread l} -> (p : l ⊑ lₐ) -> ts [ n ]ᵗ= t ->  (εᵗ (yes p) ts) [ n ]ᵗ= ε-Mac lₐ (yes p) t
ε-readᵗ {l} {lₐ} p Here with l ⊑? lₐ
ε-readᵗ {t = t} p₁ Here | yes p rewrite ε-Mac-extensional (yes p₁) (yes p) t = Here
ε-readᵗ p Here | no ¬p = ⊥-elim (¬p p)
ε-readᵗ p (There x) = There (ε-readᵗ p x)

ε-read-hole : ∀ {l lₐ n ls} {ps : Pools ls} ->
              ps [ l ]= (∙ {n = n}) -> ε-pools lₐ ps [ l ]= (∙ {n = n})
ε-read-hole {l} {lₐ} {n} Here rewrite εᵗ∙≡∙ (l ⊑? lₐ) n = Here
ε-read-hole (There x) = There (ε-read-hole x)              

--------------------------------------------------------------------------------

ε-updateᵗ : ∀ {l lₐ n' n} {ts₁ ts₂ : Pool l n'} {t : Thread l} -> (p : l ⊑ lₐ) ->
               ts₂ ← ts₁ [ n ]ᵗ≔ t ->
               (εᵗ (yes p) ts₂) ← (εᵗ (yes p) ts₁) [ n ]ᵗ≔ (ε-Mac lₐ (yes p) t) 
ε-updateᵗ p ∙ = ∙
ε-updateᵗ p upd = upd
ε-updateᵗ p (skip x) = skip (ε-updateᵗ p x)

ε-updateᵖ : ∀ {l lₐ n ls} {ps₁ ps₂ : Pools ls} {ts : Pool l n} -> (p : l ⊑ lₐ) ->
             ps₂ ← ps₁ [ l ]≔ ts  ->
             (ε-pools lₐ ps₂) ← (ε-pools lₐ ps₁) [ l ]≔ (εᵗ (yes p) ts)
ε-updateᵖ {l} {lₐ} {ts = ts} p Here rewrite εᵗ-extensional (yes p) (l ⊑? lₐ) ts = Here
ε-updateᵖ p (There x) = There (ε-updateᵖ p x)

▻-≡ : ∀ {l lₐ n} (ts : Pool l n) (t : Thread l)  (x : Dec (l ⊑ lₐ)) -> (εᵗ x ts ▻ ε-Mac _ x t) ≡ εᵗ (l ⊑? lₐ) (ts ▻ t)
▻-≡ {l} {lₐ} ts t (yes p) rewrite εᵗ-extensional (l ⊑? lₐ) (yes p) (ts ▻ t) = sym (ε-▻-≡ p t ts)
▻-≡ {l} {lₐ} ts t (no ¬p) with l ⊑? lₐ
▻-≡ ts t (no ¬p) | yes p = ⊥-elim (¬p p)
▻-≡ ts t (no ¬p₁) | no ¬p = refl

ε-update-▻ : ∀ {l lₐ ls n} {ps₁ ps₂ : Pools ls} {ts : Pool l n} {t : Thread l} -> (x : Dec (l ⊑ lₐ)) ->
               ps₂ ← ps₁ [ l ]≔ (ts ▻ t) ->
               ε-pools lₐ ps₂ ← ε-pools lₐ ps₁ [ l ]≔ ((εᵗ x ts) ▻ (ε-Mac _ x t))
ε-update-▻ {l} {lₐ} {ts = ts} {t = t} x Here rewrite ▻-≡ ts t x = Here
ε-update-▻ x (There y) = There (ε-update-▻ x y)

--------------------------------------------------------------------------------

foo : ∀ {h lₐ n} -> (x : Dec (h ⊑ lₐ)) (t : Thread h) -> εᴱ lₐ (fork? t n) ≡ fork? (ε-Mac lₐ x t) n
foo x t with is∙? t
foo (yes p) .∙ | yes ∙ = refl
foo (no ¬p) .∙ | yes ∙ = refl
foo {h} {lₐ} (yes p) t | no ¬p with h ⊑? lₐ
foo (yes p) (Var x) | no ¬p | yes p' = refl
foo (yes p) (App t t₁) | no ¬p | yes p' = refl
foo (yes p) (If t Then t₁ Else t₂) | no ¬p | yes p' = refl
foo (yes p) (Return t) | no ¬p | yes p' = refl
foo (yes p) (t >>= t₁) | no ¬p | yes p' = refl
foo (yes p) (Throw t) | no ¬p | yes p' = refl
foo (yes p) (Catch t t₁) | no ¬p | yes p' = refl
foo (yes p) (Mac t) | no ¬p | yes p' = refl
foo (yes p) (Macₓ t) | no ¬p | yes p' = refl
foo (yes p) (unlabel x t) | no ¬p | yes p' = refl
foo (yes p) (read x t) | no ¬p | yes p' = refl
foo (yes p) (write x t t₁) | no ¬p | yes p' = refl
foo (yes p) (fork x t) | no ¬p | yes p' = refl
foo (yes p) (takeMVar t) | no ¬p | yes p' = refl
foo (yes p) (putMVar t t₁) | no ¬p | yes p' = refl
foo (yes p) ∙ | no ¬p | yes p' = ⊥-elim (¬p ∙)
... | no ¬p' = ⊥-elim (¬p' p)
foo {h} {lₐ} (no ¬p₁) t | no ¬p rewrite ε-Mac-CTerm≡∙ _ t ¬p₁ with h ⊑? lₐ
... | yes p = ⊥-elim (¬p₁ p)
... | no _ = refl

-- TODO refactoring
εᵍ-dist : ∀ {l n ls} {g₁ g₂ : Global ls} -> (lₐ : Label) -> l , n ⊢ g₁ ↪ g₂ -> l , n ⊢ (εᵍ lₐ g₁) ↪ (εᵍ lₐ g₂)
εᵍ-dist {l} lₐ (step r₁ r₂ st sc w₁ w₂) with l ⊑? lₐ | ε-sch-dist (l ⊑? lₐ) sc
εᵍ-dist {l} {n} lₐ (step {ts₂ = ts} r₁ r₂ st sc w₁ w₂) | yes p | sc' with ε-updateᵗ p w₁ | ε-updateᵖ p w₂ 
... | x | y  rewrite εᵗ-extensional (yes p) (l ⊑? lₐ) ts = step (ε-readᵖ (yes p) r₁) (ε-readᵗ p r₂) (ε-↑ p st) sc' x y
εᵍ-dist {l} {n}  lₐ (step r₁ r₂ st sc w₁ w₂) | no ¬p | sc' with ε-read∙ ¬p r₁
... | x rewrite εˢ-≡ lₐ ¬p (stepOf st) | ε-write-≡ ¬p w₂ | ε-sch-≡ ¬p sc = hole x sc'
εᵍ-dist {l} lₐ (fork r₁ r₂ r₃ st sc  w₁ w₂ w₃) with l ⊑? lₐ | ε-sch-dist (l ⊑? lₐ) sc
εᵍ-dist {l} {n} lₐ (fork {h = h} {tsʰ = tsʰ} {tʰ = tʰ} r₁ r₂ r₃ st sc w₁ w₂ w₃) | yes p | sc' with h ⊑? lₐ | ε-update-▻ {ts = tsʰ} {t = tʰ} (h ⊑? lₐ) w₃
εᵍ-dist lₐ (fork {h = h} {nʰ = nʰ} {tsʰ = tsʰ} {tʰ = tʰ} r₁ r₂ r₃ st sc w₁ w₂ w₃) | yes p | sc' | yes p₁ | u
  rewrite foo {n = nʰ} (h ⊑? lₐ) tʰ | ε-Mac-extensional (yes p₁) (h ⊑? lₐ) tʰ
  = fork (ε-readᵖ (yes p) r₁) (ε-readᵗ p r₂) (ε-readᵖ (yes p₁) r₃)
      (ε-↑ p st) sc' (ε-updateᵗ p w₁) (ε-updateᵖ p w₂) u
εᵍ-dist lₐ (fork {h = h} {nʰ = nʰ} {tsʰ = tsʰ} {tʰ = tʰ} r₁ r₂ r₃ st sc w₁ w₂ w₃) | yes p | sc' | no ¬p | u
  rewrite foo {n = nʰ} (h ⊑? lₐ) tʰ | ε-Mac-extensional (no ¬p) (h ⊑? lₐ) tʰ
  = fork (ε-readᵖ (yes p) r₁) (ε-readᵗ p r₂) (ε-readᵖ (no ¬p) r₃)
      (ε-↑ p st) sc' (ε-updateᵗ p w₁) (ε-updateᵖ p w₂) u
εᵍ-dist {l} {n} lₐ (fork r₁ r₂ r₃ st sc w₁ w₂ w₃) | no ¬p | sc' with ε-read∙ ¬p r₁ 
... | x rewrite εˢ-≡ lₐ ¬p (stepOf st) | ε-write-≡ ¬p w₂ | ε-write-≡ (trans-⋢ (fork-⊑ st) ¬p) w₃ | ε-sch-≡ ¬p sc = hole x sc'
εᵍ-dist {l} lₐ (hole r sc) with l ⊑? lₐ
εᵍ-dist lₐ (hole r sc) | yes p = hole (ε-read-hole r) (ε-sch-dist (yes p) sc)
εᵍ-dist lₐ (hole r sc) | no ¬p = hole (ε-read-hole r) (ε-sch-dist (no ¬p) sc)
εᵍ-dist {l} lₐ (skip r₁ r₂ b sc ) with l ⊑? lₐ | ε-sch-dist (l ⊑? lₐ) sc
εᵍ-dist lₐ (skip r₁ r₂ b sc) | yes p | sc' = skip (ε-readᵖ (yes p) r₁) (ε-readᵗ p r₂) (ε-Blocked p b) sc'
εᵍ-dist lₐ (skip r₁ r₂ b sc) | no ¬p | sc' rewrite ε-sch-≡ ¬p sc = hole (ε-read∙ ¬p r₁) sc'
εᵍ-dist {l} lₐ (exit r₁ r₂ isV sc) with l ⊑? lₐ | ε-sch-dist (l ⊑? lₐ) sc
εᵍ-dist lₐ (exit r₁ r₂ isV sc) | yes p | sc' = exit (ε-readᵖ (yes p) r₁) (ε-readᵗ p r₂) (ε-IsValue p isV) sc'
εᵍ-dist {l} {n} lₐ (exit r₁ r₂ isV sc) | no ¬p | sc' rewrite ε-sch-≡ ¬p sc = hole (ε-read∙ ¬p r₁) sc'
