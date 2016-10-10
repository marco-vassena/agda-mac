open import Lattice
open import Scheduler using (Scheduler)

-- open import Concurrent.Communication
-- open import Relation.Binary.PropositionalEquality
--open import Concurrent.Security.Erasure hiding (εˢ-≡)

module Concurrent.Security.Distributivity (𝓛 : Lattice) (𝓢 : Scheduler 𝓛) where

open import Types 𝓛
open import Scheduler 𝓛

open Scheduler.Scheduler using (ε-sch-dist ; ε-sch-≡)

import Sequential.Calculus as S
open module S1 = S 𝓛

import Sequential.Semantics as S₂
open module S2 = S₂ 𝓛

open import Sequential.Security 𝓛

import Sequential.Security.Erasure.Graph as SG
open module S3 = SG 𝓛

import Concurrent.Calculus
open module C = Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢
open import Concurrent.Security.Erasure.Base 𝓛 𝓢

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

Value-ε : ∀ {τ l lₐ} {t : CTerm (Mac l τ)} -> (p : l ⊑ lₐ) -> IsValue (ε-Mac lₐ (yes p) t) -> IsValue t
Value-ε {τ} {l} {lₐ} {t = t} p isV = aux (ε-Mac-yes-ErasureIso (Macᴸ p) p t) isV
  where aux : ∀ {t tᵉ : CTerm (Mac l τ)} {nonS : Insensitive lₐ (Mac l τ)} -> ErasureIso nonS t tᵉ -> IsValue tᵉ -> IsValue t
        aux (SG.Mac p₁ x) (S.Mac t₁) = S.Mac _
        aux (SG.Macₓ p₁ e₁) (S.Macₓ e) = S.Macₓ _



PRedex-ε : ∀ {lₐ τ} {c cᵉ : CTerm τ} {nonS : Insensitive lₐ τ} -> ErasureIso nonS c cᵉ -> PRedex cᵉ -> PRedex c
PRedex-ε (SG.App nonS e₁ e₂) (S₂.Step (S₂.AppL s)) with PRedex-ε e₁ (Step s)
... | Step s' = S₂.Step (S₂.AppL s')
PRedex-ε (SG.App nonS (SG.Abs x₃) x₂) (S₂.Step S₂.Beta) = Step Beta
PRedex-ε (SG.Ite nonS e₁ e₂ e₃) (S₂.Step (S₂.IfCond x)) with PRedex-ε e₁ (Step x)
... | Step s' = S₂.Step (S₂.IfCond s')
PRedex-ε (SG.Ite nonS SG.True e₂ e₃) (S₂.Step S₂.IfTrue) = S₂.Step S₂.IfTrue
PRedex-ε (SG.Ite nonS SG.False e₂ e₁) (S₂.Step S₂.IfFalse) = S₂.Step S₂.IfFalse
PRedex-ε (SG.unId nonS e) (S₂.Step (S₂.unIdCtx x)) with PRedex-ε e (Step x)
... | Step s' = S₂.Step (S₂.unIdCtx s')
PRedex-ε (SG.unId nonS (SG.Id x)) (S₂.Step S₂.unId) = S₂.Step S₂.unId
PRedex-ε (e SG.<*>ᴵ e₁) (S₂.Step (S₂.appFunIdCtx₁ x₂)) with PRedex-ε e (Step x₂)
... | Step s' = S₂.Step (S₂.appFunIdCtx₁ s')
PRedex-ε (SG.Id (SG.Iso nonS e₁) SG.<*>ᴵ e₂) (S₂.Step (S₂.appFunIdCtx₂ x₂)) with PRedex-ε e₁ (Step x₂)
... | Step s' = S₂.Step (S₂.appFunIdCtx₂ s')
PRedex-ε (SG.Id (SG.Iso ._ (SG.Abs x₂)) SG.<*>ᴵ e₁) (S₂.Step (S₂.appFunIdCtx₃ x₄)) with PRedex-ε e₁ (Step x₄)
... | Step s' = S₂.Step (S₂.appFunIdCtx₃ s')
PRedex-ε (SG.Id (SG.Iso ._ (SG.Abs x₂)) SG.<*>ᴵ SG.Id x₃) (S₂.Step S₂.appFunId) = S₂.Step S₂.appFunId
PRedex-ε (SG.Return p x) (S₂.Step S₂.Return) = S₂.Step S₂.Return
PRedex-ε (SG.Throw p e₁) (S₂.Step S₂.Throw) = S₂.Step S₂.Throw
PRedex-ε (SG.Bind p (SG.Mac .p x) e₁) (S₂.Step S₂.Bind) = S₂.Step S₂.Bind
PRedex-ε (SG.Bind p (SG.Macₓ .p e₁) e₂) (S₂.Step S₂.BindEx) = S₂.Step S₂.BindEx
PRedex-ε (SG.Catch p (SG.Mac .p x) e₁) (S₂.Step S₂.Catch) = S₂.Step S₂.Catch
PRedex-ε (SG.Catch p (SG.Macₓ .p e₁) e₂) (S₂.Step S₂.CatchEx) = S₂.Step S₂.CatchEx
PRedex-ε (SG.labelᴸ p₁ p p₃ x) (S₂.Step (S₂.label .p)) = S₂.Step (S₂.label p)
PRedex-ε (SG.labelᴴ p₁ p p₃ x) (S₂.Step (S₂.label∙ .p)) = S₂.Step (S₂.label p)
PRedex-ε (SG.label∙ p₁ p x) (S₂.Step (S₂.label∙ .p)) = S₂.Step (label∙ p)
PRedex-ε (SG.unlabel p₁ p (SG.Iso nonS x)) (S₂.Step (S₂.unlabelCtx₁ .p x₁)) with PRedex-ε x (Step x₁)
... | Step s' = S₂.Step (S₂.unlabelCtx₁ p s')
PRedex-ε (SG.unlabel p₁ p (SG.Res∙ ¬p x)) (S₂.Step (S₂.unlabelCtx₁ .p x₁)) = ⊥-elim (¬p (trans-⊑ p p₁))
--... | r = {!!}
PRedex-ε (SG.unlabel p₁ p (SG.Iso .(SG.Resᴸ p₂) (SG.Res p₂ (SG.Iso nonS x)))) (S₂.Step (S₂.unlabelCtx₂ .p x₁))
  with PRedex-ε x (Step x₁)
... | Step s' = S₂.Step (S₂.unlabelCtx₂ p s')
PRedex-ε (SG.unlabel p₁ p (SG.Res∙ ¬p x)) (S₂.Step (S₂.unlabelCtx₂ .p x₁)) = ⊥-elim (¬p (trans-⊑ p p₁))
PRedex-ε (SG.unlabel p₁ p (SG.Iso .(SG.Resᴸ p₂) (SG.Res p₂ (SG.Iso ._ (SG.Id x))))) (S₂.Step (S₂.unlabel .p)) = S₂.Step (S₂.unlabel p)
PRedex-ε (SG.unlabel p₁ p (SG.Res∙ ¬p x)) (S₂.Step (S₂.unlabel .p)) = ⊥-elim (¬p (trans-⊑ p p₁))
PRedex-ε (SG.unlabel p₁ p (SG.Iso .(SG.Resᴸ p₂) (SG.Resₓ p₂ x))) (S₂.Step (S₂.unlabelEx .p)) = S₂.Step (S₂.unlabelEx p)
PRedex-ε (SG.unlabel p₁ p (SG.Res∙ ¬p x)) (S₂.Step (S₂.unlabelEx .p)) = ⊥-elim (¬p (trans-⊑ p p₁))
PRedex-ε (SG.Star p e e₁) (S₂.Step (S₂.appFunCtx₁ x₂)) with PRedex-ε e (Step x₂)
... | Step s' = S₂.Step (S₂.appFunCtx₁ s')
PRedex-ε (SG.Star p (SG.Res .p (SG.Iso nonS x₁)) e₁) (S₂.Step (S₂.appFunCtx₂ x₃)) with PRedex-ε e₁ (Step x₃)
... | Step s' = S₂.Step (S₂.appFunCtx₂ s')
PRedex-ε (SG.Star p (SG.Resₓ .p e₁) e₂) (S₂.Step (S₂.appFunCtx₂ₓ x₃)) with PRedex-ε e₂ (Step x₃)
... | Step s' = S₂.Step (S₂.appFunCtx₂ₓ s')
PRedex-ε (SG.Star p (SG.Res .p x₁) (SG.Res .p x₂)) (S₂.Step S₂.appFun) = S₂.Step S₂.appFun
PRedex-ε (SG.Star p (SG.Resₓ .p e₁) (SG.Res .p x₁)) (S₂.Step S₂.appFun₁ₓ) = S₂.Step S₂.appFun₁ₓ
PRedex-ε (SG.Star p (SG.Res .p x) (SG.Resₓ .p e₂)) (S₂.Step S₂.appFun₂ₓ) = S₂.Step S₂.appFun₂ₓ
PRedex-ε (SG.Star p (SG.Resₓ .p e) (SG.Resₓ .p e₃)) (S₂.Step S₂.appFun₁₂ₓ) = S₂.Step S₂.appFun₁₂ₓ
PRedex-ε (SG.Star∙ p e e₁) (S₂.Step (S₂.appFunCtx∙₁ x₂)) with PRedex-ε e (Step x₂)
... | Step s' = S₂.Step (S₂.appFunCtx∙₁ s')
PRedex-ε (SG.Star∙ p (SG.Res .p x₁) e₁) (S₂.Step (S₂.appFunCtx∙₂ x₃)) with PRedex-ε e₁ (Step x₃)
... | Step s' = S₂.Step (S₂.appFunCtx∙₂ s')
PRedex-ε (SG.Star∙ p (SG.Resₓ .p e₁) e₂) (S₂.Step (S₂.appFunCtx∙₂ₓ x₃)) with PRedex-ε e₂ (Step x₃)
... | Step s' = S₂.Step (S₂.appFunCtx∙₂ₓ s')
PRedex-ε (SG.Star∙ p (SG.Res .p x₁) (SG.Res .p x₂)) (S₂.Step S₂.appFun∙) = Step appFun∙
PRedex-ε (SG.Star∙ p (SG.Resₓ .p e₁) (SG.Res .p x₁)) (S₂.Step S₂.appFun∙₁ₓ) = S₂.Step S₂.appFun∙₁ₓ
PRedex-ε (SG.Star∙ p (SG.Res .p x) (SG.Resₓ .p e₂)) (S₂.Step S₂.appFun∙₂ₓ) = S₂.Step S₂.appFun∙₂ₓ
PRedex-ε (SG.Star∙ p (SG.Resₓ .p e) (SG.Resₓ .p e₃)) (S₂.Step S₂.appFun∙₁₂ₓ) = S₂.Step S₂.appFun∙₁₂ₓ
PRedex-ε (SG.∙ nonS) (S₂.Step S₂.Hole) = Step Hole
PRedex-ε (SG.relabel p p₂ (SG.Iso nonS x)) (S₂.Step (S₂.relabelCtx .p x₁)) with PRedex-ε x (Step x₁)
... | Step s' = S₂.Step (S₂.relabelCtx p s')
PRedex-ε (SG.relabel p p₂ (SG.Res∙ ¬p x)) (S₂.Step (S₂.relabelCtx .p x₁)) = ⊥-elim (¬p (trans-⊑ p p₂))
PRedex-ε (SG.relabel p p₂ (SG.Iso .(SG.Resᴸ p₁) (SG.Res p₁ x))) (S₂.Step (S₂.relabel .p)) = S₂.Step (S₂.relabel p)
PRedex-ε (SG.relabel p p₂ (SG.Res∙ ¬p x)) (S₂.Step (S₂.relabel .p)) = ⊥-elim (¬p (trans-⊑ p p₂))
PRedex-ε (SG.relabel p p₂ (SG.Iso .(SG.Resᴸ p₁) (SG.Resₓ p₁ x))) (S₂.Step (S₂.relabelEx .p)) = S₂.Step (S₂.relabelEx p)
PRedex-ε (SG.relabel p p₂ (SG.Res∙ ¬p ())) (S₂.Step (S₂.relabelEx .p))
PRedex-ε (SG.relabel∙ p p₂ (SG.Iso nonS x)) (S₂.Step (S₂.relabelCtx∙ .p x₁)) with PRedex-ε x (Step x₁)
... | Step s' = S₂.Step (S₂.relabelCtx∙ p s')
PRedex-ε (SG.relabel∙ p p₂ (SG.Res∙ ¬p x)) (S₂.Step (S₂.relabelCtx∙ .p x₁)) = ⊥-elim (¬p (trans-⊑ p p₂))
PRedex-ε (SG.relabel∙ p p₂ (SG.Iso .(SG.Resᴸ p₁) (SG.Res p₁ x))) (S₂.Step (S₂.relabel∙ .p)) = Step (relabel∙ p)
PRedex-ε (SG.relabel∙ p p₂ (SG.Res∙ ¬p x)) (S₂.Step (S₂.relabel∙ .p)) = ⊥-elim (¬p (trans-⊑ p p₂))
PRedex-ε (SG.relabel∙ p p₂ (SG.Iso .(SG.Resᴸ p₁) (SG.Resₓ p₁ x))) (S₂.Step (S₂.relabelEx∙ .p)) = S₂.Step (relabelEx∙ p)
PRedex-ε (SG.relabel∙ p p₂ (SG.Res∙ ¬p x)) (S₂.Step (S₂.relabelEx∙ .p)) = ⊥-elim (¬p (trans-⊑ p p₂))

Redex-ε : ∀ {τ l lₐ ls} {t : CTerm (Mac l τ)} {Σ : Store ls} -> (p : l ⊑ lₐ) -> Redex (εˢ lₐ Σ) (ε-Mac lₐ (yes p) t) -> Redex Σ t
Redex-ε {τ} {l} {lₐ} {ls} {t} {Σ} p isR = aux (ε-Mac-yes-ErasureIso (SG.Macᴸ p) p t) (εˢ-ErasureStore Σ) isR
  where aux : ∀ {τ} {Σ Σᵉ : Store ls} {t tᵉ : CTerm (Mac l τ)} {nonS : Insensitive lₐ (Mac l τ)} ->
                ErasureIso nonS t tᵉ -> ErasureStore lₐ Σ Σᵉ -> Redex Σᵉ tᵉ -> Redex Σ t
        aux eᵗ eˢ (S₂.Step (S₂.Pure x)) with PRedex-ε eᵗ (S₂.Step x)
        ... | Step s = S₂.Step (Pure s)
        aux eᵗ eˢ (S₂.Step (S₂.BindCtx x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.CatchCtx x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.join p₁ x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.joinEx p₁ x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.join∙ p₁)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.new p₁ q)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.writeCtx p₁ x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.write p₁ q r)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.writeEx p₁ q r)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.readCtx p₁ x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.read p₁ q r)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.readEx p₁)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.fork p₁ t₂)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.newMVar p₁ q)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.putMVarCtx x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.putMVar q r)) = {!!}
        aux eᵗ eˢ (S₂.Step S₂.putMVarEx) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.takeMVarCtx x)) = {!!}
        aux eᵗ eˢ (S₂.Step (S₂.takeMVar q r)) = {!!}
        aux eᵗ eˢ (S₂.Step S₂.takeMVarEx) = {!!}
        
-- To prove this we would need to prove the following lemmas:
-- IsValue (ε t) => IsValue t
-- Redex (ε Σ) (ε t) => Redex Σ t
-- For thise we need the graph of the erasure function, therefore I am going to postulate them for the time being
ε-Stuck : ∀ {l lₐ τ ls} {t : CTerm (Mac l τ)} {Σ : Store ls} -> (p : l ⊑ lₐ) -> Stuck Σ t -> Stuck (εˢ lₐ Σ) (ε-Mac lₐ (yes p) t)
ε-Stuck {l} {lₐ} {t = t} {Σ} p (stuck nS nV) = stuck f g
  where f : Redex (εˢ lₐ Σ)  (ε-Mac lₐ (yes p) t) -> ⊥
        f s = nS (Redex-ε p s)
        
        g : IsValue (ε-Mac lₐ (yes p) t) -> ⊥
        g isV = nV (Value-ε p isV)

ε-IsFork : ∀ {lₐ τ l} {t : CTerm (Mac l τ)}(x : Dec (l ⊑ lₐ)) -> ¬ (IsFork t) -> ¬ (IsFork (ε-Mac lₐ x t))
ε-IsFork {t = t} x nF y = aux x t nF y
  where aux : ∀ {lₐ τ l} (x : Dec (l ⊑ lₐ)) (t : CTerm (Mac l τ)) -> ¬ (IsFork t) -> ¬ (IsFork (ε-Mac lₐ x t))
        aux (yes p) (Var x) nF ()
        aux (yes p) (App t t₁) nF ()
        aux (yes p) (If t Then t₁ Else t₂) nF ()
        aux (yes p) (unId t) nF ()        
        aux (yes p) (Return t) nF ()
        aux (yes p) (t >>= t₁) nF ()
        aux (yes p) (Throw t) nF ()
        aux (yes p) (Catch t t₁) nF ()
        aux (yes p) (Mac t) nF ()
        aux (yes p) (Macₓ t) nF ()
        aux (yes p) (label x t) nF ()
        aux (yes p) (label∙ x t) nF ()
        aux (yes p) (unlabel x t) nF ()
        aux (yes p) (join x t) nF ()
        aux (yes p) (join∙ x t) nF ()
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

ε-Is∙ : ∀ {lₐ τ l} {t : CTerm (Mac l τ)} -> (p : l ⊑ lₐ) -> ¬ (Is∙ t) -> ¬ (Is∙ (ε-Mac lₐ (yes p) t))
ε-Is∙ {t = Var x} p ¬∙ ()
ε-Is∙ {t = App t t₁} p ¬∙ ()
ε-Is∙ {t = If t Then t₁ Else t₂} p ¬∙ ()
ε-Is∙ {t = unId t} p ¬∙ ()
ε-Is∙ {t = Return t} p ¬∙ ()
ε-Is∙ {t = t >>= t₁} p ¬∙ ()
ε-Is∙ {t = Throw t} p ¬∙ ()
ε-Is∙ {t = Catch t t₁} p ¬∙ ()
ε-Is∙ {t = Mac t} p ¬∙ ()
ε-Is∙ {t = Macₓ t} p ¬∙ ()
ε-Is∙ {lₐ} {t = label {h = h} x t} p ¬∙ is∙ with h ⊑? lₐ
ε-Is∙ {lₐ} {._} {l} {label x t} p₁ ¬∙ () | yes p
ε-Is∙ {lₐ} {._} {l} {label x t} p ¬∙ () | no ¬p
ε-Is∙ {t = label∙ x t} p ¬∙ ()
ε-Is∙ {t = unlabel x t} p ¬∙ ()
ε-Is∙ {lₐ} {t = join {h = h} x t} p ¬∙ is∙ with h ⊑? lₐ
ε-Is∙ {lₐ} {._} {l} {join x t} p₁ ¬∙ () | yes p
ε-Is∙ {lₐ} {._} {l} {join x t} p ¬∙ () | no ¬p
ε-Is∙ {t = join∙ x t} p ¬∙ ()
ε-Is∙ {t = read x t} p ¬∙ ()
ε-Is∙ {t = write x t t₁} p ¬∙ ()
ε-Is∙ {t = new x t} p ¬∙ ()
ε-Is∙ {t = fork x t} p ¬∙ ()
ε-Is∙ {t = newMVar x} p ¬∙ ()
ε-Is∙ {t = takeMVar t} p ¬∙ ()
ε-Is∙ {t = putMVar t t₁} p ¬∙ ()
ε-Is∙ {t = ∙} p ¬∙ is∙ = ¬∙ ∙

ε-↑ : ∀ {l lₐ ls e} {p₁ p₂ : Program ls (Mac l （）)} -> (p : l ⊑ lₐ) -> p₁ ⟼ p₂ ↑ e ->
        let ⟨ Σ₁ ∥ t₁ ⟩ = p₁
            ⟨ Σ₂ ∥ t₂ ⟩ = p₂ in
        ⟨ εˢ lₐ Σ₁ ∥ ε-Mac lₐ (yes p) t₁ ⟩ ⟼ ⟨ εˢ lₐ Σ₂ ∥ ε-Mac lₐ (yes p) t₂ ⟩ ↑ (εᵉ (yes p) e)
ε-↑ p (bullet x) = bullet (ε-Mac-dist _ (yes p) x)
ε-↑ {lₐ = lₐ} p (fork {h = h} p₁ t s) = fork p₁ (ε-Mac _ (h ⊑? lₐ) t) (ε-Mac-dist lₐ (yes p) s)
ε-↑ p (none nF ¬∙ s) = none (ε-IsFork (yes p) nF) (ε-Is∙ p ¬∙) (ε-Mac-dist _ (yes p) s)

--------------------------------------------------------------------------------

ε-updateᵖ-≡ : ∀ {l lₐ n ls} {t : Thread l} {ps₁ ps₂ : Pools ls} -> ¬ (l ⊑ lₐ) -> ps₂ ← ps₁ [ l ][ n ]≔ t -> εᴾ lₐ ps₁ ≡ εᴾ lₐ ps₂
ε-updateᵖ-≡ {l} {lₐ} ¬p (Here x) with l ⊑? lₐ
ε-updateᵖ-≡ ¬p (Here x) | yes p = ⊥-elim (¬p p)
ε-updateᵖ-≡ ¬p₁ (Here x) | no ¬p = refl
ε-updateᵖ-≡ ¬p (There x) rewrite ε-updateᵖ-≡ ¬p x = refl

--------------------------------------------------------------------------------

ε-read∙  : ∀ {l lₐ ls n} {ps : Pools ls} {t : Thread l} -> ¬ ( l ⊑ lₐ) -> ps [ l ][ n ]= t -> εᴾ lₐ ps [ l ][ n ]= ∙
ε-read∙ {l} {lₐ} {ps = x ◅ ps} ¬p (Here a) with l ⊑? lₐ
ε-read∙ {l} {lₐ} {._} {n'} {x ◅ ps} ¬p (Here a) | yes p = ⊥-elim (¬p p)
ε-read∙ {l} {lₐ} {._} {n'} {x ◅ ps} ¬p₁ (Here a) | no ¬p = Here ∙
ε-read∙ {ps = x ◅ ps} ¬p (There q) = There (ε-read∙ ¬p q)

ε-read : ∀ {l lₐ n' n} {t : Thread l} {ts : Pool l n'} -> (x : Dec (l ⊑ lₐ)) -> LookupThread t n ts -> LookupThread (ε-Mac lₐ x t) n (εᵗ x ts)
ε-read (yes p) ∙ = ∙
ε-read (yes p) Here = Here
ε-read (yes p) (There a) = There (ε-read (yes p) a)
ε-read {t = t} (no ¬p) a with ε-Mac-CTerm≡∙ _ t ¬p
... | eq rewrite eq = ∙

ε-readᵖ : ∀ {l lₐ n ls} {ps : Pools ls} {t : Thread l} -> (x : Dec (l ⊑ lₐ)) -> ps [ l ][ n ]= t -> (εᴾ lₐ ps) [ l ][ n ]= (ε-Mac _ x t)
ε-readᵖ {l} {lₐ} {t = t} x (Here {p = ts} y) with ε-Mac-extensional x (l ⊑? lₐ) t
... | eq rewrite eq = Here (ε-read (l ⊑? lₐ) y)
ε-readᵖ x (There y) = There (ε-readᵖ x y)

ε-readᵗ : ∀ {l lₐ ls n} {ps : Pools ls} {ts : Pool l n} -> (x : Dec (l ⊑ lₐ)) -> ps [ l ]= ts ->  (εᴾ lₐ ps) [ l ]= εᵗ x ts
ε-readᵗ {l} {lₐ} {ts = ts} x Here rewrite εᵗ-extensional x (l ⊑? lₐ) ts = Here
ε-readᵗ x (There y) = There (ε-readᵗ x y)

--------------------------------------------------------------------------------

ε-update : ∀ {l lₐ n' n} {ts₁ ts₂ : Pool l n'} {t : Thread l} -> (p : l ⊑ lₐ) ->
               UpdateThread t n ts₁ ts₂ -> 
               UpdateThread (ε-Mac lₐ (yes p) t) n (εᵗ (yes p) ts₁) (εᵗ (yes p) ts₂)
ε-update p ∙ = ∙
ε-update p upd = upd
ε-update p (skip a) = skip (ε-update p a)

ε-updateᵖ : ∀ {l lₐ n ls} {ps₁ ps₂ : Pools ls} {t : Thread l} -> (p : l ⊑ lₐ) ->
             ps₂ ← ps₁ [ l ][ n ]≔ t  ->
             (εᴾ lₐ ps₂) ← (εᴾ lₐ ps₁) [ l ][ n ]≔ (ε-Mac _ (yes p) t)
ε-updateᵖ {l} {lₐ} {t = t} p (Here {p₁ = ts₁} {p₂ = ts₂} x)
  rewrite εᵗ-extensional (l ⊑? lₐ) (yes p) ts₁ | εᵗ-extensional (l ⊑? lₐ) (yes p) ts₂ = Here (ε-update p x)
ε-updateᵖ p (There a) = There (ε-updateᵖ p a)

▻-≡ : ∀ {l lₐ n} (ts : Pool l n) (t : Thread l)  (x : Dec (l ⊑ lₐ)) -> (εᵗ x ts ▻ ε-Mac _ x t) ≡ εᵗ (l ⊑? lₐ) (ts ▻ t)
▻-≡ {l} {lₐ} ts t (yes p) with εᵗ-extensional (l ⊑? lₐ) (yes p) (ts ▻ t)
... | eq rewrite eq = sym (ε-▻-≡ p t ts)
▻-≡ {l} {lₐ} ts t (no ¬p) with l ⊑? lₐ
▻-≡ ts t (no ¬p) | yes p = ⊥-elim (¬p p)
▻-≡ ts t (no ¬p₁) | no ¬p = refl

ε-update-▻ : ∀ {l lₐ ls n} {ps₁ ps₂ : Pools ls} {ts : Pool l n} {t : Thread l} -> (x : Dec (l ⊑ lₐ)) ->
               ps₂ ← ps₁ [ l ]≔ (ts ▻ t) ->
               εᴾ lₐ ps₂ ← εᴾ lₐ ps₁ [ l ]≔ ((εᵗ x ts) ▻ (ε-Mac _ x t))
ε-update-▻ {l} {lₐ} {ts = ts} {t = t} x Here with ▻-≡ ts t x
... | eq rewrite eq = Here
ε-update-▻ x (There y) = There (ε-update-▻ x y)

ε-updateᵗ-≡ : ∀ {l lₐ ls n} {ps₁ ps₂ : Pools ls} {ts : Pool l n} -> ¬ (l ⊑ lₐ) ->
            ps₂ ← ps₁ [ l ]≔ ts -> εᴾ lₐ ps₁ ≡ εᴾ lₐ ps₂
ε-updateᵗ-≡ {l} {lₐ} ¬p Here with l ⊑? lₐ
ε-updateᵗ-≡ ¬p Here | yes p = ⊥-elim (¬p p)
ε-updateᵗ-≡ ¬p₁ Here | no ¬p = refl
ε-updateᵗ-≡ ¬p (There x) rewrite ε-updateᵗ-≡ ¬p x = refl

--------------------------------------------------------------------------------

ε-fork? : ∀ {h lₐ l n} -> (p : l ⊑ h) (x : Dec (h ⊑ lₐ)) -> (t : Thread h) -> εᴱ lₐ (fork? p t n)  ≡ fork? p (ε-Mac lₐ x t) n
ε-fork? l⊑h (yes p) t with is∙? t
ε-fork? l⊑h (yes p₁) .∙ | yes ∙ = refl
ε-fork? {h} {lₐ} l⊑h (yes p) t | no ¬p with h ⊑? lₐ
ε-fork? l⊑h (yes p₁) (Var x) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (App t t₁) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (If t Then t₁ Else t₂) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (unId t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (Return t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (t >>= t₁) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (Throw t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (Catch t t₁) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (Mac t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (Macₓ t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (unlabel x t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (read x t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (write x t t₁) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (fork x t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (takeMVar t) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) (putMVar t t₁) | no ¬p | yes p = refl
ε-fork? l⊑h (yes p₁) ∙ | no ¬p | yes p = ⊥-elim (¬p ∙)
ε-fork? l⊑h (yes p) t | no ¬p₁ | no ¬p = ⊥-elim (¬p p)
ε-fork? l⊑h (no ¬p) t with ε-Mac-CTerm≡∙ _ t ¬p
... | eq rewrite eq with is∙? t
ε-fork? l⊑h (no ¬p) t | refl | yes p = refl
ε-fork? {h} {lₐ} l⊑h (no ¬p₁) t | refl | no ¬p with h ⊑? lₐ
... | yes p' = ⊥-elim (¬p₁ p')
... | no ¬p' = refl

-- Distributivity
εᵍ-dist : ∀ {l n ls} {g₁ g₂ : Global ls} -> (lₐ : Label) -> l , n ⊢ g₁ ↪ g₂ -> l , n ⊢ (εᵍ lₐ g₁) ↪ (εᵍ lₐ g₂)

εᵍ-dist {l} lₐ (step r st sc w)  with l ⊑? lₐ
εᵍ-dist lₐ (step r st sc w) | yes p = step (ε-readᵖ (yes p) r) ((ε-↑ p st)) (ε-sch-dist 𝓢 (yes p) sc ) (ε-updateᵖ p w)
εᵍ-dist lₐ (step r st sc w) | no ¬p
  with ε-read∙ ¬p r | (ε-sch-dist 𝓢 (no ¬p) sc) |  εˢ-≡ lₐ ¬p (stepOf st) | ε-updateᵖ-≡ ¬p w | ε-sch-≡ 𝓢 ¬p sc
... | x | sc' | eq₁ | eq₂ | eq₃ rewrite eq₁ | eq₂ | eq₃ = hole x (bullet (Pure Hole)) sc'

εᵍ-dist {l} lₐ (fork r₁ r₂ st sc w₁ w₂) with l ⊑? lₐ
εᵍ-dist {l} lₐ (fork {h = h} {nʰ = nʰ} {tʰ = tʰ} {l⊑h = l⊑h} r₁ r₂ st sc w₁ w₂) | yes p with ε-sch-dist 𝓢 (yes p) sc
... | sc' rewrite ε-fork? {n = nʰ} l⊑h (h ⊑? lₐ) tʰ
  = fork (ε-readᵖ (yes p) r₁) (ε-readᵗ (h ⊑? lₐ) r₂) (ε-↑ p st) sc' (ε-update-▻ (h ⊑? lₐ) w₁) (ε-updateᵖ p w₂)
εᵍ-dist lₐ (fork r₁ r₂ st sc w₁ w₂) | no ¬p
  with ε-read∙ ¬p r₁ | (ε-sch-dist 𝓢 (no ¬p) sc) |  εˢ-≡ lₐ ¬p (stepOf st)
       | ε-updateᵗ-≡ (trans-⋢ (fork-⊑ st) ¬p) w₁ | ε-updateᵖ-≡ ¬p w₂ | ε-sch-≡ 𝓢 ¬p sc
... | x | sc' | eq₁ | eq₂ | eq₃ | eq₄ rewrite eq₁ | eq₂ | eq₃ | eq₄ = hole x (bullet (Pure Hole)) sc'

εᵍ-dist {l} lₐ (hole r (bullet (Pure Hole)) sc) with l ⊑? lₐ
... | yes p = hole (ε-readᵖ (yes p) r) (bullet (Pure Hole)) (ε-sch-dist 𝓢 (yes p) sc)
... | no ¬p = hole (ε-readᵖ (no ¬p) r) (bullet (Pure Hole)) (ε-sch-dist 𝓢 (no ¬p) sc)

εᵍ-dist {l} lₐ (skip r st sc) with l ⊑? lₐ
... | yes p = skip (ε-readᵖ (yes p) r) (ε-Stuck p st) (ε-sch-dist 𝓢 (yes p) sc)
... | no ¬p with ε-sch-dist 𝓢 (no ¬p) sc
... | sc' rewrite ε-sch-≡ 𝓢 ¬p sc = hole (ε-read∙ ¬p r) (bullet (Pure Hole)) sc'

εᵍ-dist {l} lₐ (exit r isV sc) with l ⊑? lₐ
... | yes p = exit (ε-readᵖ (yes p) r) (ε-IsValue p isV) (ε-sch-dist 𝓢 (yes p) sc)
... | no ¬p  with ε-sch-dist 𝓢 (no ¬p) sc
... | sc' rewrite ε-sch-≡ 𝓢 ¬p sc = hole (ε-read∙ ¬p r) (bullet (Pure Hole)) sc'
