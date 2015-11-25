module Conversion.Proofs where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_ ; _⇝_ to _⇝ᵗ_)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_ ;  _⇝_ to _⇝ᵘ_)
open import Untyped.Proofs
open import Conversion.Base public

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl) 

--------------------------------------------------------------------------------
-- Soundness results
--------------------------------------------------------------------------------

-- Soundness for typed terms

-- A typed term preserves its type when converted.
sound-⌞_⌟ : ∀ {τ Δ} -> (t : Termᵗ Δ τ) -> Δ ⊢ ⌞ t ⌟ ∷ τ
sound-⌞ （） ⌟ = （）
sound-⌞ True ⌟ = True
sound-⌞ False ⌟ = False
sound-⌞ Var x ⌟ = Var x
sound-⌞ Abs t ⌟ = Abs (sound-⌞ t ⌟)
sound-⌞ App t t₁ ⌟ = App (sound-⌞ t ⌟) (sound-⌞ t₁ ⌟)
sound-⌞ If t Then t₁ Else t₂ ⌟ = If sound-⌞ t ⌟ Then sound-⌞ t₁ ⌟ Else sound-⌞ t₂ ⌟
sound-⌞ Return t ⌟ = Return (sound-⌞ t ⌟)
sound-⌞ t >>= t₁ ⌟ = sound-⌞ t ⌟ >>= sound-⌞ t₁ ⌟
sound-⌞ ξ ⌟ = ξ
sound-⌞ Throw t ⌟ = Throw (sound-⌞ t ⌟)
sound-⌞ Catch t t₁ ⌟ = Catch (sound-⌞ t ⌟) (sound-⌞ t₁ ⌟)
sound-⌞ Mac t ⌟ = Mac (sound-⌞ t ⌟)
sound-⌞ Macₓ t ⌟ = Macₓ (sound-⌞ t ⌟)
sound-⌞ Res t ⌟ = Res (sound-⌞ t ⌟)
sound-⌞ Resₓ t ⌟ = Resₓ (sound-⌞ t ⌟)
sound-⌞ label x t ⌟ = label x (sound-⌞ t ⌟)
sound-⌞ unlabel x t ⌟ = unlabel x (sound-⌞ t ⌟)
sound-⌞ join x t ⌟ = join x (sound-⌞ t ⌟)
sound-⌞ ∙ ⌟ = ∙

-- Soundness
-- A typed closed term preserves its type when converted
sound-⟦_⟧  : ∀ {τ} -> (c : CTermᵗ τ) -> ⟦ c ⟧ :: τ
sound-map⟦_⟧ : ∀ {Δ} -> (Γ : Envᵗ Δ) -> TEnv Δ map⟦ Γ ⟧

sound-⟦ Γ , t ⟧ = sound-map⟦ Γ ⟧ , sound-⌞ t ⌟
sound-⟦ f $ x ⟧ = sound-⟦ f ⟧ $ sound-⟦ x ⟧
sound-⟦ (If c Then t Else e) ⟧ = If sound-⟦ c ⟧ Then sound-⟦ t ⟧ Else sound-⟦ e ⟧
sound-⟦ m >>= k ⟧ = (sound-⟦_⟧ m) >>= (sound-⟦ k ⟧)
sound-⟦ Catch m h ⟧ = Catch (sound-⟦_⟧ m) (sound-⟦ h ⟧)
sound-⟦ unlabel x c ⟧ = unlabel x (sound-⟦ c ⟧)
sound-⟦ join x c ⟧ = join x (sound-⟦ c ⟧)
sound-⟦ ∙ ⟧ = ∙

sound-map⟦ [] ⟧ = []
sound-map⟦ x ∷ Γ ⟧ = sound-⟦ x ⟧ ∷ sound-map⟦ Γ ⟧

--------------------------------------------------------------------------------

-- The soundness proofs for the untyped terms are implicit in the
-- conversion functionsm because their signatures
-- already guarantees that they produce typed terms (CTermᵗ, Envᵗ and Termᵗ)
-- of the right type.

--------------------------------------------------------------------------------
-- Completeness results
--------------------------------------------------------------------------------

-- Completeness for typed terms

-- ⌜_⌝ ∘ ⌞_⌟ ≡ id
complete-⌞_⌟ : ∀ {Δ τ} -> (t : Termᵗ Δ τ) ->
               let p = sound-⌞ t ⌟ in ⌜ ⌞ t ⌟ ⌝ ≡ t
complete-⌞ （） ⌟ = refl
complete-⌞ True ⌟ = refl
complete-⌞ False ⌟ = refl
complete-⌞ Var x ⌟ = refl
complete-⌞ Abs t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ App f x ⌟ rewrite complete-⌞ f ⌟ | complete-⌞ x ⌟ = refl
complete-⌞ If c Then t Else e ⌟ rewrite complete-⌞ c ⌟ | complete-⌞ t ⌟ | complete-⌞ e ⌟ = refl
complete-⌞ Return t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ m >>= k ⌟ rewrite complete-⌞ m ⌟ | complete-⌞ k ⌟ = refl
complete-⌞ ξ ⌟ = refl
complete-⌞ Throw t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ Catch m k ⌟ rewrite complete-⌞ m ⌟ | complete-⌞ k ⌟ = refl
complete-⌞ Mac t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ Macₓ t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ Res t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ Resₓ t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ label x t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ unlabel x t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ join x t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ ∙ ⌟ = refl

-- Closed terms
-- ⟪_⟫ ∘ ⟦_⟧ ≡ id
complete-⟦_⟧  : ∀ {τ} -> (c : CTermᵗ τ) ->
                let p = sound-⟦ c ⟧ in ⟪ ⟦ c ⟧ ⟫ ≡ c

-- Completness for enviroments
complete-map⟦_⟧ : ∀ {Δ} -> (Γ : Envᵗ Δ) ->
                  let p = sound-map⟦ Γ ⟧ in map⟪ map⟦ Γ ⟧ ⟫ ≡ Γ

complete-⟦ Γ , t ⟧ rewrite complete-map⟦ Γ ⟧ | complete-⌞ t ⌟ = refl
complete-⟦ f $ x ⟧ rewrite complete-⟦ f ⟧ | complete-⟦ x ⟧ = refl
complete-⟦ If c Then t Else e ⟧ rewrite complete-⟦ c ⟧ | complete-⟦ t ⟧ | complete-⟦ e ⟧ = refl
complete-⟦ m >>= k ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ k ⟧ = refl
complete-⟦ Catch m h ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ h ⟧ = refl
complete-⟦ unlabel x c ⟧ rewrite complete-⟦ c ⟧ = refl
complete-⟦ join x c ⟧ rewrite complete-⟦ c ⟧ = refl
complete-⟦ ∙ ⟧ = refl

complete-map⟦ [] ⟧ = refl
complete-map⟦ x ∷ Γ ⟧ rewrite complete-⟦ x ⟧ | complete-map⟦ Γ ⟧ = refl

--------------------------------------------------------------------------------

-- Completness for untyped terms
-- Unfortunately not always the instance arguments are resolved in the
-- signatures so I need to pass them explicitly.
-- I provided the uncluttered version in a comment

-- ⌞ ⌜ t ⌝ ⌟ ≡ t
-- ⌞_⌟ ∘ ⌜_⌝ ≡ id
complete-⌜_⌝ : ∀ {Δ τ} {t : Termᵘ (length Δ)} -> (p : Δ ⊢ t ∷ τ) -> ⌞ ⌜_⌝ t {{p}} ⌟ ≡ t
complete-⌜ （） ⌝ = refl
complete-⌜ True ⌝ = refl
complete-⌜ False ⌝ = refl
complete-⌜ App f x ⌝ rewrite complete-⌜ f ⌝ | complete-⌜ x ⌝ = refl
complete-⌜ Abs t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ Var p ⌝ = refl
complete-⌜ If c Then t Else e ⌝ rewrite complete-⌜ c ⌝ | complete-⌜ t ⌝ | complete-⌜ e ⌝ = refl
complete-⌜ Return t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ m >>= k ⌝ rewrite complete-⌜ m ⌝ | complete-⌜ k ⌝ = refl
complete-⌜ ξ ⌝ = refl
complete-⌜ Throw t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ Catch m h ⌝ rewrite complete-⌜ m ⌝ | complete-⌜ h ⌝ = refl
complete-⌜ Mac t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ Macₓ t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ label p t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ unlabel x t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ join x t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ Res t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ Resₓ t ⌝ rewrite complete-⌜ t ⌝ = refl
complete-⌜ ∙ ⌝ = refl

-- ⟦ ⟪ c ⟫ ⟧ ≡ c
-- ⟦_⟧ ∘ ⟪⟫ ≡ id
complete-⟪_⟫ : ∀ {c τ} (p : c :: τ) -> ⟦ ⟪_⟫ c {{p}} ⟧ ≡ c

-- map⟦ map⟪ c ⟫ ⟧ ≡ c
complete-map⟪_⟫ : ∀ {Δ} {Γ : Envᵘ (length Δ)} -> (Γᵗ : TEnv Δ Γ) -> map⟦ map⟪_⟫ Γ {{Γᵗ}} ⟧ ≡ Γ

complete-map⟪ [] ⟫ = refl
complete-map⟪ c ∷ Γ ⟫ rewrite complete-⟪ c ⟫ | complete-map⟪ Γ ⟫ = refl

complete-⟪ Γ , t ⟫ rewrite complete-map⟪ Γ ⟫ | complete-⌜ t ⌝ = refl
complete-⟪ f $ x ⟫ rewrite complete-⟪ f ⟫ | complete-⟪ x ⟫ = refl
complete-⟪ If c Then t Else e ⟫ rewrite complete-⟪ c ⟫ | complete-⟪ t ⟫ | complete-⟪ e ⟫ = refl
complete-⟪ m >>= k ⟫ rewrite complete-⟪ m ⟫ | complete-⟪ k ⟫ = refl
complete-⟪ Catch m h ⟫ rewrite complete-⟪ m ⟫ | complete-⟪ h ⟫ = refl
complete-⟪ unlabel x c ⟫ rewrite complete-⟪ c ⟫ = refl
complete-⟪ join x c ⟫ rewrite complete-⟪ c ⟫ = refl
complete-⟪ ∙ ⟫ = refl

--------------------------------------------------------------------------------
-- Equivalence between small step semantics
--------------------------------------------------------------------------------

lookup⟪_,_⟫ : ∀ {Δ τ} {Γ : Envᵘ (length Δ)} (Γᵗ : TEnv Δ Γ) (x : τ ∈ Δ) ->
              let p = lookup-fin x Γᵗ in ⟪ lookup (fin x) Γ ⟫ ≡ x !! map⟪ Γ ⟫
lookup⟪ x ∷ Γᵗ , Here ⟫ = refl
lookup⟪ x ∷ Γᵗ , There p ⟫ rewrite lookup⟪ Γᵗ , p ⟫ = refl

stepPureᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⇝ᵘ c₂) ->
             let p₂ = preservation⇝ p₁ s in (⟪_⟫ c₁ {{p₁}}) ⇝ᵗ (⟪_⟫ c₂ {{p₂}})
stepPureᵘᵗ (p $ p₁) (AppL s) = AppL (stepPureᵘᵗ p s)
stepPureᵘᵗ (Γ , Abs t $ p₁) Beta = Beta
stepPureᵘᵗ (Γ , Var p) Lookup rewrite lookup⟪ Γ , p ⟫ = Lookup
stepPureᵘᵗ (Γ , App t t₃) Dist-$ = Dist-$
stepPureᵘᵗ (Γ , (If t₃ Then t₄ Else t₅)) Dist-If = Dist-If
stepPureᵘᵗ (If p Then p₁ Else p₂) (IfCond s) = IfCond (stepPureᵘᵗ p s)
stepPureᵘᵗ (If Γ , True Then p₁ Else p₂) IfTrue = IfTrue
stepPureᵘᵗ (If Γ , False Then p₁ Else p₂) IfFalse = IfFalse
stepPureᵘᵗ (Γ , ∙) Dist-∙ = Dist-∙
stepPureᵘᵗ ∙ Hole = Hole

-- If c₁ ⟼ᵘ c₂ and c₁ is well-typed then we can produce an equivalent typed small step between
stepᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⟼ᵘ c₂) ->
         let p₂ = preservation p₁ s in (⟪_⟫ c₁ {{p₁}}) ⟼ᵗ (⟪_⟫ c₂ {{p₂}})
stepᵘᵗ p (Pure x) = Pure (stepPureᵘᵗ p x)
stepᵘᵗ (Γ , Return t₁) Return = Return
stepᵘᵗ (Γ , t >>= t₁) Dist->>= = Dist->>=
stepᵘᵗ (p >>= p₁) (BindCtx s) = BindCtx (stepᵘᵗ p s)
stepᵘᵗ ((Γ , Mac t₁) >>= p₁) Bind = Bind
stepᵘᵗ ((Γ , Macₓ t₁) >>= p₁) BindEx = BindEx
stepᵘᵗ (Γ , Throw t) Throw = Throw
stepᵘᵗ (Γ , Catch t₁ t₂) Dist-Catch = Dist-Catch
stepᵘᵗ (Catch p p₁) (CatchCtx s) = CatchCtx (stepᵘᵗ p s)
stepᵘᵗ (Catch (Γ , Mac t₁) p₁) Catch = Catch
stepᵘᵗ (Catch (Γ , Macₓ t₁) p₁) CatchEx = CatchEx
stepᵘᵗ (Γ , label p t₁) (label .p) = label p
stepᵘᵗ (Γ , unlabel x t₁) Dist-unlabel = Dist-unlabel x
stepᵘᵗ (Γ , join x t) (Dist-join .x) = Dist-join x
stepᵘᵗ (unlabel x (Γ , Res t)) unlabel = unlabel x
stepᵘᵗ (unlabel x (Γ , Resₓ t)) unlabelEx = unlabelEx x
stepᵘᵗ (unlabel x c) (unlabelCtx s) = unlabelCtx x (stepᵘᵗ c s)
stepᵘᵗ (join x c) (joinCtx .x s) = joinCtx x (stepᵘᵗ c s)
stepᵘᵗ (join x (Γ , Mac t)) (join .x) = join x
stepᵘᵗ (join x (Γ , Macₓ t)) (joinEx .x) = joinEx x

-- stepMacᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⟼ᵘ c₂) ->
--          let p₂ = preservation⇝ p₁ (Mac s) in ⟪ c₁ ⟫ ⇝ᵗ ⟪ c₂ ⟫


-- Just a better looking entry point for stepᵘᵗ, where the proof that c₁ is well-typed
-- is passed as an instance argument
step⟪_⟫ : ∀ {τ} {c₁ c₂ : CTermᵘ} {{p : c₁ :: τ}} -> (s : c₁ ⟼ᵘ c₂) ->
                let arg = preservation p s in ⟪ c₁ ⟫ ⟼ᵗ ⟪ c₂ ⟫
step⟪_⟫ {{p}} s = stepᵘᵗ p s

lookup⟦_⟧ : ∀ {Δ τ} {{Γ : Envᵗ Δ}} -> (p : τ ∈ Δ) -> ⟦ p !! Γ ⟧ ≡ lookup (fin p) map⟦ Γ ⟧
lookup⟦_⟧ {{Γ = []}} ()
lookup⟦_⟧ {{Γ = x ∷ Γ}} Here = refl
lookup⟦_⟧ {{Γ = x ∷ Γ}} (There p) rewrite lookup⟦ p ⟧ = refl

--------------------------------------------------------------------------------

stepPure⟦_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> c₁ ⇝ᵗ c₂ -> ⟦ c₁ ⟧ ⇝ᵘ ⟦ c₂ ⟧
stepPure⟦ AppL s ⟧ = AppL stepPure⟦ s ⟧
stepPure⟦ Beta ⟧ = Beta
stepPure⟦_⟧ {c₁ = Γ , Var p} Lookup rewrite lookup⟦ p ⟧ = Lookup
stepPure⟦ Dist-$ ⟧ = Dist-$
stepPure⟦ Dist-If ⟧ = Dist-If
stepPure⟦ IfCond s ⟧ = IfCond stepPure⟦ s ⟧
stepPure⟦ IfTrue ⟧ = IfTrue
stepPure⟦ IfFalse ⟧ = IfFalse
stepPure⟦ Dist-∙ ⟧ = Dist-∙
stepPure⟦ Hole ⟧ = Hole

-- It is possible instead to safely remove types from the typed small step semantics
-- and retrieve the untyped semantics
step⟦_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> c₁ ⟼ᵗ c₂ -> ⟦ c₁ ⟧ ⟼ᵘ ⟦ c₂ ⟧
step⟦ Pure s ⟧ = Pure stepPure⟦ s ⟧
step⟦ Return ⟧ = Return
step⟦ Dist->>= ⟧ = Dist->>=
step⟦ BindCtx s ⟧ = BindCtx step⟦ s ⟧
step⟦ Bind ⟧ = Bind
step⟦ BindEx ⟧ = BindEx
step⟦ Throw ⟧ = Throw
step⟦ Dist-Catch ⟧ = Dist-Catch
step⟦ CatchCtx s ⟧ = CatchCtx step⟦ s ⟧
step⟦ Catch ⟧ = Catch
step⟦ CatchEx ⟧ = CatchEx
step⟦ label p ⟧ = label p
step⟦ Dist-unlabel p ⟧ = Dist-unlabel
step⟦ unlabel p ⟧ = unlabel
step⟦ unlabelEx p ⟧ = unlabelEx
step⟦ Dist-join p ⟧ = Dist-join p
step⟦ join x ⟧ = join x
step⟦ joinEx x ⟧ = joinEx x
step⟦ joinCtx x s ⟧ = joinCtx x step⟦ s ⟧
step⟦ unlabelCtx p s ⟧ = unlabelCtx step⟦ s ⟧

-- Completness for small-step semantics transformations.
-- Converting a typed step to untyped and back to typed does not change the semantics, i.e. 
-- we get the same step.
uniquePureStepᵘ : ∀ {c₁ c₂} -> (s₁ : c₁ ⇝ᵘ c₂) (s₂ : c₁ ⇝ᵘ c₂) -> s₁ ≡ s₂
uniquePureStepᵘ (AppL p) (AppL q) rewrite uniquePureStepᵘ p q = refl
uniquePureStepᵘ Beta Beta = refl
uniquePureStepᵘ Lookup Lookup = refl
uniquePureStepᵘ Dist-$ Dist-$ = refl
uniquePureStepᵘ Dist-If Dist-If = refl
uniquePureStepᵘ (IfCond p) (IfCond q) rewrite uniquePureStepᵘ p q = refl
uniquePureStepᵘ IfTrue IfTrue = refl
uniquePureStepᵘ IfFalse IfFalse = refl
uniquePureStepᵘ Dist-∙ Dist-∙ = refl
uniquePureStepᵘ Hole Hole = refl

uniqueMixedStepᵘ : ∀ {c₁ c₂} -> (s₁ : c₁ ⇝ᵘ c₂) (s₂ : c₁ ⟼ᵘ c₂) -> Pure s₁ ≡ s₂
uniqueMixedStepᵘ s₁ (Pure s₂) = cong Pure (uniquePureStepᵘ s₁ s₂)
uniqueMixedStepᵘ () Return
uniqueMixedStepᵘ () Dist->>=
uniqueMixedStepᵘ () (BindCtx s₂)
uniqueMixedStepᵘ () Bind
uniqueMixedStepᵘ () BindEx
uniqueMixedStepᵘ () Throw
uniqueMixedStepᵘ () Dist-Catch
uniqueMixedStepᵘ () (CatchCtx s₂)
uniqueMixedStepᵘ () Catch
uniqueMixedStepᵘ () CatchEx
uniqueMixedStepᵘ () (label p)
uniqueMixedStepᵘ () Dist-unlabel
uniqueMixedStepᵘ () unlabel
uniqueMixedStepᵘ () unlabelEx
uniqueMixedStepᵘ () (unlabelCtx s₂)
uniqueMixedStepᵘ () (Dist-join p)
uniqueMixedStepᵘ () (joinCtx p s₂)
uniqueMixedStepᵘ () (join p)
uniqueMixedStepᵘ () (joinEx p)

-- Lemma
-- Each type of small step as at most one inhabitant.
uniqueStepᵘ : ∀ {c₁ c₂} -> (p q : c₁ ⟼ᵘ c₂) -> p ≡ q
uniqueStepᵘ (Pure s₁) s₂ = uniqueMixedStepᵘ s₁ s₂
uniqueStepᵘ s₁ (Pure s₂) = sym (uniqueMixedStepᵘ s₂ s₁)
uniqueStepᵘ Return Return = refl
uniqueStepᵘ Dist->>= Dist->>= = refl
uniqueStepᵘ (BindCtx p) (BindCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ Bind Bind = refl
uniqueStepᵘ BindEx BindEx = refl
uniqueStepᵘ Throw Throw = refl
uniqueStepᵘ Dist-Catch Dist-Catch = refl
uniqueStepᵘ (CatchCtx p) (CatchCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ Catch Catch = refl
uniqueStepᵘ CatchEx CatchEx = refl
uniqueStepᵘ (label p) (label .p) = refl
uniqueStepᵘ Dist-unlabel Dist-unlabel = refl
uniqueStepᵘ unlabel unlabel = refl
uniqueStepᵘ (unlabelCtx p) (unlabelCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ unlabelEx unlabelEx = refl
uniqueStepᵘ (Dist-join x) (Dist-join .x) = refl
uniqueStepᵘ (joinCtx x s₁) (joinCtx .x s₂) rewrite uniqueStepᵘ s₁ s₂ = refl
uniqueStepᵘ (join x) (join .x) = refl 
uniqueStepᵘ (joinEx x) (joinEx .x) = refl

complete-step⟪_,_⟫ : ∀ {c₁ c₂ τ} {{p : c₁ :: τ}} {{q : c₂ :: τ}} ->
                              (s₁ : c₁ ⟼ᵘ c₂) (s₂ : ⟦ ⟪_⟫ c₁ {{p}} ⟧ ⟼ᵘ ⟦ ⟪_⟫ c₂ {{q}} ⟧) -> s₁ ≅ s₂
complete-step⟪_,_⟫ {{p}} {{q}} s₁ s₂ rewrite complete-⟪ p ⟫ | complete-⟪ q ⟫ | uniqueStepᵘ s₁ s₂ = refl

--------------------------------------------------------------------------------

uniquePureStepᵗ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (s₁ : c₁ ⇝ᵗ c₂) (s₂ : c₁ ⇝ᵗ c₂) -> s₁ ≡ s₂
uniquePureStepᵗ (AppL p) (AppL q) rewrite uniquePureStepᵗ p q = refl
uniquePureStepᵗ Beta Beta = refl
uniquePureStepᵗ Lookup Lookup = refl
uniquePureStepᵗ Dist-$ Dist-$ = refl
uniquePureStepᵗ Dist-If Dist-If = refl
uniquePureStepᵗ (IfCond p) (IfCond q) rewrite uniquePureStepᵗ p q = refl
uniquePureStepᵗ IfTrue IfTrue = refl
uniquePureStepᵗ IfFalse IfFalse = refl
uniquePureStepᵗ Dist-∙ Dist-∙ = refl
uniquePureStepᵗ Hole Hole = refl

uniqueMixedStepᵗ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (s₁ : c₁ ⇝ᵗ c₂) (s₂ : c₁ ⟼ᵗ c₂) -> Pure s₁ ≡ s₂
uniqueMixedStepᵗ s₁ (Pure s₂) = cong Pure (uniquePureStepᵗ s₁ s₂)
uniqueMixedStepᵗ () Return
uniqueMixedStepᵗ () Dist->>=
uniqueMixedStepᵗ () (BindCtx s₂)
uniqueMixedStepᵗ () Bind
uniqueMixedStepᵗ () BindEx
uniqueMixedStepᵗ () Throw
uniqueMixedStepᵗ () Dist-Catch
uniqueMixedStepᵗ () (CatchCtx s₂)
uniqueMixedStepᵗ () Catch
uniqueMixedStepᵗ () CatchEx
uniqueMixedStepᵗ () (label p)
uniqueMixedStepᵗ () (Dist-unlabel p)
uniqueMixedStepᵗ () (unlabel p)
uniqueMixedStepᵗ () (unlabelEx p)
uniqueMixedStepᵗ () (unlabelCtx p s₂)
uniqueMixedStepᵗ () (Dist-join p)
uniqueMixedStepᵗ () (joinCtx p s₂)
uniqueMixedStepᵗ () (join p)
uniqueMixedStepᵗ () (joinEx p)

-- Lemma
-- Each type of small step as at most one inhabitant.
uniqueStepᵗ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (p q : c₁ ⟼ᵗ c₂) -> p ≡ q
uniqueStepᵗ (Pure s₁) s₂ = uniqueMixedStepᵗ s₁ s₂
uniqueStepᵗ s₁ (Pure s₂) = sym (uniqueMixedStepᵗ s₂ s₁)
uniqueStepᵗ Return Return = refl
uniqueStepᵗ Dist->>= Dist->>= = refl
uniqueStepᵗ (BindCtx p) (BindCtx q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ Bind Bind = refl
uniqueStepᵗ BindEx BindEx = refl
uniqueStepᵗ Throw Throw = refl
uniqueStepᵗ Dist-Catch Dist-Catch = refl
uniqueStepᵗ (CatchCtx p) (CatchCtx q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ Catch Catch = refl
uniqueStepᵗ CatchEx CatchEx = refl
uniqueStepᵗ (label p) (label .p) = refl
uniqueStepᵗ (Dist-unlabel p) (Dist-unlabel .p) = refl
uniqueStepᵗ (unlabel p) (unlabel .p) = refl
uniqueStepᵗ (unlabelCtx x p) (unlabelCtx .x q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ (unlabelEx p) (unlabelEx .p) = refl
uniqueStepᵗ (Dist-join x) (Dist-join .x) = refl
uniqueStepᵗ (joinCtx x s₁) (joinCtx .x s₂) rewrite uniqueStepᵗ s₁ s₂ = refl
uniqueStepᵗ (join x) (join .x) = refl 
uniqueStepᵗ (joinEx x) (joinEx .x) = refl

complete-step⟦_,_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (s₁ : c₁ ⟼ᵗ c₂) ->
                     let p₁ = sound-⟦ c₁ ⟧
                         p₂ = sound-⟦ c₂ ⟧ in (s₂ : ⟪ ⟦ c₁ ⟧ ⟫ ⟼ᵗ ⟪ ⟦ c₂ ⟧ ⟫) -> s₁ ≅ s₂
complete-step⟦_,_⟧ {_} {c₁} {c₂} s₁ s₂ rewrite complete-⟦ c₁ ⟧ | complete-⟦ c₂ ⟧ | uniqueStepᵗ s₁ s₂ = refl
