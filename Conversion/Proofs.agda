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

-- If c₁ ⟼ᵘ c₂ and c₁ is well-typed then we can produce an equivalent typed small step between
stepᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⇝ᵘ c₂) ->
         let p₂ = preservation⇝ p₁ s in ⟪ c₁ ⟫ ⇝ᵗ ⟪ c₂ ⟫

stepMacᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⟼ᵘ c₂) ->
         let p₂ = preservation⇝ p₁ (Mac s) in ⟪ c₁ ⟫ ⇝ᵗ ⟪ c₂ ⟫

stepᵘᵗ c (Mac s) = stepMacᵘᵗ c s
stepᵘᵗ (p $ p₁) (AppL s) = AppL (stepᵘᵗ p s)
stepᵘᵗ (Γ , Abs t $ p₁) Beta = Beta
stepᵘᵗ (Γ , Var p) Lookup rewrite lookup⟪ Γ , p ⟫ = Lookup
stepᵘᵗ (Γ , App t t₃) Dist-$ = Dist-$
stepᵘᵗ (Γ , (If t₃ Then t₄ Else t₅)) Dist-If = Dist-If
stepᵘᵗ (If p Then p₁ Else p₂) (IfCond s) = IfCond (stepᵘᵗ p s)
stepᵘᵗ (If Γ , True Then p₁ Else p₂) IfTrue = IfTrue
stepᵘᵗ (If Γ , False Then p₁ Else p₂) IfFalse = IfFalse
stepᵘᵗ (Γ , ∙) Dist-∙ = Dist-∙
stepᵘᵗ ∙ Hole = Hole

stepMacᵘᵗ (Γ , Return t₁) Return = Mac Return
stepMacᵘᵗ (Γ , t >>= t₁) Dist->>= = Mac Dist->>=
stepMacᵘᵗ (p >>= p₁) (BindCtx s) = Mac (BindCtx (stepᵘᵗ p s))
stepMacᵘᵗ ((Γ , Mac t₁) >>= p₁) Bind = Mac Bind
stepMacᵘᵗ ((Γ , Macₓ t₁) >>= p₁) BindEx = Mac BindEx
stepMacᵘᵗ (Γ , Throw t) Throw = Mac Throw
stepMacᵘᵗ (Γ , Catch t₁ t₂) Dist-Catch = Mac Dist-Catch
stepMacᵘᵗ (Catch p p₁) (CatchCtx s) = Mac (CatchCtx (stepᵘᵗ p s))
stepMacᵘᵗ (Catch (Γ , Mac t₁) p₁) Catch = Mac Catch
stepMacᵘᵗ (Catch (Γ , Macₓ t₁) p₁) CatchEx = Mac CatchEx
stepMacᵘᵗ (Γ , label p t₁) (label .p) = Mac (label p)
stepMacᵘᵗ (Γ , unlabel x t₁) Dist-unlabel = Mac (Dist-unlabel x)
stepMacᵘᵗ (Γ , join x t) (Dist-join .x) = Mac (Dist-join x)
stepMacᵘᵗ (unlabel x (Γ , Res t)) unlabel = Mac (unlabel x)
stepMacᵘᵗ (unlabel x (Γ , Resₓ t)) unlabelEx = Mac (unlabelEx x)
stepMacᵘᵗ (unlabel x c) (unlabelCtx s) = Mac (unlabelCtx x (stepᵘᵗ c s))
stepMacᵘᵗ (join x c) (joinCtx .x s) = Mac (joinCtx x (stepᵘᵗ c s))
stepMacᵘᵗ (join x (Γ , Mac t)) (join .x) = Mac (join x)
stepMacᵘᵗ (join x (Γ , Macₓ t)) (joinEx .x) = Mac (joinEx x)

-- Just a better looking entry point for stepᵘᵗ, where the proof that c₁ is well-typed
-- is passed as an instance argument
step⟪_⟫ : ∀ {τ} {c₁ c₂ : CTermᵘ} {{p : c₁ :: τ}} -> (s : c₁ ⇝ᵘ c₂) ->
                let arg = preservation⇝ p s in ⟪ c₁ ⟫ ⇝ᵗ ⟪ c₂ ⟫
step⟪_⟫ {{p}} s = stepᵘᵗ p s

lookup⟦_⟧ : ∀ {Δ τ} {{Γ : Envᵗ Δ}} -> (p : τ ∈ Δ) -> ⟦ p !! Γ ⟧ ≡ lookup (fin p) map⟦ Γ ⟧
lookup⟦_⟧ {{Γ = []}} ()
lookup⟦_⟧ {{Γ = x ∷ Γ}} Here = refl
lookup⟦_⟧ {{Γ = x ∷ Γ}} (There p) rewrite lookup⟦ p ⟧ = refl

--------------------------------------------------------------------------------

-- It is possible instead to safely remove types from the typed small step semantics
-- and retrieve the untyped semantics
step⟦_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> c₁ ⇝ᵗ c₂ -> ⟦ c₁ ⟧ ⇝ᵘ ⟦ c₂ ⟧
stepMac⟦_⟧ : ∀ {l τ} {c₁ c₂ : CTermᵗ (Mac l τ)} -> c₁ ⟼ᵗ c₂ -> ⟦ c₁ ⟧ ⟼ᵘ ⟦ c₂ ⟧

stepMac⟦ Return ⟧ = Return
stepMac⟦ Dist->>= ⟧ = Dist->>=
stepMac⟦ BindCtx s ⟧ = BindCtx step⟦ s ⟧
stepMac⟦ Bind ⟧ = Bind
stepMac⟦ BindEx ⟧ = BindEx
stepMac⟦ Throw ⟧ = Throw
stepMac⟦ Dist-Catch ⟧ = Dist-Catch
stepMac⟦ CatchCtx s ⟧ = CatchCtx step⟦ s ⟧
stepMac⟦ Catch ⟧ = Catch
stepMac⟦ CatchEx ⟧ = CatchEx
stepMac⟦ label p ⟧ = label p
stepMac⟦ Dist-unlabel p ⟧ = Dist-unlabel
stepMac⟦ unlabel p ⟧ = unlabel
stepMac⟦ unlabelEx p ⟧ = unlabelEx
stepMac⟦ Dist-join p ⟧ = Dist-join p
stepMac⟦ join x ⟧ = join x
stepMac⟦ joinEx x ⟧ = joinEx x
stepMac⟦ joinCtx x s ⟧ = joinCtx x step⟦ s ⟧
stepMac⟦ unlabelCtx p s ⟧ = unlabelCtx step⟦ s ⟧

step⟦ Mac s ⟧ = Mac (stepMac⟦ s ⟧)
step⟦ AppL s ⟧ = AppL step⟦ s ⟧
step⟦ Beta ⟧ = Beta
step⟦_⟧ {c₁ = Γ , Var p} Lookup rewrite lookup⟦ p ⟧ = Lookup
step⟦ Dist-$ ⟧ = Dist-$
step⟦ Dist-If ⟧ = Dist-If
step⟦ IfCond s ⟧ = IfCond step⟦ s ⟧
step⟦ IfTrue ⟧ = IfTrue
step⟦ IfFalse ⟧ = IfFalse
step⟦ Dist-∙ ⟧ = Dist-∙
step⟦ Hole ⟧ = Hole

-- Completness for small-step semantics transformations.
-- Converting a typed step to untyped and back to typed does not change the semantics, i.e. 
-- we get the same step.

-- Lemma
-- Each type of small step as at most one inhabitant.
uniqueStepᵘ : ∀ {c₁ c₂} -> (p q : c₁ ⇝ᵘ c₂) -> p ≡ q

uniqueStepᵘ⟼ : ∀ {c₁ c₂} -> (s₁ s₂ : c₁ ⟼ᵘ c₂) -> s₁ ≡ s₂
uniqueStepᵘ⟼ Return Return = refl
uniqueStepᵘ⟼ Dist->>= Dist->>= = refl
uniqueStepᵘ⟼ (BindCtx p) (BindCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ⟼ Bind Bind = refl
uniqueStepᵘ⟼ BindEx BindEx = refl
uniqueStepᵘ⟼ Throw Throw = refl
uniqueStepᵘ⟼ Dist-Catch Dist-Catch = refl
uniqueStepᵘ⟼ (CatchCtx p) (CatchCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ⟼ Catch Catch = refl
uniqueStepᵘ⟼ CatchEx CatchEx = refl
uniqueStepᵘ⟼ (label p) (label .p) = refl
uniqueStepᵘ⟼ Dist-unlabel Dist-unlabel = refl
uniqueStepᵘ⟼ unlabel unlabel = refl
uniqueStepᵘ⟼ (unlabelCtx p) (unlabelCtx q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ⟼ unlabelEx unlabelEx = refl
uniqueStepᵘ⟼ (Dist-join x) (Dist-join .x) = refl
uniqueStepᵘ⟼ (joinCtx x s₁) (joinCtx .x s₂) rewrite uniqueStepᵘ s₁ s₂ = refl
uniqueStepᵘ⟼ (join x) (join .x) = refl 
uniqueStepᵘ⟼ (joinEx x) (joinEx .x) = refl

uniqueStepMixedᵘ : ∀ {c₁ c₂} -> (s₁ : c₁ ⇝ᵘ c₂) (s₂ : c₁ ⟼ᵘ c₂) -> s₁ ≡ (Mac s₂)
uniqueStepMixedᵘ (AppL s₁) ()
uniqueStepMixedᵘ Beta ()
uniqueStepMixedᵘ Lookup ()
uniqueStepMixedᵘ Dist-$ ()
uniqueStepMixedᵘ Dist-If ()
uniqueStepMixedᵘ (IfCond s₁) ()
uniqueStepMixedᵘ IfTrue ()
uniqueStepMixedᵘ IfFalse ()
uniqueStepMixedᵘ (Mac s₁) s₂ rewrite uniqueStepᵘ⟼ s₁ s₂ = refl
uniqueStepMixedᵘ Dist-∙ ()
uniqueStepMixedᵘ Hole ()

uniqueStepᵘ (Mac s₁) s₂ = sym (uniqueStepMixedᵘ s₂ s₁)
uniqueStepᵘ s₁ (Mac s₂) = uniqueStepMixedᵘ s₁ s₂
uniqueStepᵘ (AppL p) (AppL q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ Beta Beta = refl
uniqueStepᵘ Lookup Lookup = refl
uniqueStepᵘ Dist-$ Dist-$ = refl
uniqueStepᵘ Dist-If Dist-If = refl
uniqueStepᵘ (IfCond p) (IfCond q) rewrite uniqueStepᵘ p q = refl
uniqueStepᵘ IfTrue IfTrue = refl
uniqueStepᵘ IfFalse IfFalse = refl
uniqueStepᵘ Dist-∙ Dist-∙ = refl
uniqueStepᵘ Hole Hole = refl

complete-step⟪_,_⟫ : ∀ {c₁ c₂ τ} {{p : c₁ :: τ}} {{q : c₂ :: τ}} ->
                              (s₁ : c₁ ⇝ᵘ c₂) (s₂ : ⟦ ⟪_⟫ c₁ {{p}} ⟧ ⇝ᵘ ⟦ ⟪_⟫ c₂ {{q}} ⟧) -> s₁ ≅ s₂
complete-step⟪_,_⟫ {{p}} {{q}} s₁ s₂ rewrite complete-⟪ p ⟫ | complete-⟪ q ⟫ | uniqueStepᵘ s₁ s₂ = refl

--------------------------------------------------------------------------------

uniqueStepᵗ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (s₁ s₂ : c₁ ⇝ᵗ c₂) -> s₁ ≡ s₂
uniqueStepᵗ⟼ : ∀ {l τ} {c₁ c₂ : CTermᵗ (Mac l τ)} -> (s₁ s₂ : c₁ ⟼ᵗ c₂) -> s₁ ≡ s₂
uniqueStepMixedᵗ : ∀ {l τ} {c₁ c₂ : CTermᵗ (Mac l τ)} -> (s₁ : c₁ ⇝ᵗ c₂) (s₂ : c₁ ⟼ᵗ c₂) -> s₁ ≡ Mac s₂

uniqueStepᵗ⟼ Return Return = refl
uniqueStepᵗ⟼ Dist->>= Dist->>= = refl
uniqueStepᵗ⟼ (BindCtx p) (BindCtx q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ⟼ Bind Bind = refl
uniqueStepᵗ⟼ BindEx BindEx = refl
uniqueStepᵗ⟼ Throw Throw = refl
uniqueStepᵗ⟼ Dist-Catch Dist-Catch = refl
uniqueStepᵗ⟼ (CatchCtx p) (CatchCtx q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ⟼ Catch Catch = refl
uniqueStepᵗ⟼ CatchEx CatchEx = refl
uniqueStepᵗ⟼ (label p) (label .p) = refl
uniqueStepᵗ⟼ (Dist-unlabel p) (Dist-unlabel .p) = refl
uniqueStepᵗ⟼ (unlabel p) (unlabel .p) = refl
uniqueStepᵗ⟼ (unlabelCtx x p) (unlabelCtx .x q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ⟼ (unlabelEx .x) (unlabelEx x) = refl
uniqueStepᵗ⟼ (Dist-join x) (Dist-join .x) = refl
uniqueStepᵗ⟼ (joinCtx x s₁) (joinCtx .x s₂) rewrite uniqueStepᵗ s₁ s₂ = refl
uniqueStepᵗ⟼ (join x) (join .x) = refl 
uniqueStepᵗ⟼ (joinEx x) (joinEx .x) = refl

uniqueStepMixedᵗ (AppL s₁) ()
uniqueStepMixedᵗ Beta ()
uniqueStepMixedᵗ Lookup ()
uniqueStepMixedᵗ Dist-$ ()
uniqueStepMixedᵗ Dist-If ()
uniqueStepMixedᵗ (IfCond s₁) ()
uniqueStepMixedᵗ IfTrue ()
uniqueStepMixedᵗ IfFalse ()
uniqueStepMixedᵗ (Mac s₁) s₂ rewrite uniqueStepᵗ⟼ s₁ s₂ = refl
uniqueStepMixedᵗ Dist-∙ ()
uniqueStepMixedᵗ Hole ()

uniqueStepᵗ (Mac s₁) s₂ = sym (uniqueStepMixedᵗ s₂ s₁)
uniqueStepᵗ s₁ (Mac s₂) = uniqueStepMixedᵗ s₁ s₂
uniqueStepᵗ (AppL p) (AppL q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ Beta Beta = refl
uniqueStepᵗ Lookup Lookup = refl
uniqueStepᵗ Dist-$ Dist-$ = refl
uniqueStepᵗ Dist-If Dist-If = refl
uniqueStepᵗ (IfCond p) (IfCond q) rewrite uniqueStepᵗ p q = refl
uniqueStepᵗ IfTrue IfTrue = refl
uniqueStepᵗ IfFalse IfFalse = refl
uniqueStepᵗ Dist-∙ Dist-∙ = refl
uniqueStepᵗ Hole Hole = refl

complete-step⟦_,_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> (s₁ : c₁ ⇝ᵗ c₂) ->
                     let p₁ = sound-⟦ c₁ ⟧
                         p₂ = sound-⟦ c₂ ⟧ in (s₂ : ⟪ ⟦ c₁ ⟧ ⟫ ⇝ᵗ ⟪ ⟦ c₂ ⟧ ⟫) -> s₁ ≅ s₂
complete-step⟦_,_⟧ {_} {c₁} {c₂} s₁ s₂ rewrite complete-⟦ c₁ ⟧ | complete-⟦ c₂ ⟧ | uniqueStepᵗ s₁ s₂ = refl
