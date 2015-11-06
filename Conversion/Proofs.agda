module Conversion.Proofs where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)
open import Untyped.Proofs
open import Conversion.Base public
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Soundness results
--------------------------------------------------------------------------------

-- Soundness for typed terms

-- A typed term preserves its type when converted.
sound-⌞_⌟ : ∀ {τ Δ} -> (t : Termᵗ Δ τ) -> Δ ⊢ ⌞ t ⌟ ∷ τ
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
sound-⌞ label x t ⌟ = label x (sound-⌞ t ⌟)
sound-⌞ unlabel x t ⌟ = unlabel x (sound-⌞ t ⌟)
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
complete-⌞ label x t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ unlabel x t ⌟ rewrite complete-⌞ t ⌟ = refl
complete-⌞ ∙ ⌟ = refl

-- Closed terms
-- ⟪_⟫ ∘ ⟦_⟧ ≡ id
complete-⟦_⟧  : ∀ {τ} -> (c : CTermᵗ τ) ->
                let p = sound-⟦ c ⟧ in ⟪ ⟦ c ⟧ ⟫ ≡ c

-- Enviroments
complete-map⟦_⟧ : ∀ {Δ} -> (Γ : Envᵗ Δ) ->
                  let p = sound-map⟦ Γ ⟧ in map⟪ map⟦ Γ ⟧ ⟫ ≡ Γ

complete-⟦ Γ , t ⟧ rewrite complete-map⟦ Γ ⟧ | complete-⌞ t ⌟ = refl
complete-⟦ f $ x ⟧ rewrite complete-⟦ f ⟧ | complete-⟦ x ⟧ = refl
complete-⟦ If c Then t Else e ⟧ rewrite complete-⟦ c ⟧ | complete-⟦ t ⟧ | complete-⟦ e ⟧ = refl
complete-⟦ m >>= k ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ k ⟧ = refl
complete-⟦ Catch m h ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ h ⟧ = refl
complete-⟦ unlabel x c ⟧ rewrite complete-⟦ c ⟧ = refl
complete-⟦ ∙ ⟧ = refl

complete-map⟦ [] ⟧ = refl
complete-map⟦ x ∷ Γ ⟧ rewrite complete-⟦ x ⟧ | complete-map⟦ Γ ⟧ = refl

--------------------------------------------------------------------------------

-- Completness for untyped terms
-- Unfortunately not always the instance arguments are not resolved in the
-- signatures so I need to pass them explicitly.
-- I provided the uncluttered version in a comment

-- ⌞ ⌜ t ⌝ ⌟ ≡ t
-- ⌞_⌟ ∘ ⌜_⌝ ≡ id
complete-⌜_⌝ : ∀ {Δ τ} {t : Termᵘ (length Δ)} -> (p : Δ ⊢ t ∷ τ) -> ⌞ ⌜_⌝ t {{p}} ⌟ ≡ t
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
complete-⌜ Res t ⌝ rewrite complete-⌜ t ⌝ = refl
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
complete-⟪ ∙ ⟫ = refl

--------------------------------------------------------------------------------
-- Equivalence between small step semantics
--------------------------------------------------------------------------------

lookup⟪_,_⟫ : ∀ {Δ τ} {Γ : Envᵘ (length Δ)} (Γᵗ : TEnv Δ Γ) (x : τ ∈ Δ) ->
              let p = lookup-fin x Γᵗ in ⟪ lookup (fin x) Γ ⟫ ≡ x !! map⟪ Γ ⟫
lookup⟪ x ∷ Γᵗ , Here ⟫ = refl
lookup⟪ x ∷ Γᵗ , There p ⟫ rewrite lookup⟪ Γᵗ , p ⟫ = refl

-- If c₁ ⟼ᵘ c₂ and c₁ is well-typed then we can produce an equivalent typed small step between
stepᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p₁ : c₁ :: τ) -> (s : c₁ ⟼ᵘ c₂) ->
         let p₂ = preservation p₁ s in ⟪ c₁ ⟫ ⟼ᵗ ⟪ c₂ ⟫
stepᵘᵗ (p $ p₁) (AppL s) = AppL (stepᵘᵗ p s)
stepᵘᵗ (Γ , Abs t $ p₁) Beta = Beta
stepᵘᵗ (Γ , Var p) Lookup rewrite lookup⟪ Γ , p ⟫ = Lookup
stepᵘᵗ (Γ , App t t₃) Dist-$ = Dist-$
stepᵘᵗ (Γ , (If t₃ Then t₄ Else t₅)) Dist-If = Dist-If
stepᵘᵗ (If p Then p₁ Else p₂) (IfCond s) = IfCond (stepᵘᵗ p s)
stepᵘᵗ (If Γ , True Then p₁ Else p₂) IfTrue = IfTrue
stepᵘᵗ (If Γ , False Then p₁ Else p₂) IfFalse = IfFalse
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
stepᵘᵗ (unlabel x (Γ , Res t₁)) unlabel = unlabel x
stepᵘᵗ (unlabel x (Γ , App t t₃)) (unlabelCtx Dist-$) = unlabelCtx x Dist-$
stepᵘᵗ (unlabel x (Γ , Var p)) (unlabelCtx Lookup) = unlabelCtx x (stepᵘᵗ (Γ , Var p) Lookup )
stepᵘᵗ (unlabel x (Γ , (If t Then t₄ Else t₅))) (unlabelCtx Dist-If) = unlabelCtx x Dist-If
stepᵘᵗ (unlabel x (Γ , Res t₁)) (unlabelCtx ())
stepᵘᵗ (unlabel x (Γ , ∙)) (unlabelCtx s) = unlabelCtx x (stepᵘᵗ (Γ , ∙) s)
stepᵘᵗ (unlabel x (p $ p₁)) (unlabelCtx (AppL s)) = unlabelCtx x (AppL (stepᵘᵗ p s))
stepᵘᵗ (unlabel x (p $ p₁)) (unlabelCtx Beta) = unlabelCtx x (stepᵘᵗ (p $ p₁) Beta)
stepᵘᵗ (unlabel x (If p Then p₁ Else p₂)) (unlabelCtx s) = unlabelCtx x (stepᵘᵗ (If p Then p₁ Else p₂) s)
stepᵘᵗ (unlabel x ∙) (unlabelCtx s) = unlabelCtx x (stepᵘᵗ ∙ s)
stepᵘᵗ (Γ , ∙) Dist-∙ = Dist-∙
stepᵘᵗ ∙ Hole = Hole

-- Just a better looking entry point for stepᵘᵗ, where the proof that c₁ is well-typed
-- is passed as an instance argument

-- TODO: Try to prove that the steps (both directions) do not miss the case where [[ ]] or << >> switch
-- branches.

step⟪_⟫ : ∀ {τ} {c₁ c₂ : CTermᵘ} {{p : c₁ :: τ}} -> (s : c₁ ⟼ᵘ c₂) ->
                let arg = preservation p s in ⟪ c₁ ⟫ ⟼ᵗ ⟪ c₂ ⟫
step⟪_⟫ {{p}} s = stepᵘᵗ p s

-- It is possible instead to safely remove types from the typed small step semantics
-- and retrieve the untyped semantics
step⟦_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> c₁ ⟼ᵗ c₂ -> ⟦ c₁ ⟧ ⟼ᵘ ⟦ c₂ ⟧

lookup⟦_⟧ : ∀ {Δ τ} {{Γ : Envᵗ Δ}} -> (p : τ ∈ Δ) -> ⟦ p !! Γ ⟧ ≡ lookup (fin p) map⟦ Γ ⟧
lookup⟦_⟧ {{Γ = []}} ()
lookup⟦_⟧ {{Γ = x ∷ Γ}} Here = refl
lookup⟦_⟧ {{Γ = x ∷ Γ}} (There p) rewrite lookup⟦ p ⟧ = refl

step⟦ AppL s ⟧ = AppL step⟦ s ⟧
step⟦ Beta ⟧ = Beta
step⟦_⟧ {c₁ = Γ , Var p} Lookup rewrite lookup⟦ p ⟧ = Lookup
step⟦ Dist-$ ⟧ = Dist-$
step⟦ Dist-If ⟧ = Dist-If
step⟦ IfCond s ⟧ = IfCond step⟦ s ⟧
step⟦ IfTrue ⟧ = IfTrue
step⟦ IfFalse ⟧ = IfFalse
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
step⟦ unlabelCtx p s ⟧ = unlabelCtx step⟦ s ⟧
step⟦ Dist-∙ ⟧ = Dist-∙
step⟦ Hole ⟧ = Hole

--------------------------------------------------------------------------------

-- Completness for small-step semantics transformations.
-- Converting a typed step to untyped and back to typed does not change the semantics, i.e. 
-- we get the same step.

-- Lemma
-- Each type of small step as at most one inhabitant.
uniqueStep : ∀ {c₁ c₂} -> (p q : c₁ ⟼ᵘ c₂) -> p ≡ q
uniqueStep (AppL p) (AppL q) rewrite uniqueStep p q = refl
uniqueStep Beta Beta = refl
uniqueStep Lookup Lookup = refl
uniqueStep Dist-$ Dist-$ = refl
uniqueStep Dist-If Dist-If = refl
uniqueStep (IfCond p) (IfCond q) rewrite uniqueStep p q = refl
uniqueStep IfTrue IfTrue = refl
uniqueStep IfFalse IfFalse = refl
uniqueStep Return Return = refl
uniqueStep Dist->>= Dist->>= = refl
uniqueStep (BindCtx p) (BindCtx q) rewrite uniqueStep p q = refl
uniqueStep Bind Bind = refl
uniqueStep BindEx BindEx = refl
uniqueStep Throw Throw = refl
uniqueStep Dist-Catch Dist-Catch = refl
uniqueStep (CatchCtx p) (CatchCtx q) rewrite uniqueStep p q = refl
uniqueStep Catch Catch = refl
uniqueStep CatchEx CatchEx = refl
uniqueStep (label p) (label .p) = refl
uniqueStep Dist-unlabel Dist-unlabel = refl
uniqueStep unlabel unlabel = refl
uniqueStep (unlabelCtx p) (unlabelCtx q) rewrite uniqueStep p q = refl
uniqueStep Dist-∙ Dist-∙ = refl
uniqueStep Hole Hole = refl

open import Relation.Binary.HeterogeneousEquality

complete-step⟪_,_⟫ : ∀ {c₁ c₂ τ} {{p : c₁ :: τ}} {{q : c₂ :: τ}} ->
                              (s₁ : c₁ ⟼ᵘ c₂) (s₂ : ⟦ ⟪_⟫ c₁ {{p}} ⟧ ⟼ᵘ ⟦ ⟪_⟫ c₂ {{q}} ⟧) -> s₁ ≅ s₂
complete-step⟪_,_⟫ {{p}} {{q}} s₁ s₂ rewrite complete-⟪ p ⟫ | complete-⟪ q ⟫ | uniqueStep s₁ s₂ = refl

-- TODO prove similarly complete-step⟦_,_⟧
