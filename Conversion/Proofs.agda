module Conversion.Proofs where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)
open import Untyped.Proofs
open import Conversion.Base
open import Relation.Binary.PropositionalEquality

-- Equivalence between typed and untyped terms
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
-- Converted typed closed term preserve type 
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
-- Completeness results
--------------------------------------------------------------------------------

-- Typed to untyped conversion

-- Simple terms
complete-⌞_⌟ : ∀ {Δ τ} -> (t : Termᵗ Δ τ) -> ⌜ sound-⌞ t ⌟ ⌝ ≡ t
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
complete-⟦_⟧  : ∀ {τ} -> (c : CTermᵗ τ) -> ⟪ sound-⟦ c ⟧ ⟫ ≡ c

-- Enviroments
complete-map⟦_⟧ : ∀ {Δ} -> (Γ : Envᵗ Δ) -> map⟪ sound-map⟦ Γ ⟧ ⟫ ≡ Γ 

complete-⟦ Γ , t ⟧ rewrite complete-map⟦ Γ ⟧ | complete-⌞ t ⌟ = refl
complete-⟦ f $ x ⟧ rewrite complete-⟦ f ⟧ | complete-⟦ x ⟧ = refl
complete-⟦ If c Then t Else e ⟧ rewrite complete-⟦ c ⟧ | complete-⟦ t ⟧ | complete-⟦ e ⟧ = refl
complete-⟦ m >>= k ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ k ⟧ = refl
complete-⟦ Catch m h ⟧ rewrite complete-⟦ m ⟧ | complete-⟦ h ⟧ = refl
complete-⟦ unlabel x c ⟧ rewrite complete-⟦ c ⟧ = refl
complete-⟦ ∙ ⟧ = refl

complete-map⟦ [] ⟧ = refl
complete-map⟦ x ∷ Γ ⟧ rewrite complete-⟦ x ⟧ | complete-map⟦ Γ ⟧ = refl

-- Untyped to typed conversion

complete-⌜_⌝ : ∀ {Δ τ} {t : Termᵘ (length Δ)} -> (p : Δ ⊢ t ∷ τ) -> ⌞ ⌜ p ⌝ ⌟ ≡ t
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

complete-⟪_⟫ : ∀ {τ c} (p : c :: τ) -> ⟦ ⟪ p ⟫ ⟧ ≡ c
complete-map⟪_⟫ : ∀ {Δ} {Γ : Envᵘ (length Δ)} -> (Γᵗ : TEnv Δ Γ) -> map⟦ map⟪ Γᵗ ⟫ ⟧ ≡ Γ

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

lookup⟪_,_⟫ : ∀ {Δ τ} {Γ : Envᵘ (length Δ)} (Γᵗ : TEnv Δ Γ) (p : τ ∈ Δ) -> ⟪ lookup-fin p Γᵗ ⟫ ≡ p !! map⟪ Γᵗ ⟫
lookup⟪ x ∷ Γᵗ , Here ⟫ = refl
lookup⟪ x ∷ Γᵗ , There p ⟫ rewrite lookup⟪ Γᵗ , p ⟫ = refl

-- If c₁ ⟼ᵘ c₂ and c₁ is well-typed then we can produce an equivalent typed small step between
stepᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> (p : c₁ :: τ) -> (s : c₁ ⟼ᵘ c₂) -> ⟪ p ⟫ ⟼ᵗ ⟪ preservation p s ⟫
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
step⟪_⟫ : ∀ {τ} {c₁ c₂ : CTermᵘ} {{p : c₁ :: τ}} -> (s : c₁ ⟼ᵘ c₂) -> ⟪ p ⟫ ⟼ᵗ ⟪ preservation p s ⟫
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