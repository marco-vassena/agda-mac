module Misc where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)
open import Untyped.Proofs
open import Relation.Binary.PropositionalEquality

-- Untype function
⌞_⌟ : ∀ {τ Δ} -> Termᵗ Δ τ -> Termᵘ (length Δ)
⌞ True ⌟ = True
⌞ False ⌟ = False
⌞ Var x ⌟ = Var (fin x)
⌞ Abs t ⌟ = Abs ⌞ t ⌟
⌞ App f x ⌟ = App ⌞ f ⌟ ⌞ x ⌟
⌞ If c Then t Else e ⌟ = If ⌞ c ⌟ Then ⌞ t ⌟ Else ⌞ e ⌟
⌞ Return t ⌟ = Return ⌞ t ⌟
⌞ m >>= k ⌟ = ⌞ m ⌟ >>= ⌞ k ⌟
⌞ ξ ⌟ = ξ
⌞ Throw t ⌟ = Throw ⌞ t ⌟
⌞ Catch m h ⌟ = Catch ⌞ m ⌟ ⌞ h ⌟
⌞ Mac t ⌟ = Mac ⌞ t ⌟
⌞ Macₓ t ⌟ = Macₓ ⌞ t ⌟
⌞ Res {{l}} t ⌟ = Res l ⌞ t ⌟
⌞ label x t ⌟ = label x ⌞ t ⌟
⌞ unlabel x t ⌟ = unlabel ⌞ t ⌟
⌞ ∙ ⌟ = ∙

-- Equivalence between typed and untyped terms
convert : ∀ {τ Δ} -> (t : Termᵗ Δ τ) -> Δ ⊢ ⌞ t ⌟ ∷ τ
convert True = True
convert False = False
convert (Var x) = Var x
convert (Abs t) = Abs (convert t)
convert (App t t₁) = App (convert t) (convert t₁)
convert (If t Then t₁ Else t₂) = If convert t Then convert t₁ Else convert t₂
convert (Return t) = Return (convert t)
convert (t >>= t₁) = convert t >>= convert t₁
convert ξ = ξ
convert (Throw t) = Throw (convert t)
convert (Catch t t₁) = Catch (convert t) (convert t₁)
convert (Mac t) = Mac (convert t)
convert (Macₓ t) = Macₓ (convert t)
convert (Res t) = Res (convert t)
convert (label x t) = label x (convert t)
convert (unlabel x t) = unlabel x (convert t)
convert ∙ = ∙

⟦_⟧ : ∀ {τ} -> CTermᵗ τ -> CTermᵘ
map⟦_⟧ : ∀ {Δ} -> Envᵗ Δ -> Envᵘ (length Δ)

⟦ Γ , t ⟧ = map⟦ Γ ⟧ , ⌞ t ⌟
⟦ f $ x ⟧ = ⟦ f ⟧ $ ⟦ x ⟧
⟦ If c Then t Else e ⟧ = If ⟦ c ⟧ Then ⟦ t ⟧ Else ⟦ e ⟧
⟦ m >>= k ⟧ = ⟦ m ⟧ >>= ⟦ k ⟧
⟦ Catch m h ⟧ = Catch ⟦ m ⟧ ⟦ h ⟧
⟦ unlabel x c ⟧ = unlabel ⟦ c ⟧
⟦ ∙ ⟧ = ∙

map⟦ [] ⟧ = []
map⟦ x ∷ Γ ⟧ = ⟦ x ⟧ ∷ map⟦ Γ ⟧

-- Convert closed term
convertCᵘ  : ∀ {τ} -> (c : CTermᵗ τ) -> ⟦ c ⟧ :: τ
convertΓᵘ : ∀ {Δ} -> (Γ : Envᵗ Δ) -> TEnv Δ map⟦ Γ ⟧

convertCᵘ (Γ , t) = (convertΓᵘ Γ) , convert t
convertCᵘ (f $ x) = (convertCᵘ f) $ (convertCᵘ x)
convertCᵘ (If c Then t Else e) = If (convertCᵘ c) Then (convertCᵘ t) Else (convertCᵘ e)
convertCᵘ (m >>= k) = (convertCᵘ m) >>= (convertCᵘ k)
convertCᵘ (Catch m h) = Catch (convertCᵘ m) (convertCᵘ h)
convertCᵘ (unlabel x c) = unlabel x (convertCᵘ c)
convertCᵘ ∙ = ∙

convertΓᵘ [] = []
convertΓᵘ (x ∷ Γ) = convertCᵘ x ∷ convertΓᵘ Γ

-- Convertion in the opposite direction, from untyped to typed
⌜_⌝ : ∀ {Δ τ} {t : Termᵘ (length Δ)} -> Δ ⊢ t ∷ τ -> Termᵗ Δ τ
⌜ True ⌝ = True
⌜ False ⌝ = False
⌜ App f x ⌝ = App ⌜ f ⌝ ⌜ x ⌝
⌜ Abs t ⌝ = Abs ⌜ t ⌝
⌜ Var p ⌝ = Var p
⌜ If c Then t Else e ⌝ = If ⌜ c ⌝ Then ⌜ t ⌝ Else ⌜ e ⌝
⌜ Return t ⌝ = Return ⌜ t ⌝
⌜ m >>= k ⌝ = ⌜ m ⌝ >>= ⌜ k ⌝
⌜ ξ ⌝ = ξ
⌜ Throw t ⌝ = Throw ⌜ t ⌝
⌜ Catch m h ⌝ = Catch ⌜ m ⌝ ⌜ h ⌝
⌜ Mac t ⌝ = Mac ⌜ t ⌝
⌜ Macₓ t ⌝ = Macₓ ⌜ t ⌝
⌜ label p t ⌝ = label p ⌜ t ⌝
⌜ unlabel x t ⌝ = unlabel x ⌜ t ⌝
⌜ Res t ⌝ = Res ⌜ t ⌝
⌜ ∙ ⌝ = ∙

-- Conversion for closed untyped term
⟪_⟫ : ∀ {τ c} -> c :: τ -> CTermᵗ τ
map⟪_⟫ : ∀ {Δ} {Γ : Envᵘ (length Δ)} -> TEnv Δ Γ -> Envᵗ Δ

⟪ Γ , t ⟫ = map⟪ Γ ⟫ , ⌜ t ⌝
⟪ f $ x ⟫ = ⟪ f ⟫ $ ⟪ x ⟫
⟪ If c Then t Else e ⟫ = If ⟪ c ⟫ Then ⟪ t ⟫ Else ⟪ e ⟫
⟪ m >>= k ⟫ = ⟪ m ⟫ >>= ⟪ k ⟫
⟪ Catch m k ⟫ = Catch ⟪ m ⟫ ⟪ k ⟫
⟪ unlabel x c ⟫ = unlabel x ⟪ c ⟫
⟪ ∙ ⟫ = ∙ 

map⟪ [] ⟫ = []
map⟪ x ∷ Γ ⟫ = ∙ ∷ map⟪ Γ ⟫

--------------------------------------------------------------------------------
-- Equivalence between small step semantics
--------------------------------------------------------------------------------

-- TODO remove
-- @Ale This lemma cannot be proved and shows how the typed small semantics is strictly more 
-- expressive. In particular in the recursive cases subterms of the typing judgments are not
-- shared.
-- stepᵘᵗ : ∀ {τ} {c₁ c₂ : CTermᵘ} -> c₁ ⟼ᵘ c₂ -> (p : c₁ :: τ) (q : c₂ :: τ) -> ⟪ p ⟫ ⟼ᵗ ⟪ q ⟫
-- stepᵘᵗ (AppL s) (p $ p₁) (q $ q₁) = {!!}
-- stepᵘᵗ Beta (p $ p₁) q = {!!}
-- stepᵘᵗ Lookup p₁ q = {!!}
-- stepᵘᵗ Dist-$ p q = {!!}
-- stepᵘᵗ Dist-If p q = {!!}
-- stepᵘᵗ (IfCond s) (If c Then t Else e) (If c' Then t' Else e') = {!IfCond ?!} -- Does not work because t ≠ t' and e ≠ e'
-- stepᵘᵗ IfTrue p q = {!!}
-- stepᵘᵗ IfFalse p q = {!!}
-- stepᵘᵗ Return p q = {!!}
-- stepᵘᵗ Dist->>= p q = {!!}
-- stepᵘᵗ (BindCtx s) p q = {!!}
-- stepᵘᵗ Bind p q = {!!}
-- stepᵘᵗ BindEx p q = {!!}
-- stepᵘᵗ Throw p q = {!!}
-- stepᵘᵗ Dist-Catch p q = {!!}
-- stepᵘᵗ (CatchCtx s) p q = {!!}
-- stepᵘᵗ Catch p q = {!!}
-- stepᵘᵗ CatchEx p q = {!!}
-- stepᵘᵗ (label p) p₁ q = {!!}
-- stepᵘᵗ Dist-unlabel p q = {!!}
-- stepᵘᵗ unlabel p q = {!!}
-- stepᵘᵗ (unlabelCtx s) p q = {!!}
-- stepᵘᵗ Hole p q = {!!}
-- stepᵘᵗ Hole' p q = {!!}

-- It is possible instead to safely remove types from the typed small step semantics
-- and retrieve the untyped semantics
step⟦_⟧ : ∀ {τ} {c₁ c₂ : CTermᵗ τ} -> c₁ ⟼ᵗ c₂ -> ⟦ c₁ ⟧ ⟼ᵘ ⟦ c₂ ⟧

lookup⟦_⟧ : ∀ {Δ τ} {{Γ : Envᵗ Δ}} -> (p : τ ∈ Δ) -> ⟦ p !! Γ ⟧ ≡ lookup (fin p) map⟦ Γ ⟧
lookup⟦_⟧ {{Γ = []}} ()
lookup⟦_⟧ {{Γ = x ∷ Γ}} Here = refl
lookup⟦_⟧ {{Γ = x ∷ Γ}} (There p) rewrite lookup⟦ p ⟧ = refl

step⟦ AppL s ⟧ = AppL step⟦ s ⟧
step⟦ Beta ⟧ = Beta
step⟦_⟧ {_} {c₁ = Γ , Var p} Lookup rewrite lookup⟦ p ⟧ = Lookup
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
step⟦ Dist-unlabel ⟧ = Dist-unlabel
step⟦ unlabel ⟧ = unlabel
step⟦ unlabelCtx s ⟧ = unlabelCtx step⟦ s ⟧
step⟦ Hole ⟧ = Hole
step⟦ Hole' ⟧ = Hole'
