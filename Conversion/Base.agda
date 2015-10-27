module Conversion.Base where

open import Typed.Base renaming (Term to Termᵗ ; CTerm to CTermᵗ ; Env to Envᵗ)
open import Typed.Semantics renaming (_⟼_ to _⟼ᵗ_)
open import Untyped.Base renaming (Term to Termᵘ ; CTerm to CTermᵘ ; Env to Envᵘ)
open import Untyped.Semantics renaming (_⟼_ to _⟼ᵘ_)

--------------------------------------------------------------------------------
-- Typed to untyped

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

--------------------------------------------------------------------------------
-- Untyped to Typed

convertᵘᵗ : ∀ {Δ τ} {t : Termᵘ (length Δ)} -> Δ ⊢ t ∷ τ -> Termᵗ Δ τ
convertᵘᵗ True = True
convertᵘᵗ False = False
convertᵘᵗ (App f x) = App (convertᵘᵗ f) (convertᵘᵗ x)
convertᵘᵗ (Abs t) = Abs (convertᵘᵗ t)
convertᵘᵗ (Var p) = Var p
convertᵘᵗ (If c Then t Else e) = If (convertᵘᵗ c) Then (convertᵘᵗ t) Else (convertᵘᵗ e)
convertᵘᵗ (Return t) = Return (convertᵘᵗ t)
convertᵘᵗ (m >>= k) = (convertᵘᵗ m) >>= (convertᵘᵗ k)
convertᵘᵗ ξ = ξ
convertᵘᵗ (Throw t) = Throw (convertᵘᵗ t)
convertᵘᵗ (Catch m h) = Catch (convertᵘᵗ m) (convertᵘᵗ h)
convertᵘᵗ (Mac t) = Mac (convertᵘᵗ t)
convertᵘᵗ (Macₓ t) = Macₓ (convertᵘᵗ t)
convertᵘᵗ (label p t) = label p (convertᵘᵗ t)
convertᵘᵗ (unlabel x t) = unlabel x (convertᵘᵗ t)
convertᵘᵗ (Res t) = Res (convertᵘᵗ t)
convertᵘᵗ ∙ = ∙

-- Just a better looking for the conversion function convertᵘᵗ in which
-- the typing judgment is passed as an instance argument
⌜_⌝ : ∀ {Δ τ} (t : Termᵘ (length Δ)) ->{{p : Δ ⊢ t ∷ τ}} -> Termᵗ Δ τ
⌜_⌝ _ {{p}} = convertᵘᵗ p

-- Conversion from well-typed closed term to typed closed term
convertCᵘᵗ : ∀ {τ c} -> c :: τ -> CTermᵗ τ

-- Conversion from well-typed enviroment to typed environment
convertEnvᵘᵗ : ∀ {Δ} {Γ : Envᵘ (length Δ)} -> TEnv Δ Γ -> Envᵗ Δ

convertCᵘᵗ (Γ , t) = convertEnvᵘᵗ Γ , convertᵘᵗ t
convertCᵘᵗ (f $ x) = (convertCᵘᵗ f) $ (convertCᵘᵗ x)
convertCᵘᵗ (If c Then t Else e) = If (convertCᵘᵗ c) Then (convertCᵘᵗ t) Else (convertCᵘᵗ e)
convertCᵘᵗ (m >>= k) = (convertCᵘᵗ m) >>= (convertCᵘᵗ k)
convertCᵘᵗ (Catch m h) = Catch (convertCᵘᵗ m) (convertCᵘᵗ h)
convertCᵘᵗ (unlabel x c) = unlabel x (convertCᵘᵗ c)
convertCᵘᵗ ∙ = ∙

convertEnvᵘᵗ [] = []
convertEnvᵘᵗ (c ∷ Γ) = (convertCᵘᵗ c) ∷ (convertEnvᵘᵗ Γ)

-- Better looking entry points for conversion functions in which
-- the well-typedness proof is passed as an implicit parameter
⟪_⟫ : ∀ {{τ}} -> (c : CTermᵘ) -> {{p : c :: τ}} -> CTermᵗ τ
⟪_⟫ _ {{p}} = convertCᵘᵗ p

map⟪_⟫ : ∀ {Δ} -> (Γ : Envᵘ (length Δ)) -> {{p : TEnv Δ Γ}} -> Envᵗ Δ
map⟪_⟫ _ {{p}} = convertEnvᵘᵗ p
