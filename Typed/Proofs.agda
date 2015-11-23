module Typed.Proofs where

open import Typed.Semantics
open import Relation.Binary.PropositionalEquality
open import Data.Sum

progress : ∀ {τ} -> (c : CTerm τ) -> (Redex c) ⊎ (IsValue c)
progress (Γ , （）) = inj₂ tt
progress (Γ , True) = inj₂ tt
progress (Γ , False) = inj₂ tt
progress (Γ , Var x) = inj₁ (Step Lookup)
progress (Γ , Abs t) = inj₂ tt
progress (Γ , App t t₁) = inj₁ (Step Dist-$)
progress (Γ , If t Then t₁ Else t₂) = inj₁ (Step Dist-If)
progress (Γ , Return t) = inj₁ (Step (Mac Return))
progress (Γ , t >>= t₁) = inj₁ (Step (Mac Dist->>=))
progress (Γ , ξ) = inj₂ tt
progress (Γ , Throw t) = inj₁ (Step (Mac Throw))
progress (Γ , Catch m h) = inj₁ (Step (Mac Dist-Catch))
progress (Γ , Mac t) = inj₂ tt
progress (Γ , Macₓ t) = inj₂ tt
progress (Γ , Res t) = inj₂ tt
progress (Γ , Resₓ t) = inj₂ tt
progress (Γ , label x t) = inj₁ (Step (Mac (label x)))
progress (Γ , unlabel x t) = inj₁ (Step (Mac (Dist-unlabel x)))
progress (Γ , join p t) = inj₁ (Step (Mac (Dist-join p)))
progress (Γ , ∙) = inj₁ (Step Dist-∙)
progress (c $ c₁) with progress c
progress (c $ c₁) | inj₁ (Step x) = inj₁ (Step (AppL x))
progress (x , Var x₁ $ c₁) | inj₂ ()
progress (x , Abs x₁ $ c₁) | inj₂ tt = inj₁ (Step Beta)
progress (x , App x₁ x₂ $ c₁) | inj₂ ()
progress (x , If x₁ Then x₂ Else x₃ $ c₁) | inj₂ ()
progress (x , ∙ $ c₁) | inj₂ ()
progress ((c $ c₁) $ c₂) | inj₂ ()
progress (If c Then c₁ Else c₂ $ c₃) | inj₂ ()
progress (∙ $ c₂) | inj₂ ()
progress (If c Then c₁ Else c₂) with progress c
progress (If c Then c₁ Else c₂) | inj₁ (Step x) = inj₁ (Step (IfCond x))
progress (If x , True Then c₁ Else c₂) | inj₂ y = inj₁ (Step IfTrue)
progress (If x , False Then c₁ Else c₂) | inj₂ y = inj₁ (Step IfFalse)
progress (If x , Var x₁ Then c₁ Else c₂) | inj₂ ()
progress (If x , App x₁ x₂ Then c₁ Else c₂) | inj₂ ()
progress (If x , If x₁ Then x₂ Else x₃ Then c₁ Else c₂) | inj₂ ()
progress (If x , ∙ Then c₁ Else c₂) | inj₂ ()
progress (If c $ c₁ Then c₂ Else c₃) | inj₂ ()
progress (If If c Then c₁ Else c₂ Then c₃ Else c₄) | inj₂ ()
progress (If ∙ Then c₁ Else c₂) | inj₂ ()
progress (c >>= c₁) with progress c
progress (c >>= c₁) | inj₁ (Step x) = inj₁ (Step (Mac (BindCtx x)))
progress ((x , Var x₁) >>= c₁) | inj₂ ()
progress ((x , App x₁ x₂) >>= c₁) | inj₂ ()
progress ((x , If x₁ Then x₂ Else x₃) >>= c₁) | inj₂ ()
progress ((x , Return x₁) >>= c₁) | inj₂ ()
progress ((x , x₁ >>= x₂) >>= c₁) | inj₂ ()
progress ((x , Throw x₁) >>= c₁) | inj₂ ()
progress ((x , Catch x₁ x₂) >>= c₁) | inj₂ ()
progress ((x , Mac x₁) >>= c₁) | inj₂ tt = inj₁ (Step (Mac Bind))
progress ((Γ , Macₓ e) >>= k) | inj₂ tt = inj₁ (Step (Mac BindEx))
progress ((x , label x₁ x₂) >>= c₁) | inj₂ ()
progress ((x , unlabel x₁ x₂) >>= c₁) | inj₂ ()
progress ((Γ , join p t) >>= k) | inj₂ ()
progress ((x , ∙) >>= c₁) | inj₂ ()
progress ((c $ c₁) >>= c₂) | inj₂ ()
progress (If c Then c₁ Else c₂ >>= c₃) | inj₂ ()
progress (c >>= c₁ >>= c₂) | inj₂ ()
progress (Catch c c₁ >>= c₂) | inj₂ ()
progress (unlabel x c >>= c₁) | inj₂ ()
progress (∙ >>= c₁) | inj₂ ()
progress (join p c >>= k) | inj₂ ()
progress (join p c) with progress c
progress (join p c) | inj₁ (Step x) = inj₁ (Step (Mac (joinCtx p x)))
progress (join p (x , Var x₁)) | inj₂ ()
progress (join p (x , App x₁ x₂)) | inj₂ ()
progress (join p (x , If x₁ Then x₂ Else x₃)) | inj₂ ()
progress (join p (x , Return x₁)) | inj₂ ()
progress (join p (x , x₁ >>= x₂)) | inj₂ ()
progress (join p (x , Throw x₁)) | inj₂ ()
progress (join p (x , Catch x₁ x₂)) | inj₂ ()
progress (join p (x , Mac x₁)) | inj₂ y = inj₁ (Step (Mac (join p)))
progress (join p (x , Macₓ x₁)) | inj₂ y = inj₁ (Step (Mac (joinEx p)))
progress (join p (x , label x₁ x₂)) | inj₂ ()
progress (join p (x , unlabel x₁ x₂)) | inj₂ ()
progress (join p (x , join x₁ x₂)) | inj₂ ()
progress (join p (x , ∙)) | inj₂ ()
progress (join p (c $ c₁)) | inj₂ ()
progress (join p (If c Then c₁ Else c₂)) | inj₂ ()
progress (join p (c >>= c₁)) | inj₂ ()
progress (join p (Catch c c₁)) | inj₂ ()
progress (join p (unlabel x c)) | inj₂ ()
progress (join p (join x c)) | inj₂ ()
progress (join p ∙) | inj₂ ()
progress (Catch c c₁) with progress c
progress (Catch c c₃) | inj₁ (Step s) = inj₁ (Step (Mac (CatchCtx s)))
progress (Catch (x , Var x₁) c₁) | inj₂ ()
progress (Catch (x , App x₁ x₂) c₁) | inj₂ ()
progress (Catch (x , If x₁ Then x₂ Else x₃) c₁) | inj₂ ()
progress (Catch (x , Return x₁) c₁) | inj₂ ()
progress (Catch (x , x₁ >>= x₂) c₁) | inj₂ ()
progress (Catch (x , Throw x₁) c₁) | inj₂ ()
progress (Catch (x , Catch x₁ x₂) c₁) | inj₂ ()
progress (Catch (x , Mac x₁) c₁) | inj₂ tt = inj₁ (Step (Mac Catch))
progress (Catch (x , Macₓ x₁) c₁) | inj₂ y = inj₁ (Step (Mac CatchEx))
progress (Catch (x , label x₁ x₂) c₁) | inj₂ ()
progress (Catch (x , unlabel x₁ x₂) c₁) | inj₂ ()
progress (Catch (Γ , join p t) h₁) | inj₂ ()
progress (Catch (x , ∙) c₁) | inj₂ ()
progress (Catch (c $ c₁) c₂) | inj₂ ()
progress (Catch (If c Then c₁ Else c₂) c₃) | inj₂ ()
progress (Catch (c >>= c₁) c₂) | inj₂ ()
progress (Catch (Catch c c₁) c₂) | inj₂ ()
progress (Catch (unlabel x c) c₁) | inj₂ ()
progress (Catch (join p c) h₁) | inj₂ ()
progress (Catch ∙ c₁) | inj₂ ()
progress (unlabel x c) with progress c
progress (unlabel x₁ c) | inj₁ (Step x) = inj₁ (Step (Mac (unlabelCtx x₁ x)))
progress (unlabel x₂ (x , Var x₁)) | inj₂ ()
progress (unlabel x₃ (x , App x₁ x₂)) | inj₂ ()
progress (unlabel x₄ (x , If x₁ Then x₂ Else x₃)) | inj₂ ()
progress (unlabel x₂ (x , Res x₁)) | inj₂ tt = inj₁ (Step (Mac (unlabel x₂)))
progress (unlabel x₂ (x , Resₓ x₁)) | inj₂ tt = inj₁ (Step (Mac (unlabelEx x₂)))
progress (unlabel x₂ (x , ∙)) | inj₂ ()
progress (unlabel x (c $ c₁)) | inj₂ ()
progress (unlabel x (If c Then c₁ Else c₂)) | inj₂ ()
progress (unlabel x ∙) | inj₂ ()
progress ∙ = inj₁ (Step Hole)

valueNotRedex : ∀ {τ} -> (c : CTerm τ) -> IsValue c -> NormalForm c
valueNotRedex (Γ , （）) isV (Step ())
valueNotRedex (Γ , True) isV (Step ())
valueNotRedex (Γ , False) isV (Step ())
valueNotRedex (Γ , App f x) () nf
valueNotRedex (Γ , Abs t) isV (Step ())
valueNotRedex (Γ , Var x) () nf
valueNotRedex (Γ , (If c Then t Else e)) () nf
valueNotRedex (Γ , Return t) () s
valueNotRedex (Γ , m >>= k) () s
valueNotRedex (Γ , ξ) isV (Step ())
valueNotRedex (Γ , Throw t) () nf
valueNotRedex (Γ , Catch m h) () nf
valueNotRedex (Γ , Mac t) tt (Step (Mac ()))
valueNotRedex (Γ , Macₓ t) isV (Step (Mac ()))
valueNotRedex (Γ , label x t) () nf
valueNotRedex (Γ , unlabel x t) () nf
valueNotRedex (Γ , Res t) isV (Step ())
valueNotRedex (Γ , Resₓ t) isV (Step ())
valueNotRedex (Γ , join p t) () s
valueNotRedex (Γ , ∙) () s
valueNotRedex (f $ x) () nf
valueNotRedex (If c Then t Else e) () nf
valueNotRedex (m >>= k) () s
valueNotRedex (Catch m h) () nf
valueNotRedex (unlabel x t) () nf
valueNotRedex (join p c) () nf
valueNotRedex ∙ () nf

determinism⟼ : ∀ {τ l} {c₁ c₂ c₃ : CTerm (Mac l τ)} -> c₁ ⟼ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃
determinismMixed  : ∀ {τ l} {c₁ c₂ c₃ : CTerm (Mac l τ)} -> c₁ ⇝ c₂ -> c₁ ⟼ c₃ -> c₂ ≡ c₃

determinismMixed (AppL s₁) ()
determinismMixed Beta ()
determinismMixed Lookup ()
determinismMixed Dist-$ ()
determinismMixed Dist-If ()
determinismMixed (IfCond s₁) ()
determinismMixed IfTrue ()
determinismMixed IfFalse ()
determinismMixed (Mac s₁) s₂ = determinism⟼ s₁ s₂
determinismMixed Dist-∙ ()
determinismMixed Hole ()

determinism⇝ : ∀ {τ} {c₁ c₂ c₃ : CTerm τ} -> c₁ ⇝ c₂ -> c₁ ⇝ c₃ -> c₂ ≡ c₃
determinism⇝ (Mac s₁) s₂ rewrite determinismMixed s₂ s₁ = refl
determinism⇝ s₁ (Mac s₂) rewrite determinismMixed s₁ s₂ = refl
determinism⇝ (AppL s₁) (AppL s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (AppL ()) Beta
determinism⇝ Beta (AppL ())
determinism⇝ Beta Beta = refl
determinism⇝ Lookup Lookup = refl
determinism⇝ Dist-$ Dist-$ = refl
determinism⇝ Dist-If Dist-If = refl
determinism⇝ (IfCond s₁) (IfCond s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⇝ (IfCond ()) IfTrue
determinism⇝ (IfCond ()) IfFalse
determinism⇝ IfTrue (IfCond ())
determinism⇝ IfTrue IfTrue = refl
determinism⇝ IfFalse (IfCond ())
determinism⇝ IfFalse IfFalse = refl
determinism⇝ Dist-∙ Dist-∙ = refl 
determinism⇝ Hole Hole = refl

determinism⟼ Return Return = refl
determinism⟼ Dist->>= Dist->>= = refl
determinism⟼ (BindCtx s₁) (BindCtx s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⟼ (BindCtx (Mac ())) Bind
determinism⟼ (BindCtx (Mac ())) BindEx
determinism⟼ Bind (BindCtx (Mac ()))
determinism⟼ Bind Bind = refl
determinism⟼ BindEx (BindCtx (Mac ()))
determinism⟼ BindEx BindEx = refl
determinism⟼ Throw Throw = refl
determinism⟼ Dist-Catch Dist-Catch = refl
determinism⟼ (CatchCtx s₁) (CatchCtx s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⟼ (CatchCtx (Mac ())) Catch
determinism⟼ (CatchCtx (Mac ())) CatchEx
determinism⟼ Catch (CatchCtx (Mac ()))
determinism⟼ Catch Catch = refl
determinism⟼ CatchEx (CatchCtx (Mac ()))
determinism⟼ CatchEx CatchEx = refl
determinism⟼ (label p) (label .p) = refl
determinism⟼ (Dist-unlabel p) (Dist-unlabel .p) = refl
determinism⟼ (unlabel p) (unlabel .p) = refl
determinism⟼ (unlabel p) (unlabelCtx .p ())
determinism⟼ (unlabelCtx p ()) (unlabel .p)
determinism⟼ (unlabelCtx p ()) (unlabelEx .p)
determinism⟼ (unlabelCtx p s₁) (unlabelCtx .p s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⟼ (unlabelEx p) (unlabelEx .p) = refl
determinism⟼ (unlabelEx p) (unlabelCtx .p ())
determinism⟼ (Dist-join p) (Dist-join .p) = refl
determinism⟼ (joinCtx p s₁) (joinCtx .p s₂) rewrite determinism⇝ s₁ s₂ = refl
determinism⟼ (joinCtx p (Mac ())) (join .p)
determinism⟼ (joinCtx p (Mac ())) (joinEx .p)
determinism⟼ (join p) (joinCtx .p (Mac ()))
determinism⟼ (join p) (join .p) = refl
determinism⟼ (joinEx p) (joinCtx .p (Mac ()))
determinism⟼ (joinEx p) (joinEx .p) = refl

preservation⇝ : ∀ {τ} {c₁ c₂ : CTerm τ} -> c₁ ⇝ c₂ -> τ ≡ τ
preservation⇝ _ = refl

preservation⟼ : ∀ {l : Label} {τ : Ty} {c₁ c₂ : CTerm (Mac l τ)} -> c₁ ⟼ c₂ -> _≡_ {_} {Ty} (Mac l τ) (Mac l τ)
preservation⟼ s = refl
