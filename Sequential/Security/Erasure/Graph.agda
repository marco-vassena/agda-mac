module Sequential.Security.Erasure.Graph where

open import Types
open import Sequential.Calculus
open import Sequential.Security.Erasure.Base
open import Data.Sum

-- TODO consider using Sensitive and Insensitive view directly in ε
data Sensitive (lₐ : Label) : Ty -> Set where
  Macᴴ : ∀ {h τ} -> ¬ (h ⊑ lₐ) -> Sensitive lₐ (Mac h τ)
  Resᴴ : ∀ {h τ} -> ¬ (h ⊑ lₐ) -> Sensitive lₐ (Res h τ)

data Insensitive (lₐ : Label) : Ty -> Set where
  Macᴸ : ∀ {τ l} {{p : l ⊑ lₐ}} -> Insensitive lₐ (Mac l τ)
  Resᴸ : ∀ {τ l} {{p : l ⊑ lₐ}} -> Insensitive lₐ (Res l τ)
  （） : Insensitive lₐ （）
  Bool : Insensitive lₐ Bool
  Nat : Insensitive lₐ Nat
  Exception : Insensitive lₐ Exception
  Id : (τ : Ty) ->  Insensitive lₐ (Id τ)
  _=>_ : (α β : Ty) -> Insensitive lₐ (α => β)

-- Sensitive and insensitive are mutually exclusive
sensOrInsens : ∀ {τ lₐ} -> Sensitive lₐ τ -> Insensitive lₐ τ -> ⊥
sensOrInsens (Macᴴ ¬p) (Macᴸ {{p}}) = ¬p p
sensOrInsens (Resᴴ ¬p) (Resᴸ {{p}}) = ¬p p

isSensitive? : (lₐ : Label) (τ : Ty) -> (Sensitive lₐ τ) ⊎ (Insensitive lₐ τ)
isSensitive? lₐ （） = inj₂ （）
isSensitive? lₐ Bool = inj₂ Bool
isSensitive? lₐ (τ => τ₁) = inj₂ (τ => τ₁)
isSensitive? lₐ (Mac l τ) with l ⊑? lₐ
isSensitive? lₐ (Mac l τ) | yes p = inj₂ Macᴸ
isSensitive? lₐ (Mac l τ) | no ¬p = inj₁ (Macᴴ ¬p)
isSensitive? lₐ (Res l τ) with l ⊑? lₐ
isSensitive? lₐ (Res l τ) | yes p = inj₂ Resᴸ
isSensitive? lₐ (Res l τ) | no ¬p = inj₁ (Resᴴ ¬p)
isSensitive? lₐ Exception = inj₂ Exception
isSensitive? lₐ Nat = inj₂ Nat
isSensitive? lₐ (Id τ) = inj₂ (Id τ) 

data IsVar {τ} {Δ} : Term Δ τ -> Set where
  isVar : (x : τ ∈ Δ) -> IsVar (Var x)

data ErasureMac∙ {Δ τ} {lₐ l : Label} (x : Sensitive lₐ (Mac l τ)) : (t tᵉ : Term Δ (Mac l τ)) -> Set where
  ∙ : ∀ {t : Term Δ (Mac l τ)} ->  ¬ (IsVar t) -> (¬p : ¬ (l ⊑ lₐ)) -> ErasureMac∙ x t ∙
  Var : (¬p : ¬ (l ⊑ lₐ)) -> (p : (Mac l τ) ∈ Δ) ->  ErasureMac∙ x (Var p) (Var p)


extensional-ErasureMac∙ : ∀ {l lₐ τ Δ} {x : Sensitive lₐ _} {t tᵉ : Term Δ (Mac l τ)} -> ErasureMac∙ x t tᵉ -> (y : Sensitive lₐ (Mac l τ)) -> ErasureMac∙ y t tᵉ
extensional-ErasureMac∙ (∙ x₁ ¬p) (Macᴴ x₂) = ∙ x₁ x₂
extensional-ErasureMac∙ (Var ¬p p) (Macᴴ x₁) = Var x₁ p
mutual

  data ErasureRes∙ {Δ} {lₐ l : Label} (x : ¬ (l ⊑ lₐ)) : ∀ {τ} -> (t tᵉ : Term Δ (Res l τ)) -> Set where
    Var : ∀ {τ} -> (p : (Res l τ) ∈ Δ) -> ErasureRes∙ x (Var p) (Var p)
    App : ∀ {α τ} {f fᵉ : Term Δ (α => Res l τ)} {t tᵉ : Term Δ α} -> ErasureIso {lₐ} (α => Res l τ) f fᵉ -> Erasure lₐ t tᵉ -> ErasureRes∙ x (App f t) (App fᵉ tᵉ)    
    Ite : ∀ {τ} {t₁ t₁ᵉ : Term Δ Bool} {t₂ t₂ᵉ t₃ t₃ᵉ : Term Δ (Res l τ)} ->
            ErasureIso {lₐ} Bool t₁ t₁ᵉ -> ErasureRes∙ x t₂ t₂ᵉ -> ErasureRes∙ x t₃ t₃ᵉ ->
            ErasureRes∙ x (If t₁ Then t₂ Else t₃) (If t₁ᵉ Then t₂ᵉ Else t₃ᵉ) 
    unId : ∀ {τ} {t tᵉ : Term Δ (Id (Res l τ))} -> ErasureIso {lₐ} (Id (Res l τ)) t tᵉ -> ErasureRes∙ x (unId t) (unId tᵉ)

    Starᴴ : ∀ {α β} {f fᵉ : Term Δ (Labeled l (α => β))} {t tᵉ : Term Δ (Labeled l α)} ->
                     ErasureRes∙ x f fᵉ ->
                     ErasureRes∙ x t tᵉ ->
                     ErasureRes∙ x (f <*> t) (fᵉ <*>∙ tᵉ) 
    Star∙ : ∀ {α β} {f fᵉ : Term Δ (Labeled l (α => β))} {t tᵉ : Term Δ (Labeled l α)} ->
                     ErasureRes∙ x f fᵉ ->
                     ErasureRes∙ x t tᵉ ->
                     ErasureRes∙ x (f <*>∙ t) (fᵉ <*>∙ tᵉ) 

    Res : ∀ {τ} {t : Term Δ τ} -> ErasureRes∙ x (Res t) (Res ∙)
    Resₓ : ∀ {τ} {t : Term Δ Exception} -> ErasureRes∙ x {τ = τ} (Resₓ t) (Res ∙)
    relabel : ∀ {τ l'} {t tᵉ : Term Δ (Labeled l' τ)} -> (p : l' ⊑ l) -> Erasure lₐ t tᵉ ->  ErasureRes∙ x (relabel p t) (relabel∙ p tᵉ)
    relabel∙ : ∀ {τ l'} {t tᵉ : Term Δ (Labeled l' τ)} -> (p : l' ⊑ l) -> Erasure lₐ t tᵉ ->  ErasureRes∙ x (relabel∙ p t) (relabel∙ p tᵉ)
    ∙ : ∀ {τ} -> ErasureRes∙ x (∙ {{Res l τ}}) ∙
    
  data ErasureIso {lₐ : Label} {Δ} : ∀ {τ} -> Insensitive lₐ τ -> Term Δ τ -> Term Δ τ -> Set where
    True : ErasureIso Bool True True
    False : ErasureIso Bool False False
    （） : ErasureIso （） （） （）
    Var : ∀ {τ} -> (p : τ ∈ Δ) -> (nonS : Insensitive lₐ τ) -> ErasureIso nonS (Var p) (Var p)
    Abs : ∀ {α β} {x xᵉ : Term (α ∷ Δ) β} -> Erasure lₐ x xᵉ -> ErasureIso (α => β) (Abs x) (Abs xᵉ)

    App : ∀ {α β} {f fᵉ : Term Δ (α => β)} {x xᵉ : Term Δ α} -> (nonS : Insensitive lₐ β) ->
            ErasureIso {lₐ} (α => β) f fᵉ -> Erasure lₐ x xᵉ -> ErasureIso nonS (App f x) (App fᵉ xᵉ)

    Ite : ∀ {τ} {t₁ t₁ᵉ : Term Δ Bool} {t₂ t₂ᵉ t₃ t₃ᵉ : Term Δ τ} -> (nonS : Insensitive lₐ τ) ->
            ErasureIso {lₐ} Bool t₁ t₁ᵉ -> ErasureIso nonS t₂ t₂ᵉ -> ErasureIso nonS t₃ t₃ᵉ ->
            ErasureIso nonS (If t₁ Then t₂ Else t₃) (If t₁ᵉ Then t₂ᵉ Else t₃ᵉ) 

    Id : ∀ {τ} {t tᵉ : Term Δ τ} -> Erasure lₐ t tᵉ -> ErasureIso (Id τ) (Id t) (Id tᵉ)

    unId : ∀ {τ} {t tᵉ : Term Δ (Id τ)} -> (nonS : Insensitive lₐ τ) -> ErasureIso {lₐ} (Id τ) t tᵉ -> ErasureIso nonS (unId t) (unId tᵉ)

    _<*>ᴵ_ : ∀ {α β} {f fᵉ : Term Δ (Id (α => β))} {x xᵉ : Term Δ (Id α)} -> ErasureIso {lₐ} (Id (α => β)) f fᵉ -> ErasureIso {lₐ} (Id α) x xᵉ ->
                  ErasureIso (Id β) (f <*>ᴵ x) (fᵉ <*>ᴵ xᵉ)

    Star : ∀ {α β l} {f fᵉ : Term Δ (Labeled l (α => β))} {x xᵉ : Term Δ (Labeled l α)} -> (p : l ⊑ lₐ) ->
                     ErasureIso {lₐ} Resᴸ f fᵉ ->
                     ErasureIso {lₐ} Resᴸ x xᵉ ->
                     ErasureIso Resᴸ (f <*> x) (fᵉ <*> xᵉ) 

    Star∙ : ∀ {α β l} {f fᵉ : Term Δ (Labeled l (α => β))} {x xᵉ : Term Δ (Labeled l α)} -> (p : l ⊑ lₐ) ->
                     ErasureIso {lₐ} Resᴸ f fᵉ ->
                     ErasureIso {lₐ} Resᴸ x xᵉ ->
                     ErasureIso Resᴸ (f <*>∙ x) (fᵉ <*>∙ xᵉ) 

    Res : ∀ {τ l} {t tᵉ : Term Δ τ} -> (p : l ⊑ lₐ) -> Erasure lₐ t tᵉ -> ErasureIso Resᴸ (Res t) (Res tᵉ)
    Resₓ : ∀ {τ l} {t tᵉ : Term Δ Exception} -> (p : l ⊑ lₐ) -> ErasureIso {lₐ = lₐ} Exception t tᵉ -> ErasureIso (Resᴸ) (Resₓ {α = τ} t) (Resₓ tᵉ)

    relabel : ∀ {τ l h} {t tᵉ : Term Δ (Labeled l τ)} -> (p₁ : l ⊑ h) (p₂ : h ⊑ lₐ) -> Erasure lₐ t tᵉ ->
                        ErasureIso Resᴸ (relabel p₁ t) (relabel p₁ tᵉ)
    relabel∙ : ∀ {τ l h} {t tᵉ : Term Δ (Labeled l τ)} -> (p₁ : l ⊑ h) (p₂ : h ⊑ lₐ) -> Erasure lₐ t tᵉ ->
                        ErasureIso Resᴸ (relabel∙ p₁ t) (relabel∙ p₁ tᵉ)

    Return : ∀ {τ l} {t tᵉ : Term Δ τ} -> (p : l ⊑ lₐ) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (Return t) (Return tᵉ)
    Bind : ∀ {α β l} {m mᵉ : Term Δ (Mac l α)} {k kᵉ : Term Δ (α => Mac l β)} -> (p : l ⊑ lₐ) ->
                        ErasureIso Macᴸ m mᵉ -> ErasureIso {lₐ} (α => Mac l β) k kᵉ ->  ErasureIso Macᴸ (m >>= k) (mᵉ >>= kᵉ)

    Throw : ∀ {τ l} {t tᵉ : Term Δ Exception} -> (p : l ⊑ lₐ) -> ErasureIso {lₐ} Exception t tᵉ -> ErasureIso Macᴸ (Throw {{α = τ}} t) (Throw tᵉ)

    Catch : ∀ {τ l} {t tᵉ : Term Δ (Mac l τ)} {h hᵉ : Term Δ (Exception => (Mac l τ))} -> (p : l ⊑ lₐ) ->
                       ErasureIso Macᴸ t tᵉ -> ErasureIso {lₐ} (Exception => Mac l τ) h hᵉ -> ErasureIso Macᴸ (Catch t h) (Catch tᵉ hᵉ)

    Mac : ∀ {τ l} {t tᵉ : Term Δ τ} -> (p : l ⊑ lₐ) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (Mac t) (Mac tᵉ)
    Macₓ : ∀ {τ l} {t tᵉ : Term Δ Exception} -> (p : l ⊑ lₐ) -> ErasureIso {lₐ} Exception t tᵉ -> ErasureIso Macᴸ (Macₓ {α = τ} t) (Macₓ tᵉ)

    labelᴸ : ∀ {τ l h} {t tᵉ : Term Δ τ} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) (p₃ : h ⊑ lₐ) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (label p₂ t) (label p₂ tᵉ)
    labelᴴ : ∀ {τ l h} {t tᵉ : Term Δ τ} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) (p₃ : ¬ (h ⊑ lₐ)) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (label p₂ t) (label∙ p₂ tᵉ)
    label∙ : ∀ {τ l h} {t tᵉ : Term Δ τ} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (label∙ p₂ t) (label∙ p₂ tᵉ)
    
    unlabel : ∀ {τ l h} {t tᵉ : Term Δ (Labeled l τ)} -> (p₁ : h ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (unlabel p₂ t) (unlabel p₂ tᵉ)

    joinᴸ : ∀ {τ l h} {t tᵉ : Term Δ (Mac h τ)} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) (p₃ : h ⊑ lₐ) -> ErasureIso Macᴸ t tᵉ -> ErasureIso Macᴸ (join p₂ t) (join p₂ tᵉ)
    joinᴴ : ∀ {τ l h} {t tᵉ : Term Δ (Mac h τ)} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) (p₃ : ¬ (h ⊑ lₐ)) -> ErasureMac∙ (Macᴴ p₃) t tᵉ -> ErasureIso Macᴸ (join p₂ t) (join∙ p₂ tᵉ)
    join∙ : ∀ {τ l h} {t tᵉ : Term Δ (Mac h τ)} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (join∙ p₂ t) (join∙ p₂ tᵉ)

    read : ∀ {τ l h} {t tᵉ : Term Δ (Ref l τ)} -> (p₁ : h ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (read {α = τ} p₂ t) (read p₂ tᵉ)
    write : ∀ {τ l h} {r rᵉ : Term Δ (Ref h τ)} {t tᵉ : Term Δ τ} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) ->
                   Erasure lₐ r rᵉ -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (write p₂ r t) (write p₂ rᵉ tᵉ)
    new : ∀ {τ l h} {t tᵉ : Term Δ τ} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (new p₂ t) (new p₂ tᵉ)
    fork : ∀ {l h} {t tᵉ : Term Δ (Mac h _)} ->  (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (fork p₂ t) (fork p₂ tᵉ)
    
    newMVar : ∀ {τ l h} -> (p₁ : l ⊑ lₐ) (p₂ : l ⊑ h) -> ErasureIso Macᴸ (newMVar {α = τ} p₂) (newMVar {α = τ} p₂)
    takeMVar : ∀ {τ l} {t tᵉ : Term Δ (MVar l τ)} -> (p : l ⊑ lₐ) -> ErasureIso Resᴸ t tᵉ -> ErasureIso Macᴸ (takeMVar {α = τ} t) (takeMVar tᵉ)
    putMVar : ∀ {τ l} {r rᵉ : Term Δ (MVar l τ)} {t tᵉ : Term Δ τ} -> (p : l ⊑ lₐ) ->
                ErasureIso Resᴸ r rᵉ -> Erasure lₐ t tᵉ -> ErasureIso Macᴸ (putMVar r t) (putMVar rᵉ tᵉ)
    
    ξ : ErasureIso Exception ξ ξ
    zero : ErasureIso Nat zero zero
    suc : ∀ {n nᵉ} -> ErasureIso {lₐ} Nat n nᵉ -> ErasureIso Nat (suc n) (suc nᵉ)
    ∙ : ∀ {τ} -> (nonS : Insensitive lₐ τ) -> ErasureIso nonS ∙ ∙

  data Erasure {Δ} (lₐ : Label) : ∀ {τ} -> (t tᵉ : Term Δ τ) -> Set where
    Iso : ∀ {τ} {t tᵉ : Term Δ τ} -> (nonS : Insensitive lₐ τ) -> ErasureIso nonS t tᵉ -> Erasure lₐ t tᵉ
    Mac∙ : ∀ {τ h} {t tᵉ : Term Δ (Mac h τ)} -> (¬p : ¬ (h ⊑ lₐ)) -> ErasureMac∙ (Macᴴ ¬p) t tᵉ -> Erasure lₐ t tᵉ
    Res∙ : ∀ {τ h} {t tᵉ : Term Δ (Res h τ)} -> (¬p : ¬ (h ⊑ lₐ)) -> ErasureRes∙ ¬p t tᵉ -> Erasure lₐ t tᵉ
    
open import Relation.Binary.PropositionalEquality

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C -> D) {x y z u v w} → x ≡ y → u ≡ v → z ≡ w → f x u z ≡ f y v w
cong₃ f refl refl refl = refl

Erasure-ε : ∀ {lₐ τ Δ} {t tᵉ : Term Δ τ} -> Erasure lₐ t tᵉ -> ε lₐ t ≡ tᵉ
ErasureIso-ε : ∀ {lₐ τ Δ} {t tᵉ : Term Δ τ} {nonS : Insensitive lₐ τ} -> ErasureIso nonS t tᵉ -> ε lₐ t ≡ tᵉ

ErasureIso-ε-Mac-no : ∀ {lₐ h τ Δ} {t tᵉ : Term Δ (Mac h τ)} -> (¬p : ¬ (h ⊑ lₐ)) -> ErasureMac∙ (Macᴴ ¬p) t tᵉ -> ε-Mac lₐ (no ¬p) t ≡ tᵉ
ErasureIso-ε-Mac-no {t = unId t} ¬p (∙ x ¬p₁) = refl
ErasureIso-ε-Mac-no {t = Var x} ¬p (∙ x₁ ¬p₁) = ⊥-elim (x₁ (isVar x))
ErasureIso-ε-Mac-no {t = Var .x} ¬p (Var ¬p₁ x) = refl
ErasureIso-ε-Mac-no {t = App t t₁} ¬p (∙ x ¬p₁) = refl
ErasureIso-ε-Mac-no {t = If t Then t₁ Else t₂} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = Return t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = t >>= t₁} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = Throw t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = Catch t t₁} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = Mac t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = Macₓ t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = label x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = label∙ x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = unlabel x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = join x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = join∙ x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = read x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = write x t t₁} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = new x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = fork x t} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = newMVar x} ¬p (∙ _ _) = refl
ErasureIso-ε-Mac-no {t = takeMVar t} ¬p (∙ x ¬p₁) = refl
ErasureIso-ε-Mac-no {t = putMVar t t₁} ¬p (∙ x ¬p₁) = refl
ErasureIso-ε-Mac-no {t = ∙} ¬p (∙ x ¬p₁) = refl

ErasureIso-ε-Mac-yes : ∀ {lₐ l τ Δ} {t tᵉ : Term Δ (Mac l τ)} {nonS : Insensitive lₐ (Mac l τ)} -> (p : l ⊑ lₐ) -> ErasureIso nonS t tᵉ -> ε-Mac lₐ (yes p) t ≡ tᵉ
ErasureIso-ε-Mac-yes p (Var p₁ nonS) = refl
ErasureIso-ε-Mac-yes p (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂)
ErasureIso-ε-Mac-yes p (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε-Mac-yes p x₁) (ErasureIso-ε-Mac-yes p x₂)
ErasureIso-ε-Mac-yes p (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε-Mac-yes p (Return p₁ x) = cong Return (Erasure-ε x)
ErasureIso-ε-Mac-yes p (Bind p₁ x x₁) = cong₂ _>>=_ (ErasureIso-ε-Mac-yes p x) (ErasureIso-ε x₁)
ErasureIso-ε-Mac-yes p (Throw p₁ x) = cong Throw (ErasureIso-ε x)
ErasureIso-ε-Mac-yes p (Catch p₁ x x₁) = cong₂ Catch (ErasureIso-ε-Mac-yes p x) (ErasureIso-ε x₁)
ErasureIso-ε-Mac-yes p (Mac p₁ x) = cong Mac (Erasure-ε x)
ErasureIso-ε-Mac-yes p (Macₓ p₁ x) = cong Macₓ (ErasureIso-ε x)
ErasureIso-ε-Mac-yes {lₐ = lₐ} p (labelᴸ {h = h} p₁ p₂ p₃ x) with h ⊑? lₐ
ErasureIso-ε-Mac-yes p₁ (labelᴸ p₂ p₃ p₄ x) | yes p = cong (label p₃) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (labelᴸ p₁ p₂ p₃ x) | no ¬p = ⊥-elim (¬p p₃)
ErasureIso-ε-Mac-yes {lₐ = lₐ} p (labelᴴ {h = h} p₁ p₂ p₃ x) with h ⊑? lₐ
ErasureIso-ε-Mac-yes p₁ (labelᴴ p₂ p₃ p₄ x) | yes p = ⊥-elim (p₄ p)
ErasureIso-ε-Mac-yes p (labelᴴ p₁ p₂ p₃ x) | no ¬p = cong (label∙ p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (label∙ p₁ p₂ x) = cong (label∙ p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (unlabel p₁ p₂ x) = cong (unlabel p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes {lₐ} p (joinᴸ {h = h} p₁ p₂ p₃ x) with h ⊑? lₐ
ErasureIso-ε-Mac-yes p₁ (joinᴸ p₂ p₃ p₄ x) | yes p = cong (join p₃) (ErasureIso-ε-Mac-yes p x)
ErasureIso-ε-Mac-yes p (joinᴸ p₁ p₂ p₃ x) | no ¬p = ⊥-elim (¬p p₃)
ErasureIso-ε-Mac-yes {lₐ} p (joinᴴ {h = h} p₁ p₂ p₃ x) with h ⊑? lₐ
ErasureIso-ε-Mac-yes p₁ (joinᴴ p₂ p₃ p₄ x) | yes p = ⊥-elim (p₄ p)
ErasureIso-ε-Mac-yes p (joinᴴ p₁ p₂ ¬p' x) | no ¬p = cong (join∙ p₂) (ErasureIso-ε-Mac-no ¬p (extensional-ErasureMac∙ x (Macᴴ ¬p)))
ErasureIso-ε-Mac-yes p (join∙ p₁ p₂ x) = cong (join∙ p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (read p₁ p₂ x) = cong (read p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (write p₁ p₂ x x₁) = cong₂ (write p₂) (Erasure-ε x) (Erasure-ε x₁)
ErasureIso-ε-Mac-yes p (new p₁ p₂ x) = cong (new p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (fork p₁ p₂ x) = cong (fork p₂) (Erasure-ε x)
ErasureIso-ε-Mac-yes p (newMVar p₁ p₂) = refl
ErasureIso-ε-Mac-yes p (takeMVar p₁ x) = cong takeMVar (ErasureIso-ε x)
ErasureIso-ε-Mac-yes p (putMVar p₁ x x₁) = cong₂ putMVar (ErasureIso-ε x) (Erasure-ε x₁)
ErasureIso-ε-Mac-yes p (∙ nonS) = refl

ErasureIso-ε {lₐ} {Mac l τ} x with l ⊑? lₐ
ErasureIso-ε {lₐ} {Mac l τ} x | yes p = ErasureIso-ε-Mac-yes p x
ErasureIso-ε {lₐ} {Mac l τ} {nonS = nonS} x | no ¬p = ⊥-elim (sensOrInsens (Macᴴ ¬p) nonS)
ErasureIso-ε True = refl
ErasureIso-ε False = refl
ErasureIso-ε （） = refl
ErasureIso-ε {lₐ} (Var p nonS) rewrite εVar≡Var lₐ p = refl
ErasureIso-ε (Abs x) rewrite Erasure-ε x = refl
ErasureIso-ε {τ = （）} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = Bool} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = τ => τ₁} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = Res x τ} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = Exception} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = Nat} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = Id τ} (App nonS x₁ x₂) = cong₂ App (ErasureIso-ε x₁) (Erasure-ε x₂) 
ErasureIso-ε {τ = （）} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = Bool} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = τ => τ₁} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = Res _ τ} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = Exception} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = Nat} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {τ = Id τ} (Ite nonS x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε (Id x) rewrite Erasure-ε x = refl
ErasureIso-ε {τ = （）} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = Bool} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = τ => τ₁} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = Res _ τ} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = Exception} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = Nat} (unId nonS x) = cong unId (ErasureIso-ε x)
ErasureIso-ε {τ = Id τ} (unId nonS x) = cong unId (ErasureIso-ε x) 
ErasureIso-ε (x₁ <*>ᴵ x₂) = cong₂ _<*>ᴵ_ (ErasureIso-ε x₁) (ErasureIso-ε x₂)
ErasureIso-ε {lₐ} {Res l (Id τ)} (Star p x₁ x₂) with l ⊑? lₐ
ErasureIso-ε {lₐ} {Res l (Id τ)} (Star p₁ x₁ x₂) | yes p rewrite ErasureIso-ε x₁ | ErasureIso-ε x₂ = refl
ErasureIso-ε {lₐ} {Res l (Id τ)} (Star p x₁ x₂) | no ¬p = ⊥-elim (¬p p)
ErasureIso-ε (Star∙ p x₁ x₂) rewrite ErasureIso-ε x₁ | ErasureIso-ε x₂ = refl
ErasureIso-ε {lₐ} {Res l τ} (Res p x) with l ⊑? lₐ
ErasureIso-ε {lₐ} {Res l τ} (Res p₁ x) | yes p rewrite Erasure-ε x = refl
ErasureIso-ε {lₐ} {Res l τ} (Res p x) | no ¬p = ⊥-elim (¬p p)
ErasureIso-ε {lₐ} {Res l τ} (Resₓ p x)  with l ⊑? lₐ
ErasureIso-ε {lₐ} {Res l τ} (Resₓ p₁ x) | yes p = cong Resₓ (ErasureIso-ε x)
ErasureIso-ε {lₐ} {Res l τ} (Resₓ p x) | no ¬p = ⊥-elim (¬p p)
ErasureIso-ε {lₐ} {Res h (Id τ)} (relabel p₁ p₂ x) with h ⊑? lₐ
ErasureIso-ε {lₐ} {Res h (Id τ)} (relabel p₁ p₂ x) | yes p = cong (relabel p₁) (Erasure-ε x)
ErasureIso-ε {lₐ} {Res h (Id τ)} (relabel p₁ p₂ x) | no ¬p = ⊥-elim (¬p p₂)
ErasureIso-ε (relabel∙ p₁ p₂ x) = cong (relabel∙ p₁) (Erasure-ε x)
ErasureIso-ε ξ = refl
ErasureIso-ε zero = refl
ErasureIso-ε (suc x) = cong suc (ErasureIso-ε x)
ErasureIso-ε {lₐ} {τ} {Δ} (∙ nonS) rewrite ε∙≡∙ {τ} {Δ} lₐ = refl

ErasureRes∙-ε : ∀ {l lₐ Δ τ} {t tᵉ : Term Δ (Res l τ)} -> (¬p : ¬ (l ⊑ lₐ)) -> ErasureRes∙ ¬p t tᵉ -> ε lₐ t ≡ tᵉ
ErasureRes∙-ε ¬p (Var p) = refl
ErasureRes∙-ε ¬p (App x x₁) = cong₂ App (ErasureIso-ε x) (Erasure-ε x₁)
ErasureRes∙-ε ¬p (Ite x x₁ x₂) = cong₃ If_Then_Else_ (ErasureIso-ε x) (ErasureRes∙-ε ¬p x₁) (ErasureRes∙-ε ¬p x₂)
ErasureRes∙-ε ¬p (unId x) = cong unId (ErasureIso-ε x)
ErasureRes∙-ε {l} {lₐ} ¬p (Starᴴ x x₁) with l ⊑? lₐ
ErasureRes∙-ε ¬p (Starᴴ x x₁) | yes p = ⊥-elim (¬p p)
ErasureRes∙-ε ¬p₁ (Starᴴ x x₁) | no ¬p = cong₂ _<*>∙_ (ErasureRes∙-ε ¬p₁ x) (ErasureRes∙-ε ¬p₁ x₁)
ErasureRes∙-ε ¬p (Star∙ x x₁) = cong₂ _<*>∙_ (ErasureRes∙-ε ¬p x) (ErasureRes∙-ε ¬p x₁)
ErasureRes∙-ε {l} {lₐ} ¬p Res with l ⊑? lₐ
ErasureRes∙-ε ¬p Res | yes p = ⊥-elim (¬p p)
ErasureRes∙-ε ¬p₁ Res | no ¬p = refl
ErasureRes∙-ε {l} {lₐ} ¬p Resₓ with l ⊑? lₐ
ErasureRes∙-ε ¬p Resₓ | yes p = ⊥-elim (¬p p)
ErasureRes∙-ε ¬p₁ Resₓ | no ¬p = refl
ErasureRes∙-ε {l} {lₐ} ¬p (relabel p x) with l ⊑? lₐ
ErasureRes∙-ε ¬p (relabel p₁ x) | yes p = ⊥-elim (¬p p)
ErasureRes∙-ε ¬p₁ (relabel p x) | no ¬p = cong (relabel∙ p) (Erasure-ε x)
ErasureRes∙-ε ¬p (relabel∙ p x) = cong (relabel∙ p) (Erasure-ε x)
ErasureRes∙-ε ¬p ∙ = refl

Erasure-ε (Iso nonS x) = ErasureIso-ε x
Erasure-ε {lₐ} (Mac∙ {h = h} ¬p x) with h ⊑? lₐ
Erasure-ε (Mac∙ ¬p x) | yes p = ⊥-elim (¬p p)
Erasure-ε (Mac∙ ¬p₁ x) | no ¬p = ErasureIso-ε-Mac-no ¬p (extensional-ErasureMac∙ x (Macᴴ ¬p))
Erasure-ε (Res∙ ¬p x) = ErasureRes∙-ε ¬p x

--------------------------------------------------------------------------------
-- Sufficient

ε-Erasure : ∀ {τ lₐ Δ} (t : Term Δ τ) -> Erasure lₐ t (ε lₐ t)
ε-ErasureIso : ∀ {τ lₐ Δ} (nonS : Insensitive lₐ τ) (t : Term Δ τ) -> ErasureIso nonS t (ε lₐ t)

ε-Mac-no-ErasureIso : ∀ {τ h lₐ Δ} (¬p : ¬ (h ⊑ lₐ)) (t : Term Δ (Mac h τ)) -> ErasureMac∙ (Macᴴ ¬p) t (ε-Mac lₐ (no ¬p) t)
ε-Mac-no-ErasureIso ¬p (unId t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Var x) = Var ¬p x
ε-Mac-no-ErasureIso ¬p (App t t₁) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (If t Then t₁ Else t₂) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Return t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (t >>= t₁) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Throw t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Catch t t₁) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Mac t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (Macₓ t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (label x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (label∙ x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (unlabel x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (join x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (join∙ x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (read x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (write x t t₁) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (new x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (fork x t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (newMVar x) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (takeMVar t) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p (putMVar t t₁) = ∙ (λ ()) ¬p
ε-Mac-no-ErasureIso ¬p ∙ = ∙ (λ ()) ¬p

ε-Mac-yes-ErasureIso : ∀ {τ l lₐ Δ} (nonS : Insensitive lₐ (Mac l τ)) (p : l ⊑ lₐ) (t : Term Δ (Mac l τ)) -> ErasureIso nonS t (ε-Mac lₐ (yes p) t)
ε-Mac-yes-ErasureIso nonS p (unId t) = unId nonS (ε-ErasureIso (Id (Mac _ _)) t)
ε-Mac-yes-ErasureIso nonS p (Var x) = Var x nonS
ε-Mac-yes-ErasureIso nonS p (App t t₁) = App nonS (ε-ErasureIso (_ => Mac _ _) t) (ε-Erasure t₁)
ε-Mac-yes-ErasureIso nonS p (If t Then t₁ Else t₂) = Ite nonS (ε-ErasureIso Bool t) (ε-Mac-yes-ErasureIso nonS p t₁) (ε-Mac-yes-ErasureIso nonS p t₂)
ε-Mac-yes-ErasureIso Macᴸ p₁ (Return t) = Return _ (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (t >>= t₁) = Bind _ (ε-Mac-yes-ErasureIso Macᴸ p₁ t) (ε-ErasureIso (_ => Mac _ _) t₁)
ε-Mac-yes-ErasureIso Macᴸ p₁ (Throw t) = Throw _ (ε-ErasureIso Exception t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (Catch t t₁) = Catch _ (ε-Mac-yes-ErasureIso Macᴸ p₁ t) (ε-ErasureIso (Exception => Mac _ _) t₁)
ε-Mac-yes-ErasureIso Macᴸ p₁ (Mac t) = Mac _ (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (Macₓ t) = Macₓ _ (ε-ErasureIso Exception t)
ε-Mac-yes-ErasureIso {lₐ = lₐ} Macᴸ p₁ (label {h = h} x t) with h ⊑? lₐ
ε-Mac-yes-ErasureIso Macᴸ p₂ (label x t) | yes p = labelᴸ _ x p (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (label x t) | no ¬p = labelᴴ _ x ¬p (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (label∙ x t) = label∙ _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (unlabel x t) = unlabel _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso {lₐ = lₐ} Macᴸ p (join {h = h} x t) with h ⊑? lₐ
ε-Mac-yes-ErasureIso Macᴸ p₂ (join x t) | yes p = joinᴸ _ x p (ε-Mac-yes-ErasureIso Macᴸ p t)
ε-Mac-yes-ErasureIso Macᴸ p₁ (join x t) | no ¬p = joinᴴ _ x ¬p (ε-Mac-no-ErasureIso ¬p t)
ε-Mac-yes-ErasureIso Macᴸ p (join∙ x t) = join∙ _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p (read x t) = read _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p (write x t t₁) = write _ x (ε-Erasure t) (ε-Erasure t₁)
ε-Mac-yes-ErasureIso Macᴸ p (new x t) = new _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p (fork x t) = fork _ x (ε-Erasure t)
ε-Mac-yes-ErasureIso Macᴸ p (newMVar x) = newMVar _ x
ε-Mac-yes-ErasureIso Macᴸ p (takeMVar t) = takeMVar _ (ε-ErasureIso Resᴸ t)
ε-Mac-yes-ErasureIso Macᴸ p (putMVar t t₁) = putMVar _ (ε-ErasureIso Resᴸ t) (ε-Erasure t₁)
ε-Mac-yes-ErasureIso Macᴸ p ∙ = ∙ Macᴸ

ε-ErasureIso {Mac l τ} {lₐ} Macᴸ t with l ⊑? lₐ
ε-ErasureIso {Mac l τ} Macᴸ t | yes p = ε-Mac-yes-ErasureIso Macᴸ p t
ε-ErasureIso {Mac l τ} Macᴸ t | no ¬p = ⊥-elim (sensOrInsens (Macᴴ {τ = τ} ¬p) Macᴸ)
ε-ErasureIso Resᴸ (unId t) = unId Resᴸ (ε-ErasureIso (Id (Res _ _)) t)
ε-ErasureIso Resᴸ (Var x) = Var x Resᴸ
ε-ErasureIso Resᴸ (App t t₁) = App Resᴸ (ε-ErasureIso (_ => _) t) (ε-Erasure t₁)
ε-ErasureIso Resᴸ (If t Then t₁ Else t₂) = Ite Resᴸ (ε-ErasureIso Bool t) (ε-ErasureIso Resᴸ t₁) (ε-ErasureIso Resᴸ t₂)
ε-ErasureIso {Res l τ} {lₐ} Resᴸ (Res t) with l ⊑? lₐ
ε-ErasureIso {Res l τ} Resᴸ (Res t) | yes p = Res _ (ε-Erasure t)
ε-ErasureIso {Res l τ} Resᴸ (Res t) | no ¬p = ⊥-elim (sensOrInsens (Resᴴ {τ = τ} ¬p) Resᴸ)
ε-ErasureIso {Res l τ} {lₐ} Resᴸ (Resₓ t) with l ⊑? lₐ
ε-ErasureIso {Res l τ} Resᴸ (Resₓ t) | yes p = Resₓ _ (ε-ErasureIso Exception t)
ε-ErasureIso {Res l τ} Resᴸ (Resₓ t) | no ¬p = ⊥-elim (sensOrInsens (Resᴴ {τ = τ} ¬p) Resᴸ)
ε-ErasureIso {Res l (Id τ)} {lₐ} Resᴸ (relabel x t) with l ⊑? lₐ
ε-ErasureIso {Res l (Id τ)} Resᴸ (relabel x t) | yes p = relabel x _ (ε-Erasure t)
ε-ErasureIso {Res l (Id τ)} Resᴸ (relabel x t) | no ¬p = ⊥-elim (sensOrInsens (Resᴴ {τ = τ} ¬p) Resᴸ)
ε-ErasureIso {Res l (Id τ)} {lₐ} Resᴸ (relabel∙ x t) = relabel∙ x _ (ε-Erasure t)
ε-ErasureIso {Res l (Id τ)} {lₐ} Resᴸ (t <*> t₁) with l ⊑? lₐ
ε-ErasureIso {Res l (Id τ)} Resᴸ (t <*> t₁) | yes p = Star _ (ε-ErasureIso Resᴸ t) (ε-ErasureIso Resᴸ t₁)
ε-ErasureIso {Res l (Id τ)} Resᴸ (t <*> t₁) | no ¬p = ⊥-elim (sensOrInsens (Resᴴ {τ = τ} ¬p) Resᴸ)
ε-ErasureIso Resᴸ (t <*>∙ t₁) = Star∙ _ (ε-ErasureIso Resᴸ t) (ε-ErasureIso Resᴸ t₁)
ε-ErasureIso Resᴸ ∙ = ∙ Resᴸ
ε-ErasureIso （） （） = （）
ε-ErasureIso （） (unId t) = unId （） (ε-ErasureIso (Id （）) t)
ε-ErasureIso （） (Var x) = Var x （）
ε-ErasureIso （） (App t t₁) = App （） (ε-ErasureIso (_ => （）) t) (ε-Erasure t₁)
ε-ErasureIso （） (If t Then t₁ Else t₂) = Ite （） (ε-ErasureIso Bool t) (ε-ErasureIso （） t₁) (ε-ErasureIso （） t₂)
ε-ErasureIso （） ∙ = ∙ （）
ε-ErasureIso Bool True = True
ε-ErasureIso Bool False = False
ε-ErasureIso Bool (unId t) = unId Bool (ε-ErasureIso (Id Bool) t)
ε-ErasureIso Bool (Var x) = Var x Bool
ε-ErasureIso Bool (App t t₁) = App Bool (ε-ErasureIso (_ => Bool) t) (ε-Erasure t₁)
ε-ErasureIso Bool (If t Then t₁ Else t₂) = Ite Bool (ε-ErasureIso Bool t) (ε-ErasureIso Bool t₁) (ε-ErasureIso Bool t₂)
ε-ErasureIso Bool ∙ = ∙ Bool
ε-ErasureIso Nat (unId t) = unId Nat (ε-ErasureIso (Id Nat) t)
ε-ErasureIso Nat (Var x) = Var x Nat
ε-ErasureIso Nat (App t t₁) = App Nat (ε-ErasureIso (_ => Nat) t) (ε-Erasure t₁)
ε-ErasureIso Nat (If t Then t₁ Else t₂) = Ite Nat (ε-ErasureIso Bool t) (ε-ErasureIso Nat t₁) (ε-ErasureIso Nat t₂)
ε-ErasureIso Nat zero = zero
ε-ErasureIso Nat (suc t) = suc (ε-ErasureIso Nat t)
ε-ErasureIso Nat ∙ = ∙ Nat
ε-ErasureIso Exception (unId t) = unId Exception (ε-ErasureIso (Id Exception) t)
ε-ErasureIso Exception (Var x) = Var x Exception
ε-ErasureIso Exception (App t t₁) = App Exception (ε-ErasureIso (_ => Exception) t) (ε-Erasure t₁)
ε-ErasureIso Exception (If t Then t₁ Else t₂) = Ite Exception (ε-ErasureIso Bool t) (ε-ErasureIso Exception t₁) (ε-ErasureIso Exception t₂)
ε-ErasureIso Exception ξ = ξ
ε-ErasureIso Exception ∙ = ∙ Exception
ε-ErasureIso (Id τ) (Id t) = Id (ε-Erasure t)
ε-ErasureIso (Id τ) (unId t) = unId (Id τ) (ε-ErasureIso (Id (Id τ)) t)
ε-ErasureIso (Id β) (t <*>ᴵ t₁) = (ε-ErasureIso (Id (_ => β)) t) <*>ᴵ ε-ErasureIso (Id _) t₁
ε-ErasureIso (Id τ) (Var x) = Var x (Id τ)
ε-ErasureIso (Id τ) (App t t₁) = App (Id τ) (ε-ErasureIso (_ => Id τ) t) (ε-Erasure t₁)
ε-ErasureIso (Id τ) (If t Then t₁ Else t₂) = Ite (Id τ) (ε-ErasureIso Bool t) (ε-ErasureIso (Id τ) t₁) (ε-ErasureIso (Id τ) t₂)
ε-ErasureIso (Id τ) ∙ = ∙ (Id τ)
ε-ErasureIso (α => β) (unId t) = unId (α => β) (ε-ErasureIso (Id (α => β)) t)
ε-ErasureIso (α => β) (Var x) = Var x (α => β)
ε-ErasureIso (α => β) (Abs t) = Abs (ε-Erasure t)
ε-ErasureIso (α => β) (App t t₁) = App (α => β) (ε-ErasureIso (_ => (α => β)) t) (ε-Erasure t₁)
ε-ErasureIso (α => β) (If t Then t₁ Else t₂) = Ite (α => β) (ε-ErasureIso Bool t) (ε-ErasureIso (α => β) t₁) (ε-ErasureIso (α => β) t₂)
ε-ErasureIso (α => β) ∙ = ∙ (α => β)

ε-Res-ErasureRes∙ : ∀ {h lₐ τ Δ} (¬p : ¬ (h ⊑ lₐ)) (t : Term Δ (Res h τ)) -> ErasureRes∙ ¬p t (ε lₐ  t)
ε-Res-ErasureRes∙ ¬p (unId t) = unId (ε-ErasureIso (Id (Res _ _)) t)
ε-Res-ErasureRes∙ ¬p (Var x) = Var x
ε-Res-ErasureRes∙ ¬p (App t t₁) = App (ε-ErasureIso (_ => _) t) (ε-Erasure t₁)
ε-Res-ErasureRes∙ ¬p (If t Then t₁ Else t₂) = Ite (ε-ErasureIso Bool t) (ε-Res-ErasureRes∙ ¬p t₁) (ε-Res-ErasureRes∙ ¬p t₂)
ε-Res-ErasureRes∙ {l} {lₐ} ¬p (Res t) with l ⊑? lₐ
ε-Res-ErasureRes∙ ¬p (Res t) | yes p = ⊥-elim (¬p p)
ε-Res-ErasureRes∙ ¬p₁ (Res t) | no ¬p = Res
ε-Res-ErasureRes∙ {l} {lₐ} ¬p (Resₓ t) with l ⊑? lₐ
ε-Res-ErasureRes∙ ¬p (Resₓ t) | yes p = ⊥-elim (¬p p)
ε-Res-ErasureRes∙ ¬p₁ (Resₓ t) | no ¬p = Resₓ
ε-Res-ErasureRes∙ {l} {lₐ} ¬p (relabel x t) with l ⊑? lₐ
ε-Res-ErasureRes∙ ¬p (relabel x t) | yes p = ⊥-elim (¬p p)
ε-Res-ErasureRes∙ ¬p₁ (relabel x t) | no ¬p = relabel x (ε-Erasure t)
ε-Res-ErasureRes∙ ¬p (relabel∙ x t) = relabel∙ x (ε-Erasure t)
ε-Res-ErasureRes∙ {l} {lₐ} ¬p (t <*> t₁) with l ⊑? lₐ
ε-Res-ErasureRes∙ ¬p (t <*> t₁) | yes p = ⊥-elim (¬p p)
ε-Res-ErasureRes∙ ¬p₁ (t <*> t₁) | no ¬p = Starᴴ (ε-Res-ErasureRes∙ ¬p₁ t) (ε-Res-ErasureRes∙ ¬p₁ t₁)
ε-Res-ErasureRes∙ ¬p (t <*>∙ t₁) = Star∙ (ε-Res-ErasureRes∙ ¬p t) (ε-Res-ErasureRes∙ ¬p t₁)
ε-Res-ErasureRes∙ ¬p ∙ = ∙

ε-Erasure {τ} {lₐ} t with isSensitive? lₐ τ
ε-Erasure {_} {lₐ} t | inj₁ (Macᴴ {h} ¬p) with h ⊑? lₐ
... | yes p = ⊥-elim (¬p p)
... | no ¬p' rewrite ε-Mac-extensional (no ¬p') (no ¬p) t = Mac∙ ¬p (ε-Mac-no-ErasureIso ¬p t)
ε-Erasure t | inj₁ (Resᴴ x) = Res∙ x (ε-Res-ErasureRes∙ x t)
ε-Erasure t | inj₂ y = Iso y (ε-ErasureIso y t)
