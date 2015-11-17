module Untyped.Syntax where

open import Untyped.Base
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _⊔_) public
open import Data.Fin using (Fin ; zero ; suc ; inject≤) public


-- Safe cast.
-- Increase the the lower bound, retyping a term.
-- Note that it is always possible to rewrite terms increasing
-- the upper bound because a variable reference of Fin n can be 
-- safely casted to Fin m if n ≤ m
cast : ∀ {n m} {{p : n ≤ m}} -> Term n -> Term m
cast True = True
cast False = False
cast {{p}} (Var x) = Var (inject≤ x p)
cast {{p}} (Abs t) = Abs (cast {{s≤s p}} t)
cast (App f x) = App (cast f) (cast x)
cast (If c Then t Else e) = If cast c Then cast t Else cast e
cast (Return t) = Return (cast t)
cast (m >>= k) = (cast m) >>= (cast k)
cast ξ = ξ
cast (Throw t) = Throw (cast t)
cast (Catch m h) = Catch (cast m) (cast h)
cast (Mac t) = Mac (cast t)
cast (Macₓ t) = Macₓ (cast t)
cast (Res x t) = Res x (cast t)
cast (Resₓ x t) = Res x (cast t)
cast (label x t) = label x (cast t)
cast (unlabel t) = unlabel (cast t)
cast (join x t) = join x (cast t)
cast ∙ = ∙

--------------------------------------------------------------------------------
-- Auxiliary inequalities and lemmas about ≤ and ⊔

≤-refl : ∀ (n : ℕ) -> n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

leq₁ : ∀ (n m : ℕ) -> n ≤ n ⊔ m
leq₁ zero m = z≤n
leq₁ (suc n) zero = ≤-refl (suc n)
leq₁ (suc n) (suc m) = s≤s (leq₁ n m)

leq₂ : ∀ (n m : ℕ) -> m ≤ n ⊔ m
leq₂ zero m = ≤-refl m
leq₂ (suc n) zero = z≤n
leq₂ (suc n) (suc m) = s≤s (leq₂ n m)

leq3₂ : ∀ (a b c : ℕ) -> b ≤ a ⊔ (b ⊔ c)
leq3₂ a zero c = z≤n
leq3₂ zero (suc b) zero = ≤-refl (suc b)
leq3₂ zero (suc b) (suc c) = s≤s (leq3₂ zero b c)
leq3₂ (suc a) (suc b) zero = s≤s (leq₂ a b)
leq3₂ (suc a) (suc b) (suc c) = s≤s (leq3₂ a b c)
 
leq3₃ : ∀ (a b c : ℕ) -> c ≤ a ⊔ (b ⊔ c)
leq3₃ a b zero = z≤n
leq3₃ zero b (suc c) = leq₂ b (suc c)
leq3₃ (suc a) zero (suc c) = s≤s (leq₂ a c)
leq3₃ (suc a) (suc b) (suc c) = s≤s (leq3₃ a b c)

--------------------------------------------------------------------------------
-- If we wanted to actually write programs in this language it is convenient
-- to use these smart constructors, so that the minimal lower bound
-- is automatically computed while typechecking.

-- Smart constructors for combining terms with differen bounds
app : ∀ {n m} -> Term n -> Term m -> Term (n ⊔ m)
app {n} {m} f x = App (cast {{ leq₁ n m }} f) (cast {{ leq₂ n m }} x) 

if_then_else_ : ∀ {a b c} -> Term a -> Term b -> Term c -> Term (a ⊔ (b ⊔ c))
if_then_else_ {a} {b} {c} t₁ t₂ t₃ = If t₁' Then t₂' Else t₃'
  where t₁' = cast {{ leq₁ a (b ⊔ c) }} t₁
        t₂' = cast {{ leq3₂ a b c }} t₂
        t₃' = cast {{ leq3₃ a b c }} t₃

-- And so on for all the other compound constructors
