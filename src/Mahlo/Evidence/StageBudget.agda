{-# OPTIONS --safe --without-K #-}
module Mahlo.Evidence.StageBudget where

-- Critical-path experiment ONLY: the class-sized stage construction can stay
-- at Set₁ when closure is given by finite supports on Nat codes.
-- No distinguishedness, ordinal validity, TI, or endpoint theorem is assumed
-- proved here. Parameters are explicit unfulfilled reference-system debts.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
import Mahlo.WellOrder.Accessible as Accessible

data All (A : Nat → Set₁) : List Nat → Set₁ where
  empty : All A []
  extend : {x : Nat} {xs : List Nat} → A x → All A xs → All A (x ∷ xs)

data Supported (A : Nat → Set₁) : List (List Nat) → Set₁ where
  here : {xs : List Nat} {xss : List (List Nat)}
    → All A xs → Supported A (xs ∷ xss)
  there : {xs : List Nat} {xss : List (List Nat)}
    → Supported A xss → Supported A (xs ∷ xss)

module Budget
  (Valid : Nat → Set) (lt : Nat → Nat → Set)
  (supports : Nat → Nat → List (List Nat))
  (Global : Nat → Set₁) (M : Nat) (boundary : Nat → Nat) where

  Class : Set₂
  Class = Nat → Set₁

  Closure : Class → Nat → Nat → Set₁
  Closure A a d = Σ (Valid d) (λ _ → Supported A (supports a d))

  module Rule (A : Class) where
    Eligible : Nat → Set₁
    Eligible d = Closure A d d

    Tau : Nat → Nat → Set₁
    Tau a d = Σ (Closure A a d) (λ _ → lt d a)

    module G = Accessible.Generate Eligible Tau

  W : Class → Class
  W A = Rule.G.Generated A

  -- The host does not require resizing these large predicates into Set.
  -- boundary n is intended to code Ω_(M+n), still uninstantiated.
  stage : Nat → Class
  stage zero x = Σ (Global x) (λ _ → lt x M)
  stage (suc n) x = Σ (W (stage n) x) (λ _ → lt x (boundary (suc n)))
