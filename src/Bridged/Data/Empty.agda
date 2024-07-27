{-# OPTIONS --safe --cubical #-}
module Bridged.Data.Empty where

open import Cubical.Foundations.Prelude
open import Data.Empty public using (⊥; ⊥-elim)
import Cubical.Data.Empty as 🧊

🧊⊥-elim : ∀ {ℓ} {A : Type ℓ} → 🧊.⊥ → A
🧊⊥-elim ()

isProp⊥ : isProp ⊥
isProp⊥ ()

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
