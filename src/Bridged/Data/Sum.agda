{-# OPTIONS --safe --cubical #-}
module Bridged.Data.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Function using (_$_; _∘₂_)

open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Cubical.Data.Sum as 🧊 using (inl; inr)
open import Bridged.Data.Empty

private variable
  ℓ : Level
  A B : Type ℓ

⊎→🧊 : A ⊎ B → A 🧊.⊎ B
⊎→🧊 (inj₁ x) = inl x
⊎→🧊 (inj₂ y) = inr y

⊎←🧊 : A 🧊.⊎ B → A ⊎ B
⊎←🧊 (inl x) = inj₁ x
⊎←🧊 (inr y) = inj₂ y

⊎→←🧊 : (x : A 🧊.⊎ B) → ⊎→🧊 (⊎←🧊 x) ≡ x
⊎→←🧊 (inl x) = refl
⊎→←🧊 (inr x) = refl

⊎←→🧊 : (x : A ⊎ B) → ⊎←🧊 (⊎→🧊 x) ≡ x
⊎←→🧊 (inj₁ x) = refl
⊎←→🧊 (inj₂ y) = refl

⊎≡🧊 : (A ⊎ B) ≡ (A 🧊.⊎ B)
⊎≡🧊 = isoToPath (iso ⊎→🧊 ⊎←🧊 ⊎→←🧊 ⊎←→🧊)

isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ pA pB disj = subst isProp (sym ⊎≡🧊) (🧊.isProp⊎ pA pB (⊥→🧊 ∘₂ disj))
