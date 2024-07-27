{-# OPTIONS --safe --cubical #-}
module Bridged.Data.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Function using (_$_; _∘₂_)

open import Data.Sum public using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Cubical.Data.Sum as 🧊 using (inl; inr)
open import Bridged.Data.Empty

private variable
  ℓ : Level
  A B : Type ℓ

⊎→🧊 : A ⊎ B → A 🧊.⊎ B
⊎→🧊 (inl x) = inl x
⊎→🧊 (inr y) = inr y

⊎←🧊 : A 🧊.⊎ B → A ⊎ B
⊎←🧊 (inl x) = inl x
⊎←🧊 (inr y) = inr y

⊎→←🧊 : (x : A 🧊.⊎ B) → ⊎→🧊 (⊎←🧊 x) ≡ x
⊎→←🧊 (inl x) = refl
⊎→←🧊 (inr x) = refl

⊎←→🧊 : (x : A ⊎ B) → ⊎←🧊 (⊎→🧊 x) ≡ x
⊎←→🧊 (inl x) = refl
⊎←→🧊 (inr y) = refl

⊎≡🧊 : (A ⊎ B) ≡ (A 🧊.⊎ B)
⊎≡🧊 = isoToPath (iso ⊎→🧊 ⊎←🧊 ⊎→←🧊 ⊎←→🧊)

isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ pA pB disj = subst isProp (sym ⊎≡🧊) (🧊.isProp⊎ pA pB (⊥-elim ∘₂ disj))
