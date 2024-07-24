{-# OPTIONS --safe --cubical #-}
module Bridged.Data.Empty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Data.Empty public using (⊥; ⊥-elim)
import Cubical.Data.Empty as 🧊

⊥→🧊 : ⊥ → 🧊.⊥
⊥→🧊 ()

⊥←🧊 : 🧊.⊥ → ⊥
⊥←🧊 ()

⊥≡🧊 : ⊥ ≡ 🧊.⊥
⊥≡🧊 = isoToPath (iso ⊥→🧊 ⊥←🧊 (λ ()) (λ ()))

isProp⊥ : isProp ⊥
isProp⊥ ()

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
