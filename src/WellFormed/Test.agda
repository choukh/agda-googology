{-# OPTIONS --safe #-}
module WellFormed.Test where
open import WellFormed.Base

limExt : ⦃ _ : wf f ⦄ ⦃ _ : wf g ⦄ → lim f ≘ lim g → (∀ n → f n ≡ g n) → lim f ≡ lim g
limExt homo eq with <-trich homo
... | tri< p _ _ = case lim-inv p of λ { (n , p) → {!   !} }
... | tri≈ _ refl _ = refl
... | tri> ¬a ¬b c = {!   !}
