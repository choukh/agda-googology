{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Norm2 where
open import Probe3
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Primitive using (lzero)
-- (b) does the CANDIDATE limit lens stay continuous at limits?
lim-normal : (t : Nat → Lens lzero) (f : Nat → Ord lzero)
  → app (limLens t) (olim f) ≡ olim (λ n → app (limLens t) (f n))
lim-normal t f = refl
