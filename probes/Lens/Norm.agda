{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Norm where
open import Probe3
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Primitive using (lzero)
-- (a) is the Gentzen lens continuous at limits, definitionally?
gentzen-normal : (f : Nat → Ord lzero)
  → app gentzen (olim f) ≡ olim (λ n → app gentzen (f n))
gentzen-normal f = refl
