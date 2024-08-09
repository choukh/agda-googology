{-# OPTIONS --safe --cubical #-}
module Bridged.Data.Unit where

open import Cubical.Foundations.Prelude
open import Data.Unit public using (⊤; tt)

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl
