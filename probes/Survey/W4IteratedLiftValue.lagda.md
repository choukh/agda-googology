# 相邻标准塔之间每次推进 (ω^ω)^ω 个不动点下标

第四层。设 θ=(ω^ω)^ω。每座编号 k≥3 的标准塔之后，下一塔都能从该塔的值重新启动正槽的两层迭代。实际整树达到 g(θ·ω)，严格超过 g(ω^ω+ω²)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import W4Block as W
open import WVOne using (T₀; 𝟏; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼-suc; s≼s; ≼l; l≼; +-mono; z≼)
import B12Terminal as T
import B18Product as M
import B19IdealProduct as Ar
import B20Room as Room
import B20StandardInside as Std
import B21StandardShape as Rise
import B22TowerCut as K
import Survey.W4RoomDerivative as D
import Survey.W4NextLiftValue as Prior
import Survey.W4RouteTests as Actual
import Survey.W4IteratedLiftRun as R
import Survey.W4IteratedLiftSeries as S
import Survey.W4IteratedLiftPlace as Place
import Survey.W4IteratedLiftOrdinal as O

import Survey.W4IteratedLiftStandard as Pay

module Step (n : ℕ) where
  open Pay.Step n using (all) renaming (a to source; b to target)
  stage : ∀ i x → x ≼ source → O.stages i x ≼ target
  stage zero x p = ≼-trans {b = O.stages 1 x} (O.weak 0 x) (≼-trans {b = O.stages 2 x} (O.weak 1 x) (all 0 x p))
  stage (suc zero) x p = ≼-trans {b = O.stages 2 x} (O.weak 1 x) (all 0 x p)
  stage (suc (suc i)) x p = all i x p
  advance : ∀ a → D.g a ≼ source → D.g (a L.+ O.width) ≼ target
  advance a p = l≼ λ i → ≼-trans {b = O.stages i source} (O.stair i a source p) (stage i source (≼-refl source))

index = λ n → O.width M.· L.natᶜ n
paid : ∀ n → D.g (index n) ≼ Std.std (suc (suc (suc n)))
paid zero = ≼-trans {b = Std.std 1} D.first (≼-trans {b = Std.std 2}
  (≼-trans (≼-suc (≼-refl _)) (Rise.rise 1)) (≼-trans (≼-suc (≼-refl _)) (Rise.rise 2)))
paid (suc n) = Step.advance n (index n) (paid n)

bound = D.g (O.width M.· L.ωᶜ)
cut : bound ≼ K.cut
cut = l≼ λ n → ≼l (suc (suc (suc n))) (paid n)
whole : bound ≼ Actual.Y
whole = ≼-trans cut K.terminal

small = L.ωᶜ M.· L.ωᶜ
small-in : small ≼ Prior.exponent
small-in = ≼l 2 (M.mono (M.one-left L.ωᶜ) (≼-refl L.ωᶜ))
two : L.natᶜ 2 ≼ Prior.exponent
two = ≼l 1 (≼-trans {b = L.ωᶜ} (≼l 2 (≼-refl _)) (M.one-left L.ωᶜ))
prior-index : Prior.exponent L.+ small ≼ O.width
prior-index = ≼l 2 (≼-trans {b = Prior.exponent M.· L.natᶜ 2}
  (+-mono (M.one-right Prior.exponent) small-in) (M.mono (M.one-left Prior.exponent) two))
positive : 𝟏 ≼ O.width
positive = ≼l 0 (≼-refl _)
room : L.suc O.width ≼ O.width M.· L.ωᶜ
room = ≼l 2 (+-mono {a = O.width} {a′ = O.width M.· 𝟏} {b = 𝟏} {b′ = O.width} (M.one-right O.width) positive)
past : L.suc Prior.bound ≼ bound
past = ≼-trans {b = L.suc (D.g O.width)} (s≼s (Prior.monotone {x = Prior.exponent L.+ small} {y = O.width} prior-index))
  (≼-trans {b = D.g (L.suc O.width)} (D.above (D.g O.width)) (Prior.monotone {x = L.suc O.width} {y = O.width M.· L.ωᶜ} room))
```
