# 从每一轮恢复值重用首塔子调用的上界

第四层，无条件。即使从第 n 轮的恢复值本身起步，反复调用首塔每次正询问共有的一级子运行，全部有限轮次的上确界仍严格低于本轮旧历史的上确界。对每个正 n，第零个下一孩子的恢复值已经严格更大。[子运行的精确值](W4ReturnBoundFirst.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnBoundOrbit where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s; z≤n)
import Data.Nat.Properties as NP
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl; subst; cong; sym; trans)
open import OCF.Lean.YiRefTw2 using (tree-≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; s≼s)
import W4Block as W
import W4Ops as O
import B12XRef as Ref
import B12BtboCut as F
import B18Product as M
import B19IdealProduct as Law
import B26Depth as Depth
import B27Threshold as T
import B27CutArithmetic as Algebra
import B28Orbit as Name
import B28OrbitValue as V
import B28Branches as Child
import Survey.W4LegacyFeedback as Climb
import Survey.W4ReturnBoundFirst as Fixed
import Survey.W4Rule48 as H

factor = Law.power Fixed.ε L.ωᶜ
total = λ x → x M.· factor

ε-small : Fixed.K.small Fixed.ε
ε-small = ≼-trans {b = L.suc (F.finite 1)} (s≼s Ref.epsilon) (Climb.step 1)

factor-low : L.suc factor ≼ F.finite 2
factor-low = Fixed.K.power Fixed.ε L.ωᶜ ε-small Fixed.K.omega

factor-first : L.suc factor ≼ Name.value 1
factor-first = ≼-trans {b = F.finite 2} factor-low
  (≼-trans {b = L.suc (F.finite 2)} (≼-suc (≼-refl _))
    (≼-trans {b = H.cut 0} (H.finite-short 2)
      (≼-trans {b = L.suc (H.cut 0)} (≼-suc (≼-refl _)) (H.below-next 0))))

product-inside : ∀ k → 2 ≤ k → ∀ x y → L.suc x ≼ T.row k → L.suc y ≼ T.row k → L.suc (x M.· y) ≼ T.row k
product-inside k two = Algebra.At.product k two

module Positive (n : ℕ) where
  old : L.suc (Name.value 1) ≼ T.row (suc (suc (suc n)))
  old = T.below (suc (suc (suc n))) (Name.target 1) (subst (_≤ (suc (suc (suc n)))) (sym (V.height 0)) (s≤s (s≤s (s≤s z≤n))))

  coefficient : L.suc factor ≼ T.row (suc (suc (suc n)))
  coefficient = ≼-trans {a = L.suc factor} {b = L.suc (Name.value 1)} {c = T.row (suc (suc (suc n)))}
    (≼-suc {a = L.suc factor} {b = Name.value 1} factor-first) old

  inside : L.suc (total (Name.value (suc n))) ≼ T.row (suc (suc (suc n)))
  inside = product-inside (suc (suc (suc n))) (s≤s (s≤s z≤n)) (Name.value (suc n)) factor (V.upper n) coefficient

  first-child : L.suc (total (Name.value (suc n))) ≼ Child.At.Head.point (suc n) 0
  first-child = ≼-trans {a = L.suc (total (Name.value (suc n)))} {b = T.row (suc (suc (suc n)))} {c = Child.At.Head.point (suc n) 0} inside
    (T.minimum (suc (suc (suc n))) (Child.At.sub (suc n))
      (subst (suc (suc (suc (suc n))) ≤_) (sym (trans (Child.At.gain (suc n)) (cong suc (V.height n)))) NP.≤-refl))

below-history : ∀ n → L.suc (total (Name.value n)) ≼ H.cut n
below-history zero = ≼-trans {b = F.finite 2} (Fixed.K.product (Name.value 0) factor lo factor-low)
  (≼-trans {b = L.suc (F.finite 2)} (≼-suc (≼-refl _)) (H.finite-short 2))
  where
  lo : Fixed.K.small (Name.value 0)
  lo = ≼-trans {b = L.suc Fixed.ε} (s≼s (≼-trans {b = Ref.row 0}
    (tree-≼ refl (Name.out-h 0) (Ref.H 0)) Ref.small)) ε-small
below-history (suc n) = ≼-trans {b = Child.At.Head.point (suc n) 0} (Positive.first-child n)
  (≼-trans {b = L.suc (Child.At.Head.point (suc n) 0)} (≼-suc (≼-refl _))
    (H.OnOrbit.H.G.first (suc n) 0))

module Actual (β : O.Tr⁺ W.zero) where
  module R = Fixed.Run β
  short : ∀ n → R.x ≼ Name.value n → L.suc R.total ≼ H.cut n
  short n p = ≼-trans {b = L.suc (total (Name.value n))}
    (s≼s (≼-trans {b = total R.x} (proj₁ R.exact) (M.mono p (≼-refl factor)))) (below-history n)
```
