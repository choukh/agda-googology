# 原地板闭项与多槽轨道的逐字接合

这里不改原 TΩ 的初值和数组。每一个旧后继层闭项都恰是共享接口中
Original.oO 的 ℕ-极限；最高坐标初值仍为 top m，低世界仍为 Wi m。
因此上一文件的全轨道同形定理确实作用在原闭项，而非替代轨道。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldCoverFloor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same)
import OCF.Lean.Fold1 as Old
import OCF.Lean.Fold1If as I
import OCF.Lean.Fold1Base as Base
open import OCF.Align.BoundedWorldCoverIf
import OCF.Align.BoundedWorldCoverRun as Run
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)

module Floor (m : Cd) (lm : LgB m) where
  module A = Actual m lm (Base.Wi (hs m))
  original-shape : Old.TΩ (hs m) lm ≡ hl A.Original.oO
  original-shape = refl
  initial : A.Original.ce zero ≡ I.top m
  initial = refl
  lower-world : ∀ n → proj₁ (A.Original.cw n) ≡ Base.Wi m
  lower-world zero = refl
  lower-world (suc n) = refl
  entire-world : ∀ n → A.Original.cw n ≡ (Base.Wi m , A.Original.ce n)
  entire-world zero = refl
  entire-world (suc n) = refl
  coordinates : ∀ n → Same (A.Original.ce n) (A.orbit n)
  coordinates = Run.coordinates m lm (Base.Wi (hs m))

-- 全有限族；不是只验第一、第二项。
finite-shape : ∀ n → Old.TΩ (num (suc n)) (legal-num n) ≡
  hl (Actual.Original.oO (num n) (legal-num n) (Base.Wi (num (suc n))))
finite-shape n = Floor.original-shape (num n) (legal-num n)
finite-coordinates : ∀ n k → Same
  (Actual.Original.ce (num n) (legal-num n) (Base.Wi (num (suc n))) k)
  (Actual.orbit (num n) (legal-num n) (Base.Wi (num (suc n))) k)
finite-coordinates n = Floor.coordinates (num n) (legal-num n)
```

原输出的第 k 项仍是 Φ 到零层，输入 up(Original.ce k)，世界由 entire-world
精确给出。该世界中的每个低槽可在内部坍缩中读取、更新；本篇没有证明
它被 UniformEvaluation.read 的固定 seed 解释覆盖。需要的下一字段是
在保留这些低槽时对上述输出的有向模拟，并把输出部分和送入同一个实际
规范输出。坐标 Same 本身不能充当该字段，更不能据此宣布整个有限族 ≤ C。
