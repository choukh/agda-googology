# 配对审计：rank 2 的坐标前提有真实整链实例

将已证的原第二部分和最高反馈链接到新有限层证书 Good 1。
不把任意原始第1层坐标当作有证书；桥同时消费旧Reg与原LgB。
新Legal的枝量词由明确合法世界或Good 0坐标满足。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteNegActual where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (P)
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L)
open import OCF.Lean.BoundedFoldRun using (chain)
import OCF.Lean.BoundedTargetRegIf as Old
open import OCF.Align.BoundedFiniteRegIf
import OCF.Align.BoundedMixedSecondCoordinate as Coordinate
import OCF.Align.BoundedTargetRegClosure as Certificate

reg : ∀ c → Old.Reg c → Reg 1 c
reg hz r = tt
reg (hs c) r = reg c r
reg (hl f) r = λ n → reg (f n) (r n)
reg (hΩ (inj₁ κ) g) r = tt , (λ c rc → reg (g c) (r c))
reg (hΩ (inj₂ _) g) (mo , r) =
  (λ rw bc bd p → mo bc bd p) , (λ c rc → reg (g c) (r c))

legal-world : ∀ {W} → LegalWorld 1 W → LgW (F 1) W
legal-world (lW , rb , lb) = lW , lb

legal : ∀ c → LgB c → Legal 1 c
legal hz l = tt
legal (hs c) l = legal c l
legal (hl f) (st , l) = (λ rw n → st n) , (λ n → legal (f n) (l n))
legal (hΩ (inj₁ κ) g) (mo , l) =
  (λ lw bc bd p → mo (legal-world lw) bc bd p) ,
  (λ c q → legal (g c) (l {w = (proj₁ q , one 0)} (proj₁ (proj₂ q) , tt) (proj₂ (proj₂ q))))
legal (hΩ (inj₂ _) g) (mo , l) =
  (λ lw bc bd p → mo (legal-world lw) bc bd p) ,
  (λ c q → legal (g c) (l {w = (w₀L P , c)} (lw₀L P , proj₂ q) hself))

actual-good : ∀ n → Good 1 (chain Coordinate.Actual.run n)
actual-good n = reg _ (Certificate.actual-reg n) , legal _ (Coordinate.actual-coordinate-legal n)

-- 这正是第2层新增种类要求的低阶坐标条件。
rank-two-coordinate : ∀ n → LegalCoord 2 (inj₂ tt) (chain Coordinate.Actual.run n)
rank-two-coordinate = actual-good
```

该实例覆盖全部 n 的实际坐标，不是仅检查种子或有限样本。它证明共享
Good 1 前提可满足，不证明任意阶运行器保持Good或全混合输出合法。
翻译账：仅证书之间的结构桥，无新树、运行器或记号规则。
