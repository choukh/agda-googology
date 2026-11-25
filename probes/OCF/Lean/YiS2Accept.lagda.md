# 从第 3 站起的出口前提
验收文件；编译条件定理：第 3 站起的 LowAt 全族推出实际终点的 EBO 序数值下界。
来源：YiNLKeel.ebo-from-low，加 YiS1Low.low1 与 YiS2Low.low2；k2-from-certificate 验证同一证书的出口。
LowAt 的剩余全族仍未实填；第 2 站的新证书不提高已知序数值下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS2Accept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiCNKeel as C
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiS1Accept as SA
import OCF.Align.EboLeanTree as ET
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; exitᵍ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiNLKeel using (ebo-from-low)
open import OCF.Lean.YiS1Low using (low1)
open import OCF.Lean.YiS2Low using (low2; folded²)
open ExSuff gradedᵍ domsᵍ using (Exit₀)

k2-from-certificate : SA.Kᴱ 2
k2-from-certificate = Exit₀.exit exitᵍ (proj₁ folded²) (proj₂ folded²)

ebo-from-low2 : (∀ n → C.LowAt (suc (suc n))) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-low2 lo = ebo-from-low λ { zero → low1 ; (suc n) → lo n }

ebo-from-low3 : (∀ n → C.LowAt (suc (suc (suc n)))) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-low3 lo = ebo-from-low2 λ { zero → low2 ; (suc n) → lo n }
```
