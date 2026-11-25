# 新标准塔的已有下界
验收文件，读记号；编译定理覆盖全部 n 与全部 HC tω 证书。
来源：YiVTTw2Hi.tω≼twᶻ 与 YiCWTable.tw-same；只搬标准底的独立塔项。
不提供 EBOᵗ 或其实际分支的值下界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNDTower where
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiCWTable using (twᵗ; tw-same)
open import OCF.Lean.YiVTANLim using (tω; hΩω)
open import OCF.Lean.YiVTTw2Hi using (tω≼twᶻ)
tω≼twᵗ : (n : ℕ) (h : HC tω) → R2.Rt h ≼ readRW (twᵗ (suc (suc n)))
tω≼twᵗ n h = subst (λ x → R2.Rt h ≼ readRW x)
  (sym (tw-same (suc (suc n)))) (tω≼twᶻ n h)
inst : R2.Rt hΩω ≼ readRW (twᵗ 2)
inst = tω≼twᵗ 0 hΩω
```
