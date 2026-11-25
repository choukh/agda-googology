# 全塔 Leaf、全塔 Lift 与剩余出口前提
验收文件；`leaf-keel`、`lift-keel` 实填全部龙骨站；`full-lift` 覆盖原全域 Lift。
编译条件定理 `ebo-from-low` 仅剩 LowRest；该全族可满足性仍未知，不报告无条件 EBO。
另逐字重写逐站值下界到终点的组装；旧组装只取 reference、hs、upperᴱ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLKeel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiCNKeel as C
import OCF.Lean.YiCNAccept as CA
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-trans′)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiNLRead
open import OCF.Lean.YiNLCanonical
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
open Laws gradedᵍ domsᵍ using (Lift)

full-lift : Lift
full-lift {k} gl r = readR k r

kt-upper : ∀ n → Keel⁻.kt keelᴱ n ≤ᵀ κ n
kt-upper zero = inj₂ refl
kt-upper (suc n) = ≤-trans′ (Ωt-mono (kt-upper n)) (inj₁ (E.hd< (E.lv< (<-sucT (κ n)))))

leaf-keel : C.Leafᵏ
leaf-keel n _ = LL.rdown (tw n) (Ωt-mono (kt-upper n)) (canon-top n)

lift-keel : C.Liftᵏ
lift-keel n = readR (tw n)

ebo-from-low : CA.LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-low lo = CA.ebo-rest (λ n → leaf-keel (suc (suc (suc n)))) (λ n → lift-keel (suc (suc n))) lo

Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)

ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-stations k = ≼-trans GE.reference (l≼ (λ n → ≼-trans (k n (GE.hs n)) (GE.upperᴱ n)))
```
