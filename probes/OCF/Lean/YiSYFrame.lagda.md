# 对位松一层的站：第 n 站闭项对第 n+1 行
验收文件（读记号）；编译定理：`ebo-from-stations′` 把第 1 站起的逐站目标改成 `EBOψ (suc n) ≼ twc keelᴱ n`（第 0、1 行仍由 `k0`、`k1` 给出），第 1 站 `k1′` 无前提。
`k1′` 复用 `YiFRStations.k2` 去掉末尾 `station-step 1` 的链；`k1-value` 只给 `twᶻ 1`，经 `Bridge` 才接到 `keelᴱ`。
不否定什么：`Bridge`（`twᶻ n ≼ twc keelᴱ n`）没有编译的证明也没有否定。第 2 站的归约见 `YiSYReduce`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSYFrame where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock using (Tr; zero)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiFRStations as FS
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Lean.YiEXRow using (row₂-btbo)
open import OCF.Lean.YiMTValue using (btbo-br1ᶻ; brᶻ)
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiFRStep using (tree-transport)
open import OCF.Lean.YiPCKeel using (k1-value)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

-- perf: C-1，站的闭项只用这一个名字；别的文件的 `Keel⁻` 副本只在变量 n 上与它相遇。
twcᴱ : ℕ → Tr zero
twcᴱ n = Keel⁻.twc keelᴱ n

Kᴱ′ : ℕ → Set
Kᴱ′ n = (h : SI.E.HC (E.EBOψ (suc n))) → SI.E.tree h ≼ K.readRW (twcᴱ n)

-- perf: C-9，在变量 n 上接 upperᴱ；闭的第 0 站只在调用点代入（直接写 k0 与 upperᴱ zero 的复合 8G 堆耗尽）。
stage : ∀ n → FS.Kᴱ n → SI.E.tree (GE.hs n) ≼ K.readRW MT.EBOᶻ
stage n kn = ≼-trans (kn (GE.hs n)) (GE.upperᴱ n)

-- 第 0、1 行仍用原对位的 k0、k1：Kᴱ′ 0 要求 ψ₀(Ω) 不高于第 0 站，不在前提族里。
part : (∀ n → Kᴱ′ (suc n)) → ∀ n → SI.E.tree (GE.hs n) ≼ K.readRW MT.EBOᶻ
part k zero          = stage zero FS.k0
part k (suc zero)    = stage (suc zero) FS.k1
part k (suc (suc n)) = ≼-trans (tree-transport (GE.row-eq (suc (suc n))) (GE.hs (suc (suc n))))
  (≼-trans (k n (subst SI.E.HC (GE.row-eq (suc (suc n))) (GE.hs (suc (suc n))))) (GE.upperᴱ (suc n)))

ebo-from-stations′ : (∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-stations′ k = ≼-trans GE.reference (l≼ (part k))

k1′ : Kᴱ′ 1
k1′ h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 2))
  (≼-trans row₂-btbo (≼-trans btbo-br1ᶻ (rr≼ (brᶻ 1)))))
```

同一对位在标准底的塔 `twᶻ` 上：第 1 站由 `k1-value` 给出；接到终点要逐站的 `Bridge`。

```agda
Kᶻ′ : ℕ → Set
Kᶻ′ n = (h : SI.E.HC (E.EBOψ (suc n))) → SI.E.tree h ≼ K.readRW (MT.twᶻ n)

k1ᶻ′ : Kᶻ′ 1
k1ᶻ′ h = ≼-trans (tree-back h) (≼-trans (k1-value (back h)) (rr≼ (MT.twᶻ 1)))

Bridge : ℕ → Set
Bridge n = K.readRW (MT.twᶻ n) ≼ K.readRW (twcᴱ n)

bridged : ∀ {n} → Bridge n → Kᶻ′ n → Kᴱ′ n
bridged b k h = ≼-trans (k h) b
```
