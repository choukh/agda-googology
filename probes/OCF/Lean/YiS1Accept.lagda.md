# 第 1 站的值与共同终点目标
验收文件；编译定理：`k1ᴱ` 是实际第 1 站的序数值下界，经 `YiGIInst.exitᵍ` 由 `YiS1Low.folded¹` 给出。
`ebo-from-stations` 重写逐站值下界的终点组装，参照和上界引用 `YiGIEnd`；全族前提仍未实填。
`k1-standard` 复用 `YiMTValue.k1ᶻ` 供目标对照，不据它替代实际底上的保持。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS1Accept where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanTree as ET
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ; exitᵍ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiS1Low using (folded¹)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open ExSuff gradedᵍ domsᵍ using (Keel⁻; Exit₀)

Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)

k1ᴱ : Kᴱ 1
k1ᴱ = Exit₀.exit exitᵍ (proj₁ folded¹) (proj₂ folded¹)

ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-stations k = ≼-trans GE.reference
  (l≼ (λ n → ≼-trans (k n (GE.hs n)) (GE.upperᴱ n)))

k1-standard : MV.Kᶻ 1
k1-standard = MV.k1ᶻ
```
