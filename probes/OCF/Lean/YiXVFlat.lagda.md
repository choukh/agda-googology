# YiXVFlat
> 验收文件。档位：编译定理。Strong 源层上，零前缀嵌入后的低目标 flat 不大于高目标 flat；两个目标有字面界。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFlat where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableFold as F
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVFlatInput as Q
import OCF.Lean.YiXVFlatGround as G
import OCF.Lean.YiXVFlatStage as S
import OCF.Lean.YiXVRefLift as E
ops : ∀ κ → Strong κ → Q.Ops κ
ops L.zero h = G.ops
ops (L.suc κ) h = S.Stage.result (L.suc κ) h (λ { L.zero → ops κ h })
ops (L.lim f s) h = S.Stage.result (L.lim f s) h (λ { (L.self n) → ops (f n) (proj₁ h n) })
actual : A.Le (E.embedded (λ q → L.suc q) (Q.flat L.ωᴵ (λ q → q) (L.Ω L.ωᴵ)))
  (Q.flat (L.suc L.ωᴵ) (λ q → L.suc q) (L.Ω L.ωᴵ))
actual = Q.Ops.compare (ops L.ωᴵ F.ω-strong) F.ω-strong F.ω-strong L.zero
  (λ q → L.suc q) (λ q → q) (λ q → L.suc q) A.omegaΩ
```
