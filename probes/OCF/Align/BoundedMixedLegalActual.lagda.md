# 原实际全混合输出的合法性接口

更正 Lean.BoundedMixedLegalIf 文首的未经验证预期：对其 output 与原
Mixed.output 用 refl 检查，Agda 返回42，停在不同的 sums n。
这只是定义转换失败，不是否定两者的值或结构关系。为实际目标不再
增加副本桥，本验收入口直接引用原定义；不能用模型Pointwise替代它。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedMixedLegalActual where
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
import OCF.Align.BoundedFoldValueMixed as M
import OCF.Align.BoundedFoldValueMixedSteps as Steps
import OCF.Lean.BoundedContextClosed as C

record OriginalPointwise : Set where
  field
    legal-at : ∀ n → LgB (M.Fold.fold hz (z⊲ᴮ C.B) (M.sums n))

finish : OriginalPointwise → LgB M.output
finish p = (λ n → Steps.folded-step n) , OriginalPointwise.legal-at p
```

finish没有实例，尚不是整体合法性结论。Pointwise的实际构造仍是本轮
任务；本文只使验收接口准确指向原运行器与原全自然数输入。
