# O3：形状判据排除旧 HS 反例

**编译定理，不是有限测试。** 这里使用 `NoKCertNeg` 的实际反例 Y：
它有 HS，但第一个极限步进不是字面第一位置。新的 `Shape` 不能
接受这个反例，故没有把旧的错误 HS 桥重新包装成新证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO3ShapeCheck where

open import Data.Empty using (⊥)
import OCF.Align.LevelFixCore as LF
import OCF.Align.NoKCertNeg as N
open import OCF.Align.TreeLevelsO3Shape

no-shape-Y : Shape N.Y → ⊥
no-shape-Y h = N.no-Lgl-Y (Lgl-from-shape LF.zero N.Y h)
```

`generated-shape` 是判据的实际实例族；`no-shape-Y` 的反例底树由
`N.HS-Y` 证实有 HS。这里不否定原候选的实际输出具有 Shape，那个问题
仍开放，也不从“新判据排除了一个旧反例”推断原闭项已合法计值。
