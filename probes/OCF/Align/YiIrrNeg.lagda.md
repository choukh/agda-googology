# YiIrrNeg：对 `YiIrrIf.FoldRows` 的否定路，入口

**判决。** 接口本身没有被否定，反而有实例；被编译结果指到的只有一种定义域取法。

1. 接口：`YiIrrNegModel.model : FoldRows`，定义域 `Only0 × Legal × Low0`。`FoldRows → ⊥` 不可证。
2. 证明当数据：输出、子折叠、链逐点不依赖任何证明（`YiIrrNegForced.Consequences`）；要相关证据的只有 `fold-legal` 与 `position` 这两个证明字段。
3. 大定义域：定义域取整个 `Only0 × Legal`（不带相关的下界证据）时，接口推出 `IrrSearch` 与 `IrrDecide`（`wide→irr-search`、`wide→irr-decide`）。后者不可证是判断，对该取法只写 "未走通"；反例对象不在读回域内，读作谓词缺字段。
4. 块：新块上 `Legal x → Legal (Ω̂ x)` 对一切 `x`（`YiIrrNegLegal.Legal-Ω̂`），塔与 Λ 合法。
5. 预告：目标层 1 的派发不需要位置数据；一般目标层的位置必须是数据（`YiIrrNegDispatch`）。

没有 Funext，没有序数值，强度没有变化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNeg where

import OCF.Align.YiIrrNegLegal
import OCF.Align.YiIrrNegForced
import OCF.Align.YiIrrNegWide
import OCF.Align.YiIrrNegWideDecide
import OCF.Align.YiIrrNegModel
import OCF.Align.YiIrrNegDispatch
```
