# K3: 五个现成闭项的封顶位置 (入口)

> **第 4 层判定题, 判决 PARTIAL.** 五个候选都交封顶的编译事实 (乙), 没有一个交条件覆盖定理的实填 (甲). 没有一条是值上界.
>
> - 类型封顶 (下标类型里缺一种极限): `HtFeedClosed.TΛ` 在层号 Ω₂ ([K3CapHtFeed](K3CapHtFeed.lagda.md)); `RecB.Tω` 在第 ω 个底, 签名一级 ([K3CapRecB](K3CapRecB.lagda.md)); `RadicalValueNativeFinal.closed` 的源族在 Ω-共尾的高度 ([K3CapRadical](K3CapRadical.lagda.md)).
> - 类型不封顶, 跨底折叠在 Ω-共尾的回灌下标处只走代表坐标一支: `Third.TΛ` ([K3CapThird](K3CapThird.lagda.md)), `OutputDriven.closed`/`closedGrid` ([K3CapOutputDriven](K3CapOutputDriven.lagda.md)); 共用陈述在 [K3CapSan](K3CapSan.lagda.md).
> - 不否定: 换下标类型或换派发规则之后的同族候选; 各入口原有的读法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3Cap where

import OCF.Align.K3CapHtFeed
import OCF.Align.K3CapRecB
import OCF.Align.K3CapSan
import OCF.Align.K3CapThird
import OCF.Align.K3CapOutputDriven
import OCF.Align.K3CapRadical
```
