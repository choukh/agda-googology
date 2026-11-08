# 实际生成域的迁世界与再次运行

本轮针对完整 EBO 链中“实际输出在扩张世界能否继续运行”这一段。
通用合法输入的 Gd 搬运仍被否定；正面结果只消费原 Φ/ΦX 的真实输出。
它们满足全裸分支位置 Full，由此在给定未来底世界有新 Gd；在新世界
正规化后，可以真实再次调用原 Φ，输出再次满足同一 Full。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitGenerated where

import OCF.Lean.CircuitLegalIf
import OCF.Lean.CircuitLegalBuildNormal
import OCF.Lean.CircuitLegalBuildActual
import OCF.Lean.CircuitLegalNegGd
import OCF.Lean.CircuitGeneratedIf
import OCF.Lean.CircuitGeneratedBuild
import OCF.Lean.CircuitGeneratedFuture
import OCF.Lean.CircuitGeneratedX

-- 原前批三件的接手复核入口；ZeroFill 仅否定所写的界外填零合同。
import OCF.Lean.ThirdRunFamilyIf
import OCF.Lean.ThirdRunFamilyBuild
import OCF.Lean.ThirdRunFamilyNegFill
```

| 构件 | 已实填的范围 | 未声称的结果 |
|---|---|---|
| [Normal](CircuitLegalBuildNormal.lagda.md) | 全 Sb n、全高度、全种类的原富合法化保持当前 Gd。 | 不是 PH 全族保持，也不从旧 Gd 得未来 Gd。 |
| [合法域反例](CircuitLegalNegGd.lagda.md) | 原 Sb 1 上世界、源高度、源树均合法，旧 Gd 仍不能免费迁移；触发坐标有新 Gd 但已证不合法。 | 不是实际 Φ 输出反例，不关闭路线。 |
| [原 Φ 输出](CircuitGeneratedBuild.lagda.md) | 任意原底、世界、San、源高度、全部目标和种子，实际输出都有 Full。 | 输入／地板不必 Full；Full 不表示折叠无损。 |
| [未来重用](CircuitGeneratedFuture.lagda.md) | 全 Sb n 原整源输出，在显式给定的合法未来底世界正规化并实际再次 Φ；再次输出 Full。 | 没有由输出生成这个底世界；不把局部世界当底世界。 |
| [原 ΦX 输出](CircuitGeneratedX.lagda.md) | 全部原 ΦX 参数和非零目标也满足同一 Full。原 stp 入口实填。 | 零目标 Full 可对任意树自证，stp 实例不增加 desc 证书强度。 |

## 正反实例在同一原源上接合

下面直接使用合法域反例的原合法输入：输入本身没有新世界 Gd，
但它经原 Φ 得到的真实输出可在该新世界正规化并再次运行。
这是非空接线校准，不是高序数信息保留的值测试。

```agda
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
import OCF.Lean.CircuitLegalNegGd as N
import OCF.Lean.CircuitGeneratedFuture as Future

module Example where
  module A = Future.Run 1 N.w₀ N.lw₀ hz (hs N.m) N.legal-m N.input N.old-input
  module V = A.Enter N.w₁ N.lw₁ N.grow

  moved : V.New.Gd (hs N.m) (A.A.normal (hs N.m) hself (hz , tt))
  moved = V.normal-certificate (hs N.m) hself (hz , tt)

  rerun : V.New.GT (hs N.m)
  rerun = V.again (hs N.m) hself (hz , tt) (hs N.m) hself (hz , tt)
```

## 对完整终点的边界

没有修改原树、折叠、合法化或闭项。原洗法和取底枝的值损失没有消失；
Full 可能正是这些全裸坐标处理带来的结果，不能由此宣称树自足或新高度。
实际未来底世界的生成、其与原局部反馈的连接、QL/PH 及最终 Cd 值覆盖，
以及内部 View 和完整成本仍是独立任务。完整 EBO 验收仍是
[TerminalFoldAccept](../Align/TerminalFoldAccept.lagda.md) 的全参照覆盖。
