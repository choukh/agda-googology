# 真实树侧闭项的定向改写：直接生成底输出

本轮对象是旧 Ladder／EmbVV 树侧闭项，不是由记号良基性生成的
EboLean3 标杆。原最高实例的 ψ₀(Ω_{Ω·ω²}) 值验收已在
[TreeEmitBuildAccept](TreeEmitBuildAccept.lagda.md) 转给新闭项。
本入口不导入验收；运行及证书的导入闭包不含记号或标签。
旧构造的形状仍受记号启发，尚不宣称树自足或完成内部 View 验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeEmit where

open import OCF.Align.TreeEmitBuildClosed public
  using (module Rows; module High; closed; closed-legal; fgh)
```

## 改了什么，怎样接值证明

[TreeEmitBuild](TreeEmitBuild.lagda.md) 的 emit 逐原 Q 构造，直接生成 Z，
融合底目标上的 Run→Ordˢ zero→toZ。qi 的非零目标回调、Ω 节点中的
chain／ψᵠ／Ψ、cap 与世界更新仍沿原算法。它不以已求出的 V 充当新输出。

[OrbitRewriteIf](../Free/OrbitRewriteIf.lagda.md) 的 Pointwise 只比较同一
字面闭包界、同一 η/e 处的程序分支；
[OrbitRewriteBuild](../Free/OrbitRewriteBuild.lagda.md) 保留原证书的
全部 ys/hy/dy，构造指定的新证书并证明最终树同形。没有把任意新证书
或任意同值层号上的回调都当成相容。

[Closed](TreeEmitBuildClosed.lagda.md) 对任意 HtB、全部高度／行给 raw、
合法证书、树与原输出同形；闭项确为 HB ω²ᶜ 的 end/zero 全端点。
[Accept](TreeEmitBuildAccept.lagda.md) 接原 vv-ω² 完整双向值，并给全部
行的 FGH 逐点一致。这是保留原高度的改写，不是更高的新站，也不是 EBO。

## 已知边界

新 good 仍由原 GᴺTᵠ 经实际轨道运输得到，旧高层解释器也仍在。
因此本轮尚未消除旧环境证书的生产或证明整体成本下降。
不能把减少一个中间输出层，等同于已删去整套翻译脚手架。

实际成对切片旧侧7351／新侧7483，增加132：原 GᴺTᵠ、Goodᴺ 和高层
运行器仍全部可达，新侧另增加 emit/sound/move。脚本统计相同的树、
证书与FGH执行依赖，并补实际HB ω²参数；是语法近似，不是1513成品
口径。此变体不计作压缩成果；保留作定向改写与实际轨道值桥的实例。

[NegRaw](TreeEmitNegRaw.lagda.md) 和 [NegValue](TreeEmitNegValue.lagda.md)
在同一有限高度段、同一世界实填全部前提，证明任意裸 Q 上的下降删除
律不成立，且实际输出值也会变化。反例的 omk 两字段不满足原 Ω̇ 的
生成关联；故它不否定实际生成域上的进一步改写。

完整实验位置、切片及复核口径统一见
[终点方案](../../Survey/EBOEndgame.lagda.md#11-转到真正树侧闭项的保值改写)
与 [LOG](../../LOG.md)。
