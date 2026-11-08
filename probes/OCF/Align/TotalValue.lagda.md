# 新闭项的值证明入口

对象始终是冻结的 `RadicalValueNativeFinal.closed`，原定义未改。
目前已证 ψ₀(Ω_Ω)+ω 不高于其序数值；尚未证明原 EmbVV 的
ψ₀(Ω_{Ω·ω²}) 下界、准确值或具名上界，不宣称达到 EBO。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TotalValue where
open import OCF.Align.TotalValueHighStrict public using (strict-lower)
open import OCF.Align.TotalValueHighOmega public using (omega-lower)
open import OCF.Align.TotalValueBuildHighAccept public using
  (reference; reference-label; reference-lower; named-lower)
open import OCF.Align.TotalValueNegStrictAudit public using (not-btbo-upper)
open import OCF.Align.TotalValueTailHighFinal public using (high-sv; final-upper)
```

## 先读这些结论，再按需追证明

| 结论 | 直接入口 | 范围 |
|---|---|---|
| 冻结完整新闭项有BTBO加ω下界，并严格高于BTBO | [HighOmega](TotalValueHighOmega.lagda.md)、[HighStrict](TotalValueHighStrict.lagda.md) | 原 HBω² 端行，经真实闭包站及两层链进入原 Final；不是替换成低输入 |
| 任意原闭包行严格高于低行 | [ClosingStrict](TotalValueClosingStrict.lagda.md) | 原 Ωd1 种子第零支与第二观察输出正性，全部 HtB |
| 原完整基底闭包值恰为 BTBO | [下界](TotalValueBuildBaseActual.lagda.md)、[上界](TotalValueTailBaseWholeUpper.lagda.md) | 全部合法世界；后者不是最高端行上界 |
| 原完整基底经末端第一位置完成仍同 BTBO | [HighBaseFinal](TotalValueTailHighBaseFinal.lagda.md) | 全部合法世界；用固定外部BTBO参照实填，不是假定leg一般值单调 |
| 全原Q的底观察运行都有遗传严格性 | [HighGenerated](TotalValueTailHighGenerated.lagda.md) | 所有实际反馈分支，覆盖最高源；不声称全部裸Z严格 |
| 最高闭项的末端外部界运输 | [HighFinal](TotalValueTailHighFinal.lagda.md) | 输出严格性已实填；外部参照的HS/St及原高输出界仍为前提 |
| 完整最高闭项两层累计结构 | [HighShape](TotalValueTailHighShape.lagda.md) | 全n/k、原实际首项和最终leg均保留；不是具名上界 |
| 插入前缀后，完整前驱嵌入可通过 typed 折叠 | [BaseConsumer](TotalValueBuildBaseConsumer.lagda.md) | 全部可入层号、实际回调与环境；不只是零参数 |
| 非零参数1的完整跨层回收 | [RecoverActual](TotalValueBuildRecoverActual.lagda.md) | 全部高度、实际 cap 环境及整条反馈；未推广任意 η |
| 末端完成确会改变部分原 Q 输出的值 | [TailGenerated](TotalValueTailGenerated.lagda.md) | 否定泛原Q保值，不是最高 Ω̇ 端行的反例 |

累计嵌入需要跨极限支相容：[TailEmbedding](TotalValueTailEmbedding.lagda.md)
用严格边界统一选择映像；[PureEmbedding](TotalValuePureEmbedding.lagda.md)
把纯读取的值下界加强为可回灌的前驱嵌入。仅有值不等式不够，
[CumulativeLift](TotalValueCumulativeLift.lagda.md) 通过下一次折叠完成
必要的提升，代价是实际轨道错位，而非假设一般值序可逆。

[ActualTrace](TotalValueActualTrace.lagda.md) 直接由检查器取得原 run
的真实私有轨道，[TraceShape](TotalValueTraceShape.lagda.md) 给整树对应；
没有为验收方便改原运行器或要求函数外延。

准确高值的关键未完成项是：高 rank 反馈坐标的遗传生成域与非零回收，
以及在该域上的整高行嵌入／吸收。新的 Gen 工作是为填此处，不把已有
Balanced 或参数1回收冒充全部 η。这里只维护验收，成品仍不导入本页。


高域证书只在验收侧出现：[RelatedGenFloor](TotalValueBuildRelatedGenFloor.lagda.md)
覆盖原全部高度、全部参数Ω̇；[RelatedGenOps](TotalValueBuildRelatedGenOps.lagda.md)
封闭原加法、重复与完整链。[后继运输](TotalValueTransportSuccessor.lagda.md)
与[极限运输](TotalValueTransportLimit.lagda.md)各给正反两式Rq通勤，
不把函数逐点相容改成函数等式。域覆盖与层内保持仍不等于跨层值回收；
高行全参数的观察关系保持是下一实质缺口，不以文件数量替代它。

[RelatedGenPsi](TotalValueBuildRelatedGenPsi.lagda.md)和
[RelatedGenPsiHeight](TotalValueBuildRelatedGenPsiHeight.lagda.md)现已完整证明
原ψᵠ、Ψ在全部获准域、实际环境及反馈链上的保持；不是条件空接口。
[TailRecoveryMarker](TotalValueTailRecoveryMarker.lagda.md)再把生成marker的
全部实际观察重写到低字段的原ι，包含新run同形。但原ι与跨高度ι↓
之间的全参数观察耦合尚缺，不能从域保持直接推出高值恢复。


## 生成域各版本的适用范围

| 版本 | 准入与已证明范围 | 未交付的部分 |
|---|---|---|
| BuildGen* | qi量所有裸坐标，marker要求字面body=ιlow；已证后继/极限及原升降保持 | 原完整rowB准入未填，不用它冒充实际全源 |
| BuildAdmittedGen* | qi只接结构自相关坐标，marker仍是字面等式；原全Ω̇与升降准入 | 搬运后的精确body等式未填；只是暂停此强合同 |
| BuildRelatedGen* | marker保低Gen、body Core及Rq相容；原全Ω̇、升降、搬运、加法、反馈、ψ与Ψ保持均已实填 | 原ι/ι↓的全参数观察耦合，及由它导出的整高行值界 |

最终复核入口为 [Survey.TotalValueReview](../../Survey/TotalValueReview.lagda.md)。
本轮98件已冻结验证模块由主审单6G从头复编退出0；逐根源码与编译器
本地闭包一致，安全扫描通过。复核只认证这些陈述，不把未完成项算入。
