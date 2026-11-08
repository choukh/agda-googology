# 从原高闭项生成域接续事件回灌

接续 [迁回实验](EventReturnCtx.lagda.md)，本批将检验点移到原闭项实际
产生的高层节点。目标仍是全种类树定义及终点 EBO 序数值下界；这里
没有达到新高度，也没有证明整个原 Run 的闭包。

## 实际机制与精确结果

原 Ωd 的事件分支先读重放界，再进入动态层 g(rp H κ) 的节点。
因此“目标层迁回可忘掉高事件”和“源层在两个历史里同步运行”不能
使用同一份历史关系。迁回本身还保留闭包捕获的旧历史，不能误读成
在新历史上重新生成源。

| 交付 | 具体范围 | 未完成的部分 |
|---|---|---|
| [源生成合同与实例](EventGeneratedBuild.lagda.md) | 原 Ω₂ᴱ、Ω₃ᴱ、Ω₃² 及完整 top₃ 前缀；实际分支对全部相关坐标保持 Shape。合同的 generated-exact 逐字绑定原 Ωd。 | 不要求任意 g 同余，不宣称所有输入自动相关。 |
| [两种重放槽](EventGeneratedValueReplay.lagda.md) | 完整同步事件表的两个原 rp 均保持 Shape；原 RB 从显式相关输出产生相关事件。 | 不将仅保低界的 HistLow 当成完整同步。 |
| [原第一反馈](EventGeneratedValueFirst.lagda.md) 与 [闭项接线](EventGeneratedValueActual.lagda.md) | 任意合法最高层上的首事件关系；原进入状态实填；最终原 top₃ Ω₃² 的 body、azero→one、真实前缀接到动态层 Pair。 | 首事件没有消费后继格的输出；仍未证明 Chn、κcε 后继及完整状态闭包。 |
| [路径与可达性](EventGeneratedPath.lagda.md) | 同世界下运输第一位置、StH 与给定 AccY，保 Ω 的同 raw 坐标及 Bd。 | 两个世界间的坐标与 Bd 配对不能直接由此取得。 |
| [实际双向数据转换](EventGeneratedTransport.lagda.md) | 同世界、Shape 相关层的全部原 D 构造子；ni 先逆搬低坐标，再调用原分支。 | 没有高层往返逆律、保值或 Run 交换定理。 |
| [零层值](EventGeneratedTransportZero.lagda.md) | 全部原 D₀、任意 base 的 sum 逐形与正向转换的双向序数值界；逆向转换也有逐形。 | 不从零层推断高层值保持。 |
| [精确反例及捕获方程](EventGeneratedNegRank.lagda.md) | 合法 Ω₃ᴱ 的两个 HistLow 历史给不同且不 Shape 的动态层；原 drp₂ 的事件分支仍接回旧基底。 | 只否定 HistLow→同动态层／Shape 的候选桥，不否定原 drop、Generated 或整条路线。 |
| [全事件区间公式](EventOneWalk.lagda.md) | 原回调为 n1 时，任意源层、区间和状态的 WalkE 第二层输出恰为 counted(length suffix, 原累计值)。 | 常后继回调只看事件次数不代表任意回调也如此。 |
| [原后继内枝输出](EventGeneratedValueStep.lagda.md) | 先证保留 κ₀ 回调在全部同步未来后缀上的关系，再接原 ValueStep.output；迁回前后 rd₂ 逐枝 Shape。实际前缀、累计状态和零段均保留。 | 旧 refl 尝试的更强命题等式仍未证明，不称整个 κ₁ 反馈链已经相容。 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGenerated where

import OCF.Align.EventGeneratedIf
import OCF.Align.EventGeneratedBuild
import OCF.Align.EventGeneratedPath
import OCF.Align.EventGeneratedTransport
import OCF.Align.EventGeneratedTransportZero
import OCF.Align.EventGeneratedNegRank
import OCF.Align.EventGeneratedValueReplay
import OCF.Align.EventGeneratedValueFirst
import OCF.Align.EventGeneratedValueActual
import OCF.Align.EventOneWalk
import OCF.Align.EventGeneratedValueStep
```

## 对统一实现的意义与限制

本批给出的是实际生成的动态层、合法位置和低坐标转换，补足了
固定 R₁/R₂ 校准不能直接表达的一个接点。双向转换把相反方向的
高阶输入处理放在一个 Maps 中，终止依靠原 Acc 子证明与数据递归，
不靠函数外延或停机豁免。这是可复用的树侧结构信息。

它还没有给全种类 read/drop 的定义。现有旧 T 只有两种事件；继续
增加其专属层或关系文件并不能完成 Λ。下一实现需要统一处理生成的
低坐标、源分支、Ai/BNi/Chn 状态和后继反馈，或给出更弱而足够的
捕获环境证明；不把所有 raw Run 的迁回当成必须完成的先决目标。

本批不新增按记号阶段设计的字段，不改旧树、折叠与合法性，也不将
不同动态层强制命题相等。必要内部 View 和完整前三层成本仍须另交；
这些研究证明不是新的成品成本测量，不能拿叶文件行数与 1513 比较。
