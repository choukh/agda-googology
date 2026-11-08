# 从实际事件回灌检验全种类读回：合同、编码与生成回调

本轮接续接手前的 EvFold/FamFold 实际回路，没有新建低站。
**结论：原全 H₀ 编码、一个真实 Int 生成者及观察新建事件的迁回
已有无外延的关系定理；全种类读回、第三事件和 ψ₀Λ 闭项仍未交付。**
本篇不是新强度验收，也不宣称现有双事件程序已经能够推广到 Λ。

## 方案评估与选择

在再次核查历史之后，对照了以下三种实现方向。它们不是穷尽分类，
也不是互斥方案；下列取舍是研究判断。

| 已有机制 | 继续使用前必须处理的实际问题 | 本轮取舍 |
|---|---|---|
| FamFold/EvFold 的真实输出读回与事件回灌 | FamFold 最终经固定 Ht；EvFold 的读回层和迁回按两种事件手写。需要统一 read/drop，并保持低事件与实际回调的意义。 | 选作决定性实验，先验证原迁回能保什么，不立即追加第三事件。 |
| Third 的树与路径同时输出 | 输入的未来世界 Gd 不能给普通 HB 输出分支的每个 raw 坐标补路径；Er、常值合法化和冻结世界是分别存在的损失。更换坐标域还需内部 View。 | 保留新合法化资产；不继续把 Gd 保持或全目标截面当唯一入口。 |
| GenFold 的一般 KS 运行器 | Run 本已量化未来世界；rd₁/rd₂ 的旧闭包取当前支，encH 取 Ω 底支，无 FBA 时重复当前支。只接增长世界不能改变这些方程。 | 继承其一般节点递归，暂不叠用整套后端。 |

通向终点的候选数据流仍应是：高层输入经同一运行器产生读回，
读回进入该种类自己的坐标类型，新增事件后继续实际分支，最后观察为
合法可数树与 FGH；中途不统一下降到固定 Ht。序数值验收可错位、
多步覆盖参照塔，不要求记号基本列逐项相同。
这是一条充分策略的设计方向，尚未证明能覆盖 EBO。

## 本轮实际交付

| 件 | 编译陈述与实例 | 边界 |
|---|---|---|
| [最小合同](EventReturnIf.lagda.md) 与 [原实例](EventReturnBuild.lagda.md) | 两种 ReturnAt 的 read/event 逐字绑定原 RB/evRB；move 的目标、读回层同在合法 Λ 内。 | 校准已有构造；没有值保持字段，不算新算法。 |
| [编码](EventReturnCodeBuild.lagda.md) | encoded-readback 对全部原 H₀ 输入（含 Ω），给原 drp₁/toD₁ 经原 rd₁ 读回后的逐枝 Shape。 | 不是数据函数的命题等式，不能送入任意 continuation。 |
| [实际 Int 节点](EventReturnInt.lagda.md) 与 [读回](EventReturnIntRead.lagda.md) | node-related 包含真实的低层 Int 与 nw 前缀；whole 是原 Int(Ωd one)。whole-encoded-observed 对全部 H₀ 编码输入成立。 | 只实填这个生成者；没有任意 Int 源的完整保持。migrate 仅双侧迁回，不是单侧相干。 |
| [真实首格](EventReturnValueCell.lagda.md) | 原 κ₁ 首格、原 Y₀⊕Stp Y₀、κ₀ 零分支闭包；合同 move 前后 rd₂ 对所有起始值字面相等，且首事件含 σH。 | 一个具体运行实例，不能当作全部 κ₀ 分支的自然性。 |
| [观察事件配对](EventReturnValueEvent.lagda.md) 与 [原重放器](EventReturnReplay.lagda.md) | 全部 H₀ 观察坐标上的原 evx 成对；HistLow 确实推出原 rp 的低界 Shape，且在真实首格及其每个 H₀ 观察坐标接一次 evx 的实例中实填。 | 没有把 Shape 当事件相等，也没有从 HistLow 推出任意原 u 保持。 |
| [零层](EventReturnValueZero.lagda.md) | 原 EvFold 数据的迁回保全部基本列双模拟与双向值界。 | 旧 SumOne/HtVal 已有同机制；这里只做数据族校准。 |
| [后继分支](EventReturnValueStep.lagda.md) | 保存原 κ₀ 内枝为 n1 的 κ₁ 首格输出。 | 迁回读回等式用 refl 的尝试退出 42；该等式未证未否，不作完成结果。 |

本轮的一般证明覆盖全输入族；具体首格等式则明确只针对原闭项的
那次调用。两类都不是用有限展开样本估计强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturn where

import OCF.Align.EventReturnIf
import OCF.Align.EventReturnBuild
import OCF.Align.EventReturnCodeIf
import OCF.Align.EventReturnCodeBuild
import OCF.Align.EventReturnInt
import OCF.Align.EventReturnIntRead
import OCF.Align.EventReturnValueZero
import OCF.Align.EventReturnValueCell
import OCF.Align.EventReturnValueEvent
import OCF.Align.EventReturnValueStep
import OCF.Align.EventReturnReplay
```

## 继承账与下一验收点

Ctx、事件重放、真实回灌、结构迁回和 Int 的双递归机制都已有历史
前例。StrRel12Int.IntM 已处理两世界、不同节点位置和内外 Int；
ValNewRel.Int-M 本身也没有 NI 前提。此次没有把它们重新命名成新原理。
新增的是把关系实填到原 EvFold 的编码、实际生成者与事件历史上。

下一决定性验收点是原 Int/Run 对**相关事件历史、相关坐标及前缀**
的保持，特别是 nε 的 IWε/CutE 和读回再次生成 evx 的配对。
不能先要求任意两个历史上的回调无条件相容，再只交零函数实例。
也不能把只允许双侧 nw 的关系当单侧迁回已经闭合。

更强的全种类 ReturnAt 尚须由结构递归产生，不能永久留作模块参数。
内部 View 与终点 EBO 下界仍是独立交付；本轮没有新 ψ₀(Ω_x) 强度。

## 成本校准与翻译账

主审对原 EvFoldClosed 成功生成 HTML 与编译器依赖图，再用
[切片脚本](../../Survey/scripts/eventreturn/locslice_eventreturn.py) 计算。
脚本对可达本地模块的全部模块别名补根，不按模块名排除本地代码；
标准库按既有标杆口径不计。结果是语法切片近似：

- 原两种读回、合法性及迁回：784 行。
- 原双事件闭项 T-Ω₃²、合法性及 FGH：1423 行。

1423 尚不含新增高层内部 View；不能据此称完整纲领已满足，也不能
将新增关系文件的行数叠在它上面后称全种类成品仍低于 1513。
这些证据要求统一实现能够替换旧重复，而不是继续逐事件增加手写行。
没有可靠的全种类成品成本估计。

本轮未增加定义中的树节点、记号阶段字段或专属闭包前提。
Shape、Code、R、HistLow 属研究关系，不进入原树、折叠与证书；
ReturnAt 绑定现有算法，不决定新算法。没有因验收方便反改旧定义。
这属于摆脱侧的结构检验，尚未提供开启新攀爬站的全种类一步定理。

## 本轮复核

主审只删除本轮 12 个新模块自己的接口，再以单路 6G 冷编入口，
退出 0；核对了陈述与代码，代码块中禁用构造、Funext/UIP 命中 0。
独立读审确认了双侧迁回、具体首格与相关历史的范围。
源码导入闭包 70 模块（本地 58），编译器图 203 模块（本地 58），
两者记号禁用表命中均为 0。关键定理的定义切片记号块与记号词均为 0；
本轮未新跑切片正对照，依赖独立性主要由成功编译的完整导入闭包保证。
这些检查没有证明规则已树自足，亦未提供 EBO 的值下界。
