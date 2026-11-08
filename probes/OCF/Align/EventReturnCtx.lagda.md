# 迁回实验的统一保持与实际适用域

接续 [EventReturn](EventReturn.lagda.md)。本篇汇总后继结果，供接手与
复核使用；不改原树、折叠、读回、合法性或闭项。**没有新增序数强度，
也没有交出第三事件、全种类折叠或 ψ₀Λ 候选。**

## 已写出的定理

| 范围 | 实际陈述 | 仍需保留的条件 |
|---|---|---|
| [零层坐标](EventReturnCoordBuild.lagda.md) | E₀ 容许单侧迁移节点，原 drp 单侧保持；编码、和及部分和保持。 | 不从零层结果推断任意高阶回调相容。 |
| [原第一层 Int](EventReturnCtxBuild.lagda.md) | actual 实填 Internal；相关源、外回调和前缀经过原 Int 后仍相关，包含 ni 的内外递归及 nκ 的 Cut₀/IW₀。 | R₁、UH 是明写的前提；没有断言所有原始数据自相关。 |
| [第一层实际实例](EventReturnCtxActual.lagda.md) | 全 H₀ 编码源和前缀（含 Ω），以及原 Ωd one，实填 identity 外回调；单侧 drp₁ 后原 rd₁ 逐枝 Shape。 | 这是上述生成族，不是任意外回调。 |
| [同步事件后缀](EventReturnHistory.lagda.md) | 新增事件逐次同种类、payload Shape 的后缀可移植到新基底；全部实际 evx 观察坐标给出同步后缀。 | 可遗忘高事件的 HistLow 与同步 Suffix 不同；CutE 会逐事件执行回调，不能免费删去后缀中的执行。 |
| [第二层迁回观察](EventReturnCtxValueRun.lagda.md) | R₂ 在原 drp₂ 的单侧迁回下保持，原 rd₂ 给逐枝 Shape；包括两种 ni、nε κ₀ 与 nw。 | 消费 R₂，尚未证明完整原 Run/WalkE 生成 R₂。 |
| [第二层实例](EventReturnCtxValueActual.lagda.md) | 任意合法最高层及相应路径下，原 Act/Stp/Run n1 的第二层输出保持；有 κ₀ 闭包，回调执行原 Run n1，输出含 ni。 | Run n1 归约到动作一步，不递归处理任意源高节点；不是原 κ₁ 首格或整个运行的保持。 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtx where

import OCF.Align.EventReturnCoordIf
import OCF.Align.EventReturnCoordBuild
import OCF.Align.EventReturnCtxIf
import OCF.Align.EventReturnCtxBuild
import OCF.Align.EventReturnCtxActual
import OCF.Align.EventReturnHistory
import OCF.Align.EventReturnHistoryCompose
import OCF.Align.EventReturnCtxValueIf
import OCF.Align.EventReturnCtxValueRun
import OCF.Align.EventReturnCtxValueActual
```

## 完整运行之前不能跳过的检查

R₁ 的 ni 回调前提量化任意两份未来历史后缀（共享同一 A 路径与
合法证明）；R₂ 的回调前提只量化同步相关后缀，但其第一层坐标仍
消费 R₁。两种定义域不能混写。全编码实例证明了前提非空，**没有
证明完整实际运行产生的每个第一层坐标都落在这个域里**。
应沿原运行产生坐标与回调的地方核对，再决定是否使用这个关系；
冻结接口只是本实验的协作纪律，不是最终设计必须满足的纲领。

本轮继承 StrRel12Int.IntM、ValNewRel.Int-M 的关系保持与双递归机制；
新工作在原事件历史、移植和实际读回的适用域，不把旧原理算成新发现。
Shape 是读回后的逐枝关系，不是函数相等，也不能自动送进任意回调。

原双事件闭项的 1423 行语法切片尚不含新增高层内部 View；这些
关系定理没有进入其构造依赖，不能将新文件总行数直接加在该数字上，
也不能据此声称全种类候选能在标杆内完成。当前仍缺完整运行闭包、
结构参数统一的读回与迁回、所需内部 View 和终点 EBO 下界。
这是一组研究数据，不是选择该架构扩建到 Λ 的充分理由。
