# 以甲为脚手架完成乙：S1 第一轮

**档次：S1 的正面局部定理与骨架；完整 S1 未完成。**
按 [交接](../../Survey/Handoff-ScaffoldToTree-2026-11-08.md) 执行，
所有新增定义都在第 4 层探路，读记号，不进入乙线成品。
没有新 T甲、T乙、FGH 或序数值下界；没有进入 S2。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRound1 where

import OCF.Align.JiaBase
import OCF.Align.JiaFold
import OCF.Align.JiaAuditClosure
import OCF.Align.JiaChain
import OCF.Align.JiaChainTower
```

## 本轮得到什么

| 定理或定义 | 内容与档次 | 文件 |
|---|---|---|
| `Tree`, `coe` | 真实 EBO 码及标准形受限的可及层族；跨可及证明搬运，无 UIP。定义，不是正确 Ω 的存在性。 | [JiaBase](JiaBase.lagda.md) |
| `lift`, `regular`, `Fold.ψ` | 结构提升、后继层 Ω、带目标本层界的三路折叠。ψ 尚参数化于 Ω 种子。 | [JiaFold](JiaFold.lagda.md) |
| `no-direct-repeat` | 标准形输入不能直接再包 ψ；反例有同一码上界。只否定这个简化接口。 | [JiaAuditClosure](JiaAuditClosure.lagda.md) |
| `all-regular-normal` | 一切标准形 ν，正规 Ω_{ν+1} 的整个零起步码链均保持标准形。 | [JiaAuditClosure](JiaAuditClosure.lagda.md) |
| `zero-tower` | 任意 Ω 视图，若父折叠码标准形且目标层不高于共尾层，整个零起步码链均有 NF 与参数界不变量。 | [JiaChain](JiaChain.lagda.md) |
| `tower-zero-normal` | 上述条件在实际 Ω 塔全 k 实填；含奇异 Ω_Ω，非有限测试。 | [JiaChainTower](JiaChainTower.lagda.md) |

`zero-tower` 的条件不可省掉：父码 NF (ψ A B ∷ []) 包含
GB A B B，即从阈值 A 看得到的参数都在 B 之下。
前提的非空实例由 `tower-parent-normal`、`tower-view` 全塔构造给出，
不是假设一个未知候选已正确。

配对审查最初指出：正规 Ω 的零起步链删去初项后逐项等于记号链；
奇异 Ω_Ω 的零坐标给 1，不满足这条错位引理的前提。
主路随后以 `zero-tower` 直接处理奇异结点，不再依赖这个前提。
因此不能把零起点差异记成标准形封闭失败。

## 当前未接出的地方

树族中每个 Ω 结点的层号有标准形与本层界，**树本身尚未携带输出码**。
`Fold.ψ` 也未生产“输出树、标准形码、码树对应”的包。
`zero-tower` 的输入已经在码层，它不提供这个包，更不证明
code (ψ x) 就等于它处理的码链。

下一项实质义务是：让码树对应随 Ω、ψ 与反馈链的构造一起生成，
在奇异 Ω_Ω 的分支中把输入包送成 Ω 包，再沿所有 Ω 塔闭合。
这里须处理低层树作为新层号，不能给任意 raw 树事后补码。
后继层 `regular` 已写出，非正规层的 Ω 尚未写出；`Seeds` 的正确实例
因此未填。没有用恒零或恒 ω 的平凡实例冒充这项义务。

这是一处尚未完成的构造，不是编译过的不存在定理；
本轮没有实际链点封闭失败、必须使用 UIP、或闭项展开堆耗尽的结论。
不关闭 S1，不自行改线，也不把 `Comparison` 接口冒充实际比较清单。
T甲 的闭项、FGH、reference ≤ᵛ T甲 及运行中的比较清单全部待交。

## 翻译账与纲领

- `Layer.Tree` 仍只有零、后继、ℕ 极限、低层树分支的 Ω 极限；
  `Below` 的 NF 与码序字段是甲脚手架的代价，不能进入乙。
- ψ 的四种树情况及三路码派发来自 BTBO 范本；
  `zero-tower` 的 GB 不变量借用了记号侧封闭证明。
  这些都如实记为记号启发／依赖，不称树自足。
- 对所有 Ω 视图的一步不变量没有按站增加前提，但它只是码层结果；
  不等于乙线的阶段无关合法性或值定理已经完成。
- 本轮不改旧树、折叠、合法性定义。第 4 层逼出旧定义修改：零件。
- P1 仍为 x = Ω·ω²；S1 的局部定理不计入乙线值前沿。

## 复现与检查

从仓库根运行（库文件在仓库外，含 stdlib 与 cubical 路径）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/JiaRound1.lagda.md +RTS -M6G -RTS
```

五个数学模块删除各自接口后串行从头复核，汇总入口一同编译，退出 **0**。
源码代码块检查：无公设、洞、停机／正性绕过、trustMe，
没有 Funext、UIP 或 Un 前提。全部使用 --safe --without-K。
S1 主动导入 EBO 记号，导入闭包审计退出 **1**：本地 20 模块，
禁用表命中 EBO 一件，符合脚手架的已声明依赖；不通过成品标准。
没有使用失败编译轮的 HTML 或依赖切片。
导航检查本入口与 README 均为零问题，git diff --check 通过。

一次塔实例编译退出 42，原因是对未展开的塔别名直接使用非空列表
构造子的证明；显式给 `tower-positive` 后退出 0，属于陈述接线修正，
不是数学否定。配对审查初次编译退出 42 的 γ 视图转换也已用现成
`γ-eq` 修正。没有超时或堆耗尽。
