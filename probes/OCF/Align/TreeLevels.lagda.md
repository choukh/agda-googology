# 路线乙：2026-11-08 首轮 O1 / O7

> 后续见 [第二轮](TreeLevelsRound2.lagda.md)：O1 收窄到 LevelNoK，O3 / O8 已开始；O7 暂停于真实合法共同界及方程运输桥。以下保留首轮记录。

本篇是第 4 层工作入口；导入记号，不进入成品。按
[交接文件](../../Survey/Handoff-TreeLevels-2026-11-08.md) 工作，P7 已经作者核对。
终点仍是一个不依赖记号的合法 `Cd` 闭项，其值无条件不低于 EBO 参照。
**本轮没有达到终点，没有新增值前沿。**

## 前沿核对的继承

P1 的指标仍是 **x = Ω·ω²**。已有 `EmbVVInstO2.vv-ω²` 的双向值验收；
`TreeEmitBuildAccept.closed-value` 给同值的树侧改写。
`CrossMHighSeedAccept.labelled-strict-lower` 已使高起点实例严格越过该行
一个后继，不使 P1 的 x 上升。这三项依作者已更新的交接记录继承，
本轮未重编它们；交接的单路 14G 配方仍适用。

## 编译过的结果与尚缺的实填

| 工作 | 已编译的陈述 | 当前边界 |
|---|---|---|
| O1 覆盖 | `Cover.terminal`；`Generated.terminal` | 两个一步律与全塔上界仍须实填；后者显式允许解释带生成域证据 |
| O1 链接口 | `Dom.limit-lower`；`Accept.terminal` | 草案只处理同一世界的一次调用；尚未适配真实跨世界回灌 |
| O1 可满足性 | `reference-via-chain` | 链接口、解释与全塔覆盖有共同实例，但实例是读记号的参照，不是候选 |
| O1 容量 | `complete-lower`；`round-lower`；`round-upper`；`no-legal-cap`；`no-A-cap` | 所有 `Cd` 可进入合法可数对象并保下界，或进入 `A` 并双向保值；不能仅凭最终容器类型否定候选 |
| O7 raw 扩张 | `total-ψ→WLPO`（ThreeEquations → Stage2.WLPO） | 只针对本轮明确给出的 raw Ω+1 扩张和字面方程；共同作用域尚无候选合法公共界的实现 |
| O7 相容性 | `cuts→equations`（Cuts → ThreeEquations） | 可判定切口下的相对实例；切口未无条件提供 |

O1 与 O7 都是**部分完成**。三个候选各自的真实折叠解释 ι 尚未定义，
未交出对这些 ι 的链支配与全塔覆盖；不能把泛条件定理或容器容量
当作这些义务已经满足。O7 尚缺合法公共界/内部 View 的桥，不能读作
一切写法 A 的总折叠都已否定，更不能否定带证据的生成域折叠。
O3、O8、O5、O4 本轮未开新数学模块。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels where

import OCF.Align.TreeLevelsO1Cover
import OCF.Align.TreeLevelsO1Chain
import OCF.Align.TreeLevelsO1Model
import OCF.Align.TreeLevelsO1Capacity
import OCF.Align.TreeLevelsO7
import OCF.Align.TreeLevelsO7Model
```

## 编译与审计

从仓库根目录运行：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevels.lagda.md +RTS -M6G -RTS
```

六个数学模块及本汇总入口均已退出 0；O7 两件由主审删其自身接口后重新编译，
退出 0，并核对陈述与证明。覆盖模块初次为隐式空类型推断报 42，
模型初次为空分支匹配报 42；均已修复，不用这些迭代报错判定路线。
安全扫描只读本轮 Agda 代码块：无公设、洞、信任原语或禁用检查指示，
没有函数外延、UIP 或 `Un` 前提。所有文件都在第 4 层，导入闭包含记号；
不做成品干净闭包的声明。

新增数学六件共 788 源码行、497 非空非注释代码行；首轮当时的入口另计 66 行/8 代码行。
这是本轮增量，未重算完整依赖成本，不能与 1513 跨口径比较。

**翻译账。** 没有新增生产节点、折叠、FGH 或证书，没有用验收便利
反改前三层。`Cover` 和参照实例明确读记号，仅用于检查第 4 层的
证明义务。`ChainDom` 的生成域与步进尚未对候选实填，因此不算树自足。
O7 的 raw W 扩张只用于检验方程的必要条件，不作为新候选交付。
