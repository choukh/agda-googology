# YiWall：K2′ 的字面相等与起点守卫障碍

对纲领与目标：本轮把两个卡点分开了，但**没有证明原块上 FoldRows0
必须假定 Funext，也没有无条件否定只读树的 ψ**。前者目前只有同树列
换证书的窄函数等式；后者得到一个明标条件的 WLPO 障碍。
不改树、合法性、证书或冻结接口，不修补折叠，不关闭乙线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiWall where

import OCF.Align.YiWallLim
import OCF.Align.YiWallTree
import OCF.Align.YiWallConditional
```

## 1. 极限行：编译到了窄实例，未推出完整 Funext

[Lim](YiWallLim.lagda.md) 的 `LimPosition` 精确保留旧 FoldRows0 的极限行
和有界位置保持两字段，没有缩小这两条律的定义域。`Required.sequence`
证明：固定同一合法 LF 列 f，任意两套 Carry／Legal／Only0 及步进证书
经同一 eval 所得的两个 `ℕ → Raw zero` 函数相等。
公共界是合法的 `lim f` 本身；逐项相等另由 `Required.pointwise` 给出。

`actual-sequences` 对任意 `α β : ℕ → ℕ` 实例化到 YiK2cIrr 的真实分支源，
α 恒 0、β 恒 1 时每个位置的 Source 确实不同，底层树则相同。
这是一项关于实际输出函数的必要等式，范围仍与旧
`lim-function-equality-required` 相同，没有把它推广成任意函数外延。

**前提可满足性（编译）。** `cut-instance` 实填这两字段；它沿原第一支
裁去 lc，换证书的函数等式直接为 refl。它只用来证最小前提非空，
故意不满足 gt，不是实现修补或完整 ψ。原完整记录仍未实填。

**判断／未证。** 当前论证只能使用同一个 f。由任意两列的逐点相等
得到两个 LF 极限相等，恰是字面位置律没有提供的桥梁；没有证明
该桥梁必不可得，也没有证明完整 FoldRows0 蕴涵一般 Funext。

## 2. 只读树：两个恒分支 gt 检验加空域相等推出 WLPO

[Tree](YiWallTree.lagda.md) 的 `start-iff` 对所有层参数证明：
有原守卫坐标当且仅当下界 Lgl。`node-source` 为任何合法 Raw 0 下界
实填原 Carry／Legal／Only0；分支分别恒 1 或恒 2，第一支同为 1。
这避开了“实际证书不同”与“树不同”的混淆，两根的 irr 都是 refl。
`from-fold` 从满足字面因子分解 `ψ = run ∘ term ∘ original` 的完整目标
抽出 `ProbeRows`，即 1、2 的行及这两个恒分支 gt 行。
它只是目标接口的必要投影，不作完整目标非空的证据。

[Conditional](YiWallConditional.lagda.md) 编译了以下陈述：

| 档位 | 定理及精确前提 |
|---|---|
| 编译定理 | `probes→weak-lgl`：ProbeRows 加 EmptyAgreement（非法下界的两个空域根读数相等），给每个下界“非合法或非非合法” |
| 编译定理 | `all→legal`、`legal→all`：交错列 `1, flag(α 0), 1, flag(α 1), …` 的合法性恰等于布尔列 α 全 false |
| 编译定理 | `probes-empty→wlpo`：上述两项前提推出 WLPO，即任意布尔列“全 false 或并非全 false” |
| **条件** | `funext-probes→wlpo`：Funext 加 ProbeRows 推出 WLPO；Funext 仅用于证明空域上两个整分支函数相等 |
| **条件／目标推论** | `funext-fold-tree→wlpo`：Funext 加满足字面只读树分解的 FoldRows0 推出 WLPO；不声称这个完整目标已可满足 |

**前提可满足性。** 恒 false、恒 true 的下界分别有编译的 `encoded-good`
和 `encoded-bad`，合法下界的两个源都有闭证书。最小全域 ProbeRows、
EmptyAgreement、Funext 可同时成立的经典外延解释说明见条件篇，
明确是纸面档，不冒充无公理的 Agda 实现。完整 FoldRows0 只是被检验的
目标，不拿它作附加背景前提或可满足性证据。

**判断／未证。** 不加 EmptyAgreement 或 Funext 时，尚未从只读树与
gt 行推出 WLPO。非法下界时，两分支函数逐点相等，但原 irr 不提供
整函数相等，无法令任意 run 的两个根读数相等；这正是本证明的止点。
既没有“所有只读树 ψ 不存在”的定理，也没有由起点缺失直接否定
Carry 域：起点的合法性证据在该域恰好可由 Carry 投影。

## 3. “条件”标记的准确范围

主审所说“沿原块 FoldRows0 走就要以 Funext 为前提”目前仍未证，
不能凭窄外延实例把它升级为定理。**实际以 Funext 为前提的本轮结果
一律标“条件”**；Funext 仅命名一种前提类型，没有该类型的闭项，
没有进入成品、证书、旧定义或旧接口。本轮无有限测试，没有新序数值界。

翻译账：新增的是冻结接口的必要投影、一个最小接口的非空对照及两个
恒分支的障碍定理；没有新树节点、阶段字段、记号规则或第 4 层反逼。
极限侧只用原字面公共界，守卫侧只判定有限布尔观测；无裸下标比较。
无记号引用不等于已经让树自足，本轮没有作此声称。

## 冷编清单与审计（2026-11-10）

| 模块 | 只删自身接口后检查 | 堆上限 | 退出码 | 目标 Checking |
|---|---|---|---|---|
| YiWallLim | 是 | 6G | 0 | 有 |
| YiWallTree | 是 | 6G | 0 | 有 |
| YiWallConditional | 是 | 6G | 0 | 有 |
| YiWall | 是 | 6G | 0 | 有 |

从仓库根单路顺序执行，依赖取缓存；不声称整个闭包冷编，未使用
ignore-interfaces，未删旧接口。每个退出码由进程直接读取，不经过管道。
每件的复现配方（替换文件名，库文件含 stdlib 与 cubical）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiWall.lagda.md +RTS -M6G -RTS
```

开发有两次退出 42：窄实例的隐式证书函数类型未标全，以及 Tree 篇多了
一个括号；补全类型、改正括号后通过，均非数学否定。正式冷编无
42／251／124。四次成功冷编同时生成 HTML 与各自的编译器依赖图。

- 四件均 safe／without-K／lossy-unification；代码无公设、洞、停机或
  正性逃生、信任相等、开启 K。Funext 仅在 Conditional 的前提类型中，
  没有外延证明的闭项；其他三件代码中没有该名字。无绝对路径或尾随空白。
- importclosure 的完整白名单为 OCF.Align.Yi、OCF.Align.RR4RegOmega2、
  OCF.Align.RR4CoordRoot、OCF.Align.LevelFix、OCF.Free.Level、OCF.BTBO。
  Lim／Tree／Conditional／入口的源码本地闭包为 25／26／27／29，
  库叶为 19／20／23／23；禁用表与白名单外均 0，无记号或 C 线。
  成功编译器图的本地集合逐一相等，总模块数为 170／171／173／175。
- 成功 HTML 切片（到达块数／记号块／记号词）：sequence 63／0／0，
  actual-sequences 88／0／0，cut-instance 61／0／0，start-iff 26／0／0，
  from-fold 78／0／0，funext→empty-agreement 32／0／0，
  probes-empty→wlpo 56／0／0，funext-probes→wlpo 62／0／0，
  all→legal 与 legal→all 均 30／0／0。正对照 EboLean3Lab.ebo-lab″
  另以单路 6G 成功生成 HTML，切片为 352／33／36，未进入本轮导入闭包。
  切片为语法近似，不替代陈述、隐式参数或前提核对。
- 开工快照的 119 件既有 Yi*／LevelFix* 数学文件字节摘要未变。
  数学文件只新增本轮四件；README 与 LOG 只补记，不改旧结论。
  没有改 src／archive，没有安装包、提交或推送。
