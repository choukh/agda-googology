# 路线乙第四轮：原 Lgl 检查仍开放

**指定的 Shape 接线关闭；LevelNoK 候选未关闭。** 已按主审更正第三轮入口、
README 与 LOG 的范围。第三轮主定理只排除指定 Shape 接线，不能用来否定
原候选自己的 Lgl。本轮不改原定义，不换合法性标准；P1 仍为 **x = Ω·ω²**。

**实际路径上的局部事实（该子树即 ω）；第四轮 (a)/(b) 尚未交付。**
已对原 ψ₀Λ 实际路径上的该 ω 子树构造原 Goodᵁ，并证明计值后的原 Lgl。
主审第五轮复核指出：新信息只有该实际子树恰好是 ω；其合法性来自 ω 本身。
尚未判定整个初值，更未覆盖全部 gŝ 初始链点
及回灌。没有实际 Lgl 反例，也没有关闭候选的定理。

## 编译过的局部结果

实际路径仍是第三轮的原闭项，不是手造树或手填环境：

```text
LevelNoKFold.ψ₀Λ
  → 第 2 个 ℕ 分支的 ŝ 闭包
  → 初始反馈种子 actual-seed
  → 该种子的第 0 个 ℕ 分支
```

证明在 [自然数辅助](TreeLevels4Nat.lagda.md) 与 [实际子树](TreeLevels4SeedZero.lagda.md)。
最后这棵子树是一个完整的 ℕ 极限。TreeLevels4SeedZero 的 `actual-natural`
对每个 n 证明它的第 n 支去掉原包装后是 n 个后继；不是只检查前几个 n。
由此构造实际子树的原计值证书 `actual-seed-zero-good`，再证明
`actual-seed-zero-Lgl`：对任意层 k，原 rdR 读回原 forceᵁ 的结果满足原 Lgl。
主定理没有未知前提，不是假定整体 Goodᵁ 后投影其中的守卫。

| 项目 | 档次与范围 |
|---|---|
| TreeLevels4Nat：自然数形、重复加法及原计值的辅助引理 | 辅助证明，单独不计候选进展 |
| Box 与选择器的 read 相容定理 | 路径骨架；不生成环境或计值证书 |
| actual-natural、omega-origin | 原闭项上的全称自然数族与实际路径接线 |
| actual-seed-zero-good、actual-seed-zero-Lgl | **实际路径上的局部事实（该子树即 ω）**；不算种子第 0→1 步的进展 |
| 零或自然数的一般计值实例 | 只作辅助，不计新的候选强度 |

默认选择器的零结果不能满足 NatLimit 的 nat-limit 构造子；actual-natural
实填的是原运行中实际命中的 ol。没有靠默认值或不可满足的前提成立。
NatLimit 只描述这里需要的自然数形，不作为新的合法性标准；验收结论
直接写原 Lgl，计值仍用原 NoKCertEval，没有修补原输出的基本列。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsRound4 where

import OCF.Align.TreeLevels4Nat
import OCF.Align.TreeLevels4SeedZero
```

## 卡点与未完成范围

尚未证明整棵 actual-seed 有 Goodᵁ 和 Lgl，尤其尚无它的外层第 0 支到
第 1 支的字面 Cp 证据。因此不能把本轮子树的合法性外推为该初值合法，
也不能用单个初值外推全部 gŝ 链点、gĉ 高链或 goC.bodyG 的填表回灌闭包。

代码分析（**判断，未编译成整条迭代方程**）：这个初值来自实际 riseΩ。
内外折叠都以 U.zero 为目标类型，但内层用 tp 及 stChain，外层用 tn 0
及 stBody，地板由 trim / lowerSt 保留。把它们换成同一个纯树操作，或者
只证明与某棵合法模型结构互模拟，都还没有给出原 Lgl 所需的字面步进。
后续义务仍在原实际运行上，不是再给一个形状充分条件然后假定它成立。
目前没有证明必须修改原定义；没有以这个卡点要求作者放宽约束。

否定侧窄探针仅检查同族原 Ω₂+1 输入的有限读回与高链，在指定深宽内
未发现失败；尚未把该输入接成 ψ₀Λ 的实际路径，不计本轮候选进展。
既没有由此推出全 Lgl，也没有用旧 no-Lgl-Ωlim 的跨孩子手造形状替代
实际高链代表。第三轮 actual-bad-pair 仍只否定 Shape 的零支脊柱，
不提供本轮 Lgl 否定。

## 编译与约束

```text
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsRound4.lagda.md +RTS -M6G -RTS
```

具体实验及堆墙记录见 TreeLevels4SeedZero。所有正式结果均单路 6G 检查。
新增只在第 4 层；原树、折叠、Lgl、Shape 与 src / archive 均未修改。
本轮没有新闭项、值前沿或真实 ι。O8、O7、O5、O4 维持原状态，未再投入；
O8 仍为“未走通，未否定 SumOne”。没有提交或推送。


**复核。** 删除本轮 TreeLevels4Nat、TreeLevels4SeedZero 与汇总自身接口后，
经本入口单路 6G 冷编，三个模块全部重查，退出 0。已读定理与实际路径；
禁用构造、Funext / UIP / Un 前提扫描均为 0。源码导入闭包本地 18 模块，
记号禁用表命中 0；这只是第 4 层辅助结果的审计，不是完整成品认证。
默认 mapcheck、文章导航检查与 git diff --check 通过。
