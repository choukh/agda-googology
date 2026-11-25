# 路线乙第三轮：指定的 Shape 接线关闭；LevelNoK 候选未关闭

**交付 (b)：指定的 Shape 接线关闭；LevelNoK 候选未关闭。**
否定针对原 `ψ₀Λ` 的实际运行，不是任意 raw 反例或手工环境。
没有改原树、折叠、合法性或 Shape。P1 仍为 **x = Ω·ω²**。

关闭的精确范围是：沿原 `Goodᵁ` 计值规则，使实际反馈初值具有第二轮
指定的 Shape（即使允许原规则中的结构互模拟代表）。本轮不证明
原候选没有任何其它合法性证书，不给原树的序数值上界，也不否定
仅值相同但基本列不同的重写。主审第四轮已更正此前“候选关闭”的范围，
并指定直接检查原 Lgl；不经 Shape，不改原定义。

## 实际反例与原因

1. `whole-origin` 证明 `whole` 就是原 `LevelNoKFold.ψ₀Λ` 的只读像。
2. 沿原树的 ℕ 极限第 2 支，实际到达 `ŝ` 闭包，再取其初始反馈种子。
   两个构造子均有检查器认可的见证，不依赖选择器的默认零值。
3. 该种子是极限；其前两支又都是极限，第零项分别是 0 和 1。
4. 差树追加的原 Shape 额外要求相邻极限分支只沿**第 0 支脊柱**相接。
   上面这两个实际分支不能这样相接。

这不是对原 `Lgl` 的否定。`Lgl` 的字面第一位置允许走极限的其它
有限支；原 Shape 所定义的追加作用比这个条件更强。反例也不是
“所有 Shape 的首项是零”——那句话是假的，任意起点都可追加。
用到的全称不变量是 `shape→spine`，不把比它更强的纸面判断当定理。

## 定理与交付档次

| 内容 | 结果 | 档次 |
|---|---|---|
| 指定形状的不变量 | `shape→spine` | 全称结构定理 |
| 原闭项的实际路径与头部 | `whole-origin`、`branch-is-self-closure`、`actual-bad-pair` | 编译等式与构造子见证；用于一个具体反例，不是强度抽样 |
| 原实际反馈不能有该形状 | `no-shape-realisation`、`no-shape-representative` | 实际种子的联合计值 / Shape 否定，亦排除结构互模拟代表 |
| 反馈闭包必要子合同 | `SeedOf`、`FeedbackShapeClosure`、`FeedbackShapeRepresentatives` | 骨架；没有冒充完整 Env t |
| 原闭项证书的直接否定 | `no-original-good-with-shaped-initials` | **实质否定**：连原计值证书的弱初值 Shape 要求都无法满足 |
| 零初值实例 | `zero-good-with-shaped-initials` 及零闭包子合同实例 | 仅认证条件可满足，不计候选进展 |

主定理的弱要求 `ShapedInitials` 只约束普通 ℕ 分支到达的 `gŝ` 初始
链点 ys 0，不要求其后所有链点或所有高层 `gĉ` 都有 Shape。
原规则允许 forceᵁ seed G₀ ≅ ys 0；否定在结构互模拟下仍成立，
所以不能通过选择另一个这种代表填回证书。
主定理是原闭项上的无额外前提否定，不是假定整棵树已能计值后
再用未知的计值前提冒充实例。实际输入由原 `Legal-Λ` 支持；
合同自身的非空实例另行实填。

因此不再先铺完整 Env t 或真实 ι：本轮要求它们必须接上的 Shape
必要条件已经失败。真实 ι、ι-suc、ι-lim 均未交付；没有把
这条指定合同的否定说成所有可能解释都不可能。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsRound3 where

import OCF.Align.TreeLevels3EnvContract
import OCF.Align.TreeLevels3FeedbackSpine
import OCF.Align.TreeLevels3FeedbackShape
import OCF.Align.TreeLevels3ClosureNeg
```

## 其它路线与杂事

O8 的两天上限已到，**未走通，未否定 SumOne**。止点仍是实际状态
`Y₁` 没有旧 `Inv`；所求上界需要覆盖含 `nκ` 状态的单向值模拟。
本轮未再投入 O8，也没有提出新方案后直接做。O7 维持暂停，O5 / O4
维持暂缓；没有铺另两个候选。

仓库根的空目录 .scratch/treelevels-root/ 及其空父目录已经删除。
库文件在仓库外临时目录，文中编译命令只用占位符。

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsRound3.lagda.md +RTS -M6G -RTS
```

本轮没有新闭项或值前沿；新增都在第 4 层。反例与不变量不引用记号，
不以基本列标签验收。第三轮在指定 Shape 接线的编译否定处停止；
第四轮直接检查原 Lgl，候选本身仍开放。


**复核。** 四个数学模块及本入口删自身接口后的单路 6G 冷编全部重查，
退出 0。已读原始陈述、实际路径与证明，禁用构造 / Funext / UIP / Un
前提检查均为 0；源码导入闭包本地 18 模块，禁用表命中 0。
首次透明展开版本的 251 已按堆墙记录，不当作类型错误或通过。
数学四件共 479 源码行 / 276 非空非注释 Agda 代码行，汇总另计；
这不是完整依赖成本，不与 1513 跨口径比较。
