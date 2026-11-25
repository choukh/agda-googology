# 甲脚手架第三轮：分层 Rep 可定义，逐 fsn 的 ψ 保持被限定否定

**档次：正面关系定义与实例，加编译过的限定否定。**
树族、Ω 的全 raw 分支域及原 ψ 完全不动；没有给原始树补码。
Rep 的 Ω 子句通过正性与宇宙检查，搬运不需要 UIP 或函数外延。

本轮将“ℕ 极限逐构造子对应”具体实现成与原 EBO 的 fsn **逐项**对应。
下面的否定仅针对这个明确的实现，且带零层种子为 1 的条件。
它没有否定允许不同共尾基本列的关系式设计，也没有否定原树的值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRound3 where

import OCF.Align.JiaRep
import OCF.Align.JiaRepMove
import OCF.Align.JiaRepNamed
import OCF.Align.JiaRepOmega
import OCF.Align.JiaRepAuditBare
import OCF.Align.JiaRepAuditOne
import OCF.Align.JiaRepNoPreservation
```

## 已编译的正面结果

| 定理或定义 | 范围 | 文件 |
|---|---|---|
| `Rep`, `RelLayer.Rel` | 沿原 Acc 分层的归纳关系，四种树情况；Ω 子句只消费相关输入 | [JiaRep](JiaRep.lagda.md) |
| `rep-coe`, `rep-lift` | 跨可及证明搬运及原提升保持同一码的对应，无 UIP | [JiaRepMove](JiaRepMove.lagda.md) |
| `named-rep` | 第二轮已携码的可数输入确是此关系的实例 | [JiaRepNamed](JiaRepNamed.lagda.md) |
| `rep-regular` | 一切标准形后继层号的原正规 Ω，分支域不改 | [JiaRepOmega](JiaRepOmega.lagda.md) |
| `omega-rep`, `branch-rep` | 第二轮沿 Named 构造的 Ω 及其分支输出确有 Rep，而不只是来源记录 | [JiaRepOmega](JiaRepOmega.lagda.md) |

Ω 子句中，低层关系先于本层定义，以参数形式进入本层。
它的前件是“已有的低层 Rep”，不是从 raw 输入计算码的函数。
原函数 f 仍对全部低层树有定义；关系只约束已经相关的输入。
本轮没有给原树添加字段或构造子。

这些 Ω 实例还没有把奇异 Ω_Ω 的全 raw 分支程序接出。
`branch-rep` 的输入仍是已有的 Named；没有偷偷把它当作所有 raw 输入。

## ψ 保持的精确反例

**编译定理 `no-code-for-regular`：** 对任意种子族与可及证明，
若当前目标零层种子字面为 1，则原最小正规 Ω 经原 ψ 折叠后的树，
对每一个原 EBO 裸项类型 T 中的码，都不满足本轮逐 fsn 的 Rep。
此结论不要求输出码标准形，已经覆盖所有 T 码。
见 [JiaRepAuditOne](JiaRepAuditOne.lagda.md)。

**编译定理 `no-preservation`：** 同样的种子条件下，不存在任何
码侧运算 codeFold : T → T，使 ψ 在标准形码的相关输入上保持此 Rep。
这已经弱于作者提出的全保持义务。
见 [JiaRepNoPreservation](JiaRepNoPreservation.lagda.md)。

这两个否定不是空前提：

- 源树就是原第 1 层的 `regular`，原全分支域保留。
  源码的标准形由 `regular-normal` 给出，输入关系由 `rep-regular` 给出。
- `one-seeds`、`one-seeds-zero` 实填零层种子为 1 的条件。
  它们只证明此条件可满足，不声称高层 Ω 种子已正确。
- 任意可及证明都是定理的参数；规范实例可由原 `wf` 得到。

否定的机制如下，这是全称分类证明，不是有限样本测试：

1. 原最小正规 Ω 在原 ψ 中走 eq 分支，即从零起步的 lfp。
   零层种子为 1 时，其根第 0、1、2 项分别是零、1、ℕ 极限。
2. 对任何 ω 共尾码，若第 0 基本列项为空，现成 `Vω` 视图的全部
   构造子分类证明它只能走“复制 n 次”规则。
3. 第 1 树支为 1，迫使被复制的码为 1；因此第 2 码项为 2。
   第 2 树支却是 ℕ 极限，不能与后继码 2 满足本轮 Rep。

所以失败不靠猜测 ψᶜ 的形式；`no-preservation` 对所有 codeFold 量化。
零层种子为 1 是定理的条件，不能删掉写成对所有种子的结论。

另有较窄的 `no-bare-regular`：对所有种子，裸码 ψ₀(Ω) 与原树侧
根第 0 项不对应，见 [JiaRepAuditBare](JiaRepAuditBare.lagda.md)。
它只否定裸 ψ 的选择；强结论另用了明确的零层种子条件。

## 边界与本轮停点

本轮没有遇到正性／宇宙问题、需要 UIP、raw 补码或修改树族的情形。
现在的结果是当前 ℕ 子句的编译反例，不能报告成 Ω 子句或 raw 分支域的失败。
也不因这个反例关闭作者选定的关系式路线。

本轮没有自行放宽已固定关系的 ℕ 子句，没有改基本列、原 ψ 或树形状。
若改用允许基本列不同的关系，还需重新写明含义与证明；本轮未完成它。
泛 ψ 保持与奇异 Ω_Ω 全 raw 接线尚未交付。
T甲、FGH、终点值下界、S2 比较清单也未交付；P1 仍为 x = Ω·ω²。

## 复现与审查

从仓库根：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/JiaRound3.lagda.md +RTS -M6G -RTS
```

七件数学模块删除各自接口，经新入口串行冷编，八件全部 Checking，退出 **0**。
原依赖使用已有接口，不使用 ignore-interfaces；全部 safe、without-K。
公设、洞、停机／正性绕过、trustMe、Funext／UIP／Un 前提检查均为零。
没有失败轮 HTML 或依赖切片，没有超时或堆耗尽。

配对审查提供两个限定否定，主路核对陈述、证明与条件实例并冷编复核后采用。
初次编译中的隐参名字、漏导入及可及参数未展开问题都已修正；
后者通过对一般可及证明写 coe／lift 的零与 1 等式解决，不比较证明相等。
