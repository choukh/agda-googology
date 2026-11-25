# 路线乙第五轮：结果 (c)，在实际种子第 0→1 步暂停

**结果 (c)：未得到原 Cp，也未证明它不存在；乙线按作者本轮决定暂停。**
暂停点只在原 LevelNoKFold.ψ₀Λ 实际路径的 actual-seed 第 0 支与第 1 支。
LevelNoK 候选未关闭。指定 Shape 接线的否定仍只否定该接线，不能用来
回答本轮原 Lgl 的第一步。P1 仍为 **x = Ω·ω²**。

第四轮入口、README、LOG 已按主审更正档次：actual-seed-zero-Lgl 是
**实际路径上的局部事实（该子树即 ω）**。它没有提供第 0→1 步，
本轮不把它称为实质合法性进展。没有修改原树、折叠、Lgl 或 Shape。

## 精确停止点

[单点陈述](TreeLevels5Point.lagda.md)只用原 actual-seed 定义两支：

```text
left  = lim-at actual-seed 0
right = lim-at actual-seed 1
FirstStep = Σ (Goodᵁ left) λ G₀ → Σ (Goodᵁ right) λ G₁ →
  Cp zero (rdR zero (forceᵁ left G₀))
          (rdR zero (forceᵁ right G₁)).
```

`FirstStep` 已编译为原单点的目标类型，**没有构造它的项**。其中两份
原计值证书均存在量化；没有强迫只能用第四轮构造的左证书。
已知的 `left-good` 只是一个左证书；右证书与 Cp 均未交付。
没有以原整体 Goodᵁ 或 Lgl 为已满足的未知前提。

选择右侧极限的有限支 1 时，还需要以下字面等式：

```text
rdR zero (forceᵁ left G₀) ≡
rdR zero (forceᵁ (lim-at right 1) (right-child-good G₁)).
```

这就是 `OneEquality` 在第 0 层的实例。`step-from-one` 编译了“若有该
等号与两份计值证书，则由原 Dn 的支 1 构造原 Cp”的接线；本篇没有
提供其实际前提，不计候选进展。它不是必要条件：原 Cp 仍允许自身相等
与其它任何有限支。因此选支 1 的尝试失败不能推出 Cp 不存在。

## 编译错误原文

下面是仓库外失败实验的完整源码，按 text 保留，不进入入口的 Agda
代码块或导入闭包。签名暂把尚未构造的右证书作为变量，只为暴露 Cp
构造还缺的字面等式；没有冒称此变量已有实际实例，也没有将这个更强
尝试的失败说成 FirstStep 不存在。

```text
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns --lossy-unification -W noUnsupportedIndexedMatch #-}
module R5Attempt where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.NoKCertEval as E
import OCF.Align.TreeLevels5Point as P
try-cp : (G₁ : E.Goodᵁ P.right) → P.StepAt LF.zero
try-cp G₁ = P.step-from-one LF.zero P.left-good G₁ refl
```

单路 6G 编译退出 **42**，完整输出：

```text
Checking R5Attempt (<实验目录>/R5Attempt.agda).
<实验目录>/R5Attempt.agda:8.52-56: error: [UnequalTerms]
(OCF.Align.TreeLevels3FeedbackSpine.first
 (OCF.Align.TreeLevels3FeedbackSpine.lim-at
  OCF.Align.TreeLevels3FeedbackShape.whole 2))
!=
(OCF.Align.TreeLevels3FeedbackSpine.lim-at
 (OCF.Align.TreeLevels3FeedbackSpine.first
  (OCF.Align.TreeLevels3FeedbackSpine.lim-at
   OCF.Align.TreeLevels3FeedbackShape.whole 2))
 1)
of type E.Zᵁ
when checking that the expression refl has type
P.OneEquality LF.zero P.left-good G₁
```

这里保留了先前用于封住大闭项的 opaque 边界。这条报错只说明上述
`refl` 直接填充没有通过；**不是两棵实际树不相等的定理**，更不是
所有有限支均无 Cp 的证明。随后解除 opaque 的实际展开实验另行记录，
不以这条 42 独自支持“必须改定义”或“必须加函数外延”。


### 解除 opaque 的同一 Cp 尝试

完整实验源码：

```text
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns --lossy-unification -W noUnsupportedIndexedMatch #-}
module R5Unfold where
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.NoKCertEval as E
import OCF.Align.TreeLevels5Point as P
import OCF.Align.TreeLevels4SeedZero as M
import OCF.Align.TreeLevels3FeedbackShape as A
opaque
  unfolding A.whole A.whole-origin M.whole M.origin M.actual-natural
  try-cp : (G₁ : E.Goodᵁ P.right) → P.StepAt LF.zero
  try-cp G₁ = P.step-from-one LF.zero P.left-good G₁ refl
```

单路 6G，180 秒超时，退出 **124**。完整标准输出只有：

```text
Checking R5Unfold (<实验目录>/R5Unfold.agda).
```

这是运行资源止点，无类型通过或类型否定结论。

### 右支第 1 项的辅助具体展开

为给上述选支 1 的路线定位实际右侧子项，尝试直接填其 NatLimit。
下面的对象仍来自同一个原实际种子，不是手造模型。这是该 Cp 尝试的
辅助展开，不是其它反馈链点；即使它编译成功，也仍不能替代所需 Cp。
完整失败源码：

```text
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns --lossy-unification #-}
module R5Point where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import OCF.Align.TreeLevels4SeedZero as M
import OCF.Align.TreeLevels4Nat as N
import OCF.Align.TreeLevels3FeedbackShape as A
import OCF.Align.NoKCertEval as E
import OCF.Align.LevelNoKFold as O
open import OCF.Align.LevelNoKU using (module U)
rightOneBox : M.Box
rightOneBox = M.core (M.branch 1 (M.branch 1 (M.initial (M.branch 2 M.whole))))
right-origin : M.read rightOneBox ≡ A.lim-at (A.lim-at A.actual-seed 1) 1
right-origin = trans (M.read-core _) (trans (M.read-branch 1 _)
  (cong (λ x → A.lim-at x 1) (trans (M.read-branch 1 _)
  (cong (λ x → A.lim-at x 1) (trans (M.read-initial _)
  (cong A.first (trans (M.read-branch 2 _) (cong (λ x → A.lim-at x 2) M.origin))))))))
opaque
  unfolding M.whole
  right-natural : M.NatLimit rightOneBox
  right-natural = M.nat-limit {π = M.floor rightOneBox}
    {f = λ n → O.TT.repᵒ (M.one {M.floor rightOneBox}) n}
    (λ n → N.rn-rep {π = M.floor rightOneBox} {x = M.one {M.floor rightOneBox}} (N.rw _ (N.rs N.r0)) n)
```

该辅助展开单路 6G 退出 **251**；没有其它 Agda 同时运行时再试 14G，
仍退出 **251**。两次完整输出分别是：

```text
Checking R5Point (<实验目录>/R5Point.agda).
 Checking OCF.Align.TreeLevels4SeedZero (<仓库>/probes/OCF/Align/TreeLevels4SeedZero.lagda.md).
agda: Heap exhausted;
agda: Current maximum heap size is 6442450944 bytes (6144 MB).
agda: Use `+RTS -M<size>' to increase it.
```

```text
Checking R5Point (<实验目录>/R5Point.agda).
agda: Heap exhausted;
agda: Current maximum heap size is 15032385536 bytes (14336 MB).
agda: Use `+RTS -M<size>' to increase it.
```

堆耗尽不证明反例。没有使用这些失败轮的 html 或依赖切片，没有用
这组辅助实验声称右支已经有 Goodᵁ、或声称相邻步进不可能。

## 内外折叠的可编译公式

[状态公式](TreeLevels5Rise.lagda.md)固定原源层 C = toU Λ 及位置
r = lim 2 (fst zero)，保留原参数 st / h。令 M = trim π st {r} tt、
ξ = ξᵗ M：

```text
I(z) = ψ ∅ (tp r tt) (stChain ξ (bkᵗ M) (wkᵗ M) st) (h ξ z)
O(z) = ψ ∅ (tn 0)    (stBody  ξ (wkᵗ M) st)         (h ξ z)
z₀   = owk {π = tz} {ρ = ξ} (λ ()) (os o0)
z₁   = I(z₀)
ψ ∅ (tn 0) st (oΩ r tt h) = ol (λ n → O(chain M n)).
```

`At.rise-equation` 编译了最后这条原运算等式；`chain-zero`、`chain-one`
也已编译。内层状态的类型为 St ∅ ξ (ξ ∪ π)，外层为
St ∅ ρ (ξ ∪ π)。此节点的首步要比较 O(z₀) 与 O(I(z₀)) 的原计值读回。
没有删除这些参数，也没有把两个原函数当作一个纯树操作。

**范围。** 这个固定源层/位置上的公式对原参数成立；它没有编译出
整棵 actual-seed 与一个简化模型的等式，也没有复原到达节点前全部
包装生成的 st / h 的闭表达式。本轮把第四轮的“错位”写成了这些
精确类型与公式，**没有证明它是唯一卡点或已导致数学否定**。
实际 Cp 的目标始终是上面直接取自原 actual-seed 的 FirstStep。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsRound5 where

import OCF.Align.TreeLevels5Point
import OCF.Align.TreeLevels5Rise
```

## 暂停记录

| 已有 | 范围 |
|---|---|
| 第三轮 Shape 接线否定 | 实际种子不能满足指定 Shape；不否定原 Lgl |
| 第四轮 actual-natural / actual-seed-zero-Lgl | 实际路径上的局部事实：第零支即 ω，因而合法 |
| 第五轮 FirstStep、原构造子接线、rise-equation | 目标与运算公式；骨架/诊断，没有新的实际 Cp 或否定 |

**未决问题只有本轮单点：** 是否能为原实际两支选择原计值证书，给出
原 Cp；尚无该证据，也无其不存在的定理。没有把结构互模拟的模型
放到原 Lgl 的位置，没有用新合法性标准替代它。

**暂停的含义。** 按作者给 (c) 的约定，乙线停在这个单点；LevelNoK
保持未否定。没有继续其它链点、gĉ、回灌闭包或 ι；O8 / O7 / O5 / O4
没有新增工作。没有证明原定义必须修改，也没有擅自修改它。没有新
闭项或值前沿，没有提交或推送。

```text
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsRound5.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/R5Attempt.agda +RTS -M6G -RTS
```


**正式模块复核。** 删除本轮 TreeLevels5Point、TreeLevels5Rise 与汇总自身
接口后，单路 6G 冷编本入口，三件全部重查，退出 0。编译过的是目标
陈述与运算公式，**不是 FirstStep 的项或否定项**。禁用构造及
Funext / UIP / Un 前提检查为 0；默认及本轮文章 mapcheck、diff 检查通过。
源码导入闭包本地 21 模块，记号禁用表命中 0；不是完整成品认证。
后补正文经 Agda 代码块相等检查，没有改已通过的数学代码。

辅助失败实验的重现命令（14G 时其它 Agda 必须已结束）：

```text
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/R5Unfold.agda +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/R5Point.agda +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes -i <实验目录> <实验目录>/R5Point.agda +RTS -M14G -RTS
```

R5Unfold 的记录在外层设置 180 秒超时，退出 124；原始编译器标准输出
已完整收录，未生成类型通过结果。这里的失败模块仅按 text 保存。
