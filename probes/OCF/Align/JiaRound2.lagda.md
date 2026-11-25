# 以甲为脚手架完成乙：S1 第二轮，停在 raw 分支入口

**档次：可数输入包与 Ω 单分支的正面构造，加原接口的编译卡点。**
按作者本轮指令，遇到需要给 raw 树事后补码的接线时停下报告。
没有完成 Ω_Ω 原结点、ψ／回灌包闭包、T甲 或值下界。

第一轮六件已统一改名为 Jia 前缀，导入、README、LOG 的引用均更新；
11-03 的 ScafLadder 旧族不动。S3 起仍保留 Yi 前缀，本轮没有 Yi 成品。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRound2 where

import OCF.Align.JiaRound1
import OCF.Align.JiaCountPack
import OCF.Align.JiaSingularBranch
```

## 正面构造的范围

- [JiaCountPack](JiaCountPack.lagda.md) 的 `Named` 在零、后继、ℕ 极限
  构造时就携带码。`erase-tracks` 保证其原树逐构造子对应此码；
  `tracks-coe` 证明跨可及证明搬运保持这个对应，无 UIP、无函数外延。
  `nat` 与 `omega-named` 分别实填有限和极限构造的前提。
- [JiaSingularBranch](JiaSingularBranch.lagda.md) 的 `omega` 沿这棵输入树
  递归，零给 1，后继给原 `regular`，极限递归生成各支再提升。
  `branch` 对所有已有输入包同时生成 Ω 码、NF 证明及原树。
  `zero-branch` 编译确认零输入的树分支为 1。

`Generated.built` 记录树确由此 Ω 程序构成；`branch-code` 是码运算方程。
**这个来源记录不是输出码与树的序数值相同的定理。**
没有把它说成完整码树值对应，更没有把它说成 ψ 生成域封闭。
`Named` 的极限逐项读记号，是甲脚手架，不是乙或树自足。

## 触发停止条件的准确位置

现有 `JiaBase.Layer.o` 的低层域由 `Low` 定义成 raw 树。
在 Ω_Ω 处，原分支输入类型为零层的 Tree [] a₀；新分支 `branchTree`
接受的是构造时携码的 `Pack`。直接接线如下，编译退出 **42**：

```text
{-# OPTIONS --safe --without-K --cubical-compatible --guardedness --hidden-argument-puns #-}
module JiaPortAttempt where
open import Data.List.Base using ([])
open import OCF.Align.EboLeanDef using ([]<)
open import OCF.Align.EboLeanBase using (n[])
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Tree; below; module Layer)
open import OCF.Align.JiaSingularBranch using (Ω; branchTree)
port : (a : Acc′ Ω) → Tree Ω a
port (acc h) = Layer.o (below n[] []<) (λ x → branchTree (acc h) x)
```

原错误的路径脱敏摘录：

```text
<实验目录>/JiaPortAttempt.agda:10.66-67: error: [UnequalTerms]
(Layer.Tree [] (OCF.Align.JiaBase.Low [] (h n[] []<))) !=<
(Agda.Builtin.Sigma.Σ OCF.Align.EboLeanDef.T
 OCF.Align.JiaCountPack.Named)
when checking that the expression x has type
OCF.Align.JiaCountPack.Pack
```

这只是**当前函数的类型错位**，不是任何路线的不可能性定理。
若要保持这个接法，必须先给原 raw 输入找包；这正是作者要求停下的
“给 raw 树事后补码”。`RawRepack` 只展示一种保留原树的补码接口，
没有填它，也不声称每一种接法都必须满足它的字面等式。

另一个设计是从一开始就让低层分支接受包。它没有被本次实验否定，
但不是已编译的原 raw 树族；本轮没有为续接而改写原树族或折叠。
按停点要求，后续设计交作者决定，不继续写 raw 补码器。
没有发现必须 UIP 的定理；也没有用改成全 raw 量化来填包接口。

## 检查、复现与剩余义务

正式入口从仓库根运行：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/JiaRound2.lagda.md +RTS -M6G -RTS
```

正式九件删除自身接口后串行冷编，退出 **0**；依赖用已有接口，
不使用 ignore-interfaces。全部 safe、without-K；禁用构造检查为零。
上面的失败接线在仓库外单独编译，退出 42，不进正式 Agda 代码块，
不使用该失败轮的 HTML、切片或依赖图。没有超时或堆耗尽。

S1 仍缺：原 Ω_Ω 结点、随 ψ 与回灌生成的对应包、完整 T甲、FGH、
reference 下界及实际比较清单。没有进入 S2。
本轮无新序数值验收；P1 仍为 x = Ω·ω²。
