# S1 第五轮：混合族的全层种子，成对 ψ 在正规 raw 入口停下

## S1 结束记录（2026-11-09，作者决定）

S1 在第五轮结束，不再续接混合 ψ。停点为：奇异链需要携码，成对递归
在正规保留支又遇到 raw 输入；只给奇异结点加标签还会在加法处需要 raw 前缀码。
未交付 T甲、FGH、reference 下界或完整运行比较清单，未把缺项改称完成。

保留给 S3 的模板是：JiaExactFold 的逐项规则及 JiaExactRep 的 ψ-rep、
种子合同、JiaMixedOmega 的全有限标准形层 Ω 种子、奇异层的定位，
以及第四、五轮的逐条翻译账。

主审判断、作者同意：若 ψ 的奇异链继续使用码，码会沿分支传到正规 raw 输入；
全改码域会成为与 EboLean3／DirectClosed 同类的翻译，无法帮助树上位置派发，
而完全不用码的 ψ 已经是乙。剩余参照强度与规则清单在记号侧已有，
因此不再投入 S1，直接进入并入 S2 的 S3。这是作者的路线决定与判断，
不是本篇证明了所有甲方案不可能。后续顺序为 S3 → S5 → S4。

**档次：全标准形有限层码上的 Ω 构造与对应、实际 Ω_Ω 接线、
以及当前成对折叠接口的编译卡点。完整 S1 尚未完成。**
本轮按作者授权另开混合树族：只把奇异分支改成携码输入，正规分支保留 raw。
旧 JiaBase、JiaFold、JiaExactFold、Rep 和既有结论均不改，没有 UIP 或 raw 补码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRound5 where

import OCF.Align.JiaMixedBase
import OCF.Align.JiaMixedRep
import OCF.Align.JiaMixedOmega
import OCF.Align.JiaMixedPack
import OCF.Align.JiaMixedAuditTag
```

## 新树族与全层种子

[JiaMixedBase](JiaMixedBase.lagda.md) 区分两个 Ω 构造子。
正规 r 的分支域仍为完整的低层 raw 树，没有码、NF 或 Rep 输入要求；
奇异 q 的分支域 CodeArg j 保存有限码 d、NF d 及 d < Ω_{j+1}。
两者沿同一份 Acc 分层；搬运在 r 的输入处逆变，在 q 的码域上不作变换。

[JiaMixedRep](JiaMixedRep.lagda.md) 保留零、后继、逐 fsn 的 ℕ 子句。
正规 rr 仍只在已经相关的低层输入上约束分支；奇异 rq 对各 CodeArg
逐 fsT 约束。关系的正性、宇宙与搬运、提升均已编译。
这是新树族的对应关系，未冒称旧树到新树的全域转换已存在。

[JiaMixedOmega](JiaMixedOmega.lagda.md) 对每个 NF c、任意 Acc′ c 构造
第 c 层的 omega，并证明它对应 Ωt c。零、后继、ω-共尾、Ω-共尾四行
统一写在 build；递归的小层由原 pred、fsn、fsT 的下降与 NF 封闭给出。
Ω-共尾行的分支已有码，因此无需从 raw 树恢复层号。

`omega-rep` 与 `all-seeds` 没有未填的种子假设：每个带 Below 的低层目标
都实填 SeedSpec，覆盖 Λ 以下全部标准形有限层码。这里不声称 T 类型内
有一个有限的 Λ 码，也未把种子闭包说成 ψ 或终点闭包。

[JiaMixedPack](JiaMixedPack.lagda.md) 的 `regular-rep`、`regular-is-raw`
对任意标准形 ν 给原 raw 正规 Ω_{ν+1}；`singular-rep`、`singular-is-coded`
给实际 Ω_Ω 的 q 结点与对应。无参数的 `closed-singular` 保存其原树与 Rep，
`closed-singular-code` 给码 Ωt Ω。它不是 T甲，也不是新的值下界。

`Related` 保存码、NF、原混合树和 Rep；`next-omega` 从已有相关包给下一层
Ω 种子包。它没有接受无对应的 raw 树，也没有假设新 ψ 的输出已能打包。
**实际 ψ 输出的反馈闭包仍缺。**

## 当前折叠接法的缺口与停止范围

若把第四轮 raw ψ 逐行移入这个混合族，q 的 gt 行有新义务：
下一项应把 ψ_j(f γ) 的码送回 CodeArg。当前 f 只返回 raw 混合树，
单凭这个函数的类型不能取得该码。

改为在 Related 包上递归时，q 的输入码可从父码及 EBO γT 计算；
但 r 的 lt／eq 保留行仍须输出一个对全部 raw y 定义的分支。
此时 f y 是 raw 树，分支程序没有 y 的码或 Rep 证据，
所以不能直接把 f y 交给成对 ψ。

仓库外的下列接线实验真实退出 42；不是正式 Agda 模块中的洞：

```agda
-- 实验片段；完整实验证明选项亦为 safe、without-K，并带仓库 infective 选项。
-- 给定共同源层界 target，以及输出 r 所需的低层界 p：
-- target : Below i ℓ
-- p      : Below j i
-- out    : Related ℓ aℓ → Tree i ai
-- f      : Low i ai j p → Tree ℓ aℓ
-- keep   = Layer.r p (λ y → out (f y))
```

```text
<scratch>/JiaMixedKeepAttempt.agda:15.32-35: error: [UnequalTerms]
Layer.Tree ℓ (Low ℓ aℓ) !=< Related ℓ aℓ
when checking that the expression f y has type Related ℓ aℓ
```

这段实验只核对直接接线的输入类型，**不是所有混合 ψ 不存在的定理**。
继续此接法要把 raw y 或 raw f y 补成相关包，或改窄正规分支域；
两项均越过作者本轮停止边界，因此未做，停下报告。

还检查了“只给 q 添父码标签”的补救：这样可在 q 的 gt 行计算 γT，
但原加法的 x + q(B,f) 需要把 q 标签改成 A ++ B，A 是整个 raw 前缀 x
对应的码；只在 q 上的字段没有 A。后继复制也使用这个加法。
有限 NF 检查只能检查已有的码，不能先补出 A。

[JiaMixedAuditTag](JiaMixedAuditTag.lagda.md) 的 `ReadBack.decode-law`
精确证明一个条件诊断：若总标签更新在相关输入上给 A ++ Ω，删除末项
即可读回 A。它有有限码输入的实填实例；raw 树上的 TreeTag 合同未填。
这说明上述精确标签更新若用在全 raw 前缀上，会提供相关域的读码程序；
**没有证明这种合同不存在，也没有否定无标签、条件 NF 或其他混合接法**。
本轮没有往树里增加这种标签或把正规分支改成码域。

## 翻译账与 S2 边界

| 位置 | 采用的形状与理由 | 后续要求 |
|---|---|---|
| 奇异 q 的输入 | CodeArg 的码、NF 与 Ω_{j+1} 下界证据，直接照 EBO Ω-基本列 | S3 必须换成低层合法树；层号由树本身给出，Ω_c 对树递归 |
| 正规 r 的输入 | 完整 raw 低层树；后继 Ω 的分支为原结构 lift | 未改成码域，不以补码填本轮缺口 |
| omega 的四行 | 按码的 cof 派发，后继用 pred，极限用 fsn／fsT | 是甲的翻译，不称树自足，不进入乙的最终定义 |
| 小层与标准形 | 沿 NF 有限码的 Acc；下降、NF 分别借 TΩ／trian-fsn 与 NFΩ／cl-fsn-NF | 记号良基及封闭只在甲脚手架，S3/S5 须替换 |
| 相关包再作层号 | Related 的码及 NF 决定下一层 Tree 和 omega | 保留树及 Rep 供后续实现定理；目前未证明 ψ 输出反馈闭包 |
| 两类结点标记 | Kind 与 Root 记录 r／q 的构造来源 | S2 的每个实际比较须带此类别，不能用泛型比较记录冒充清单 |
| 未采用的 q 标签方案 | 标签更新碰到未知 raw 前缀码 | 仅诊断，未增加树字段，也未绕过停止边界 |

第四轮的精确 ψ 翻译账仍保留。旧 BTBO 式 ψ 独有基本列的 S5 线索也保留；
本轮没有从它推出新的 FGH 大小比较。

**未交付：混合 ψ、其保持与输出反馈闭包、T甲、FGH、reference 下界，
以及带正规／奇异来源的完整实际比较清单。未进入 S2。**
没有把种子构造内部的有限码比较当作 T甲 的 ψ 比较清单。
P1 仍为 x = Ω·ω²；本轮甲的种子与构造不计成品值前沿。

## 编译与复核记录

从仓库根，用外部含 stdlib/cubical 的库文件：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/JiaRound5.lagda.md +RTS -M6G -RTS
```

五个数学模块与新入口删除各自接口后冷编，六件均 Checking，单路 6G 退出 0。
依赖用已有接口，未 ignore-interfaces；代码 safe／without-K，禁用构造 0。
正规／奇异分支域、种子量词、NF 与递归小层方向、闭包未决范围均已只读复核；
主路再冷编审查文件，不把智能体的自报编译当复核。

早期退出 42 有 rq 的结点隐参未与 cof 索引显式绑定，以及递归小层被 helper 隐藏。
前者显式写 j 修正；后者将四行 build 与沿 Acc 的递归函数分开，递归调用直接
使用 h 的子证明，未使用停机绕过。最终种子及闭相关包均在 6G 通过，没有 251。
正规 keep 接线实验的 42 保留为卡点，未用失败轮 HTML、切片或图。
没有 FGH 数值测试；入口、README 与 LOG 同步，未提交或推送。
