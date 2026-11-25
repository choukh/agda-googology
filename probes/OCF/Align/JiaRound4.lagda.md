# S1 第四轮：新 ψ 逐项保持，停在 Ω_Ω 的有限索引构造

**档次：有界种子合同下的正面保持定理、非空的实际闭相关包、以及 Ω_Ω 的构造卡点。**
本轮新开精确 ψ，不改旧 `JiaFold`、`JiaBase` 的树族、全 raw 分支域或 Rep。
没有使用 UIP 或 raw 补码器。完整 T甲 尚未完成。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRound4 where

import OCF.Align.JiaExactFold
import OCF.Align.JiaExactCode
import OCF.Align.JiaExactAdd
import OCF.Align.JiaExactSeeds
import OCF.Align.JiaExactRep
import OCF.Align.JiaExactFeedback
import OCF.Align.JiaExactOne
import OCF.Align.JiaExactIndex
```

## 新保持定理及其条件

`Sound.ψ-rep`：在 SeedSpec seeds ℓ 合同下，若源树在原第 ℓ 层对应
码 c，则新 ψ 到任一有界目标 i 的输出对应原 EBO 的 ψ_i(c)。
四种树情况、EBO 比较的 lt／eq／gt 三支全部已证。
见 [JiaExactRep](JiaExactRep.lagda.md)。

合同只要求源层之下的所有目标／共尾层 Ω 种子已有 Rep；
目标与共尾层都带原源层的 `Below`。它没有假设所有裸层号上已建好种子。
但**这是合同下的保持定理，不是高层种子已构造的结论**。
目前 `one-spec` 在第 1 层实填该合同，目标只能是零层，种子为 1；
更高合同尚未实填。见 [JiaExactSeeds](JiaExactSeeds.lagda.md)。

辅助接线 [JiaExactCode](JiaExactCode.lagda.md) 只证明原 EBO 定义的等式；
[JiaExactAdd](JiaExactAdd.lagda.md) 的 `rep-add`、`rep-copies-single`
把原树加法与 n 份复制分别接到码列表连接与 replicate n。
这里不替码做正规化，也不从任意 Rep 推出输出码标准形。

## γ 链包与实际实例

[JiaExactFeedback](JiaExactFeedback.lagda.md) 的 `gamma-rep` 随迭代
生成 γ 树与原 γT 码的对应。`pack-chain` 还用原 `tow` 给标准形：
前提为父折叠码 NF、父码的 Ω 共尾证据、gt 比较及同界种子合同。
结果的 `Related` 同时含码、NF、原树、Rep，树字段就是新 ψ 的实际链点。
没有事后给一个 raw 树搜索码。

`Trees-at` 表示这个链点包可作下一层号的类型参数；
它只给下一层类型，不等于 Ω 程序或完整反馈已构造。

[JiaExactOne](JiaExactOne.lagda.md) 对第三轮的实际最小正规 Ω 给出：

- `regular-exact`：任意可及证明上的完整输出 Rep，不是有限项测试。
- `regular-chain`：原 regular 的实际提升分支上，所有 γ 链点都有相关标准形包。
  合同、NF 父码、共尾证据与比较前提均已实填。
- `closed`、`closed-code`：无参数的闭相关包，码为原 ψ₀(Ω)。
  这只是改动处的实例验证，**不是 T甲 或新的值前沿**。

## 逐条翻译账：供 S5 删除或重写

| 位置 | 为对齐 EBO 而采用的写法 | 既有形状及本轮边界 |
|---|---|---|
| 零行与种子 | ψ_i(0) 读目标 Ω_i 种子；其 Rep 必须为 Ωt i，零层实例取 1 | 种子读法由 EBO 决定；目前只填第 1 层有界合同，不冒称全层完成 |
| 后继行，规则 4 | 第 n 支为 n 份 ψ_i(x)，n=0 时为零 | `copies-old` 为 refl：与旧 JiaFold 的 lfp 加法行定义相同，不算新增树形变化 |
| ℕ 极限，规则 5ω | 逐 n 递归，不累加、不移位 | 保留原逐点形状；对应码分支为 ψ_i(fsn c n) |
| Ω 比较 | 明确比较 j+1 与 i，直接照 fsnc 的路由 | j 与 i 各带 Below 同一源层；未声称 j+1 也 Below 该层，未交完整运行清单 |
| 比较 lt／eq，规则 5Ω | 两支都保留 j 结点，对低层输入搬运后递归 | 原全 raw 域不动；Rep 证明只消费已经相关的输入 |
| 比较 gt，规则 6 起点 | γ₀ 为第 j 层 Ω 种子，码为 Ωt j | 与旧从零起步不同；种子证据来自同一有界合同 |
| 比较 gt，规则 6 步进 | γ_(n+1)=ψ_j(f γ_n)，输出第 n 支为 ψ_i(f γ_n) | 旧“j=i”的单独 lfp 也由本行覆盖；不再输出从零起步的裸迭代项 |
| 派发辅助函数 | `dispatch` 显式接受比较值和证据 | 只为避免依赖 with 的类型展开问题；不改变已列出的三支树形，不比较两份证明是否相等 |
| 链点标准形 | 用父 NF 及原 tow 的不变量给 NF(γT n) | 是记号侧封闭的使用，不能称树自足，也不能把 NF 前提删去 |

所有这些结构都只在甲脚手架。S5 须从这张表出发重写，
不能以本轮 Rep 方便为由把它们保留进乙的最终定义。

S5 回看：作者提示第三轮原 BTBO 式 ψ 的独有、较快基本列可供清单第 6 条参考；本篇只保存线索，不从 no-preservation 推出新的 FGH 比较。

## Ω_Ω 卡点与停止范围

新 ψ 的保持证明不需要给全 raw 分支找码；构造 Ω_Ω 的分支程序仍有另一项义务。
该程序接收原零层树 y，若 y 关联 d，则期望输出关联 Ωt d。
当 y 为后继 s x、x 关联 d 时，输出须关联 Ωs d。

[JiaExactIndex](JiaExactIndex.lagda.md) 的 `root-index`、`successor-point`
证明：这种正确输出的原 Ω 根字段必须正好是有限索引 d。
所以按 Ω 后继规则直接构造该分支时，需要从原始前驱 x 恢复这个有限索引。
程序分支只收到 raw x，Rep 中的 d 只在相应证明前提下给出。
本轮没有编写此恢复程序，也没有将 Rep 证据强加到原分支域上。
按作者“不补原始树码”的边界在此停下报告。

诊断有 d=0、x=零的编译实例，逐点前提非空；
该实例只是把原正规 Ω 提升后作为常函数，未说它对其他 d 正确。
索引恢复的要求弱于第二轮 RawRepack 的完整码树包，
**不是所有接法不可能的定理**，也不关闭关系式路线。
这里没有修改树族或额外假设 UIP。

因此未交付：Ω_Ω 全 raw 分支、更高种子合同、完整 Ω／回灌闭包、
T甲、T甲 的 FGH、reference 下界、完整运行比较清单。未进入 S2。
P1 仍为 x = Ω·ω²。

## 编译与工程记录

从仓库根：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/JiaRound4.lagda.md +RTS -M6G -RTS
```

八件数学模块删除自身接口，经新入口串行冷编；九件全部 Checking，退出 **0**。
safe、without-K 与禁用构造检查均通过；依赖用已有接口，未 ignore-interfaces。

一轮将具体闭树与通用证明直接比较的附加实验退出 **251**：

```text
agda: Heap exhausted;
agda: Current maximum heap size is 6442450944 bytes (6144 MB).
agda: Use `+RTS -M<size>' to increase it.
```

当时的附加代码是把 closed 单独定义成 Tree，再用 regular-exact 对它证明 Rep。
没有采用增加堆的建议。去掉该附加展开后，参数化实例 6G 通过；
再改为先用 make 在任意可及证明上装 Related，最后关闭整个记录，6G 通过。
正式 closed 保留原树与 Rep，没有为验收修改 ψ 或树形。
失败轮没有作为通过，不使用其 HTML、切片或依赖图。

其它退出 42 的初始轮是依赖 with 展开、签名 where 语法及未标明 n 类型；
分别以显式 dispatch、顶层辅助函数、n : ℕ 修正，未用 UIP。
没有数值 FGH 测试，也没有把工程失败当作数学否定。
