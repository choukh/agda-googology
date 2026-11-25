# K2′ 第一阶段交付：嵌套闭项与值下界已交，全片段 ψ 未完成

**任务未完成，乙线与 Only0 片段均未被否定。** 对纲领与目标的意义是：
YiCarry V1 的起点证书足以在一个真正含嵌套 lc 0 的规范闭输入上，
由加法规则生成链点、LglB、严格增长及合法输出；这个闭输出已有与原
ψ⁰ 比较的序数值下界。尚未得到对所有这类 Source 的完整递归 ψ，
不能据此宣称 K2′ 第一阶段成功或树已自足。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2b where

import OCF.Align.YiK2bBase
import OCF.Align.YiK2bNested
```

## (a) 定义、闭项和保持

| 项目 | 编译定理的范围 |
|---|---|
| `Only0`、`Source0`、`branch0` | 按构造子排除非字面 zero 层的 lc；沿 LF 第一支及全部原守卫分支递归。Source 仍是冻结接口的 Source，没有附加可折叠条件 |
| `zero-output`、`suc-output`、`lim-output` | 三行的合法性与正性部件；极限行明确要求相邻子输出的原 Cp |
| `AddChain.next`、`grow`、`chain-grow` | out 交合法正输出、mono 交带后坐标合法界的单调性时，真正生成下一 PointB，LglB 和原 guard 随规则保持，严格增长不作前提 |
| `AddChain.collapse`、`generator` | 同一条件下的合法正输出；与一个 ψ 的子输出相等时，装配冻结接口的 GtGenerator。这里只是条件部件，没有借此假定完整 ψ 已存在 |
| `nested-source` | 原块 `Ω₁ +ᴸ Ω₁` 的闭 Source0，实填 Only0、Carry、Legal |
| `closed`、`closed-B`、`closed-legal`、`closed-positive` | 上述闭输入的独立折叠输出与 LglB、读回 Legal、正性；分支 `Ω₁ +ᴸ up 0 η` 仍含 lc 0 |
| `closed-row`、`closed-additive`、`closed-start` | 本闭项确取子输出的极限，更新为 γ 加子输出，初项确为 start0-B 的字面 1 |
| `tail-cp`、`tail-legal` | 对任意合法正 seed 的可数尾部参数化保持，不为本例另写一套逐阶段证明 |

条件部件的前提有实例：Nested 中的 `prefix-output`、
`prefix-output-mono`、`initial`、`inner` 实填 AddChain 的全部所需前提。
这没有把它们外推为任意 Only0 分支的性质。

## 尚缺的完整递归义务

[Base](YiK2bBase.lagda.md) 的 `FoldRows0` 只陈述本轮要求，**没有实例**。
缺的是：在全部 Source0 上构造 ψ，以及零、后继、极限、gt 四行同时成立时的
OutputB、读回合法性、正性和 LF 公共界下的 bounded-position。
本例的 `tail-cp` 是 Raw 位置保持，不能冒充全片段的 LF 位置保持。

一个必须处理的情形是两个输入底层 LF 相同，但 Carry／Legal／Only0
证书不同。`certificate-coherence-required` 编译证明：若完整记录可填，
bounded-position 的两个方向及 Raw 0 第一位置反对称性将迫使两份输出
**字面相等**。公共界就是这个合法 LF 本身。这个必要接口推论没有证明
完整记录的前提可满足，更没有否定它。

**判断：** 直接把源证书传入 gt 递归调用的写法，还缺把证据不依赖性传过
递归折叠及极限的证明。原 Legal 的 irr 仅给子 LF 对守卫证据的不依赖性；
不能直接把逐支相等或逐支互模拟当成 Raw 的字面相等。
本轮没有证明这一缺口只能靠函数外延解决，也没有据此判定路线不成立。
没有在定义或证书中使用函数外延。

## (b) 值：已交闭项的无条件下界

[Value](YiK2bValue.lagda.md) 的 `nested-lower`：

```text
Value.ψ⁰ (Value.Ω₁ + Value.Ω₁) ≼ read (raw closed)
```

`tail-value` 将前缀分支输出与原 ψ⁰ 的相应分支按值双向比较；
`H-mono` 是固定前缀下、对任意可数尾部的单调性，
`chain-lower` 将原链逐项送到本例真正生成的加法链之下。
这里只证下界，没有证反向，没有作基本列或 FGH 相同的声称。

输入也有严格越过 Ω₁ 的编译证据：`suc-Ω₁≤reference` 给后继下界，
`reference-not≤Ω₁` 排除反向。这不是一个只在 Ω₁ 上重复旧验收的例子。
尚不把这个比较另读成某个更高 ψ₀(Ω_x) 站的强度验收。

## 止损与档位

- **编译过的定理：** 上述部件、闭项保持、必要接口推论及值下界。
- **有限测试：** 无。
- **判断／未完成：** 全片段递归器与跨证书的字面位置保持未走通；没有编译定理否定其中任一行。

因此没有把类型检查过程中的报错当作数学否定，没有声称触发“某行保持
不成立”的止损，也没有消耗一次获准的写法更换。此次返回的是部分成果，
不关闭或否定路线；完整任务仍有上节逐项列出的工作。

## 翻译账

| 部分 | 来源与新增内容 |
|---|---|
| 四行目标形状 | 参考 JiaExactFold 的零、复制后继、逐项极限、链上子输出极限；定义闭包不导入它，不称规则已由树侧唯一推出 |
| 加法链的写法 | 来自 RR4 与作者 D10 的决定，单列为树侧候选。直接使用 YiK2Base 的右递归加法与路径运输，不逐项读 EBO 基本列 |
| Only0 与 Source0 | 本轮指定的构造子片段；保留原 Source，不改 Carry、Reg、Gd、Lgl、Legal，不以更强的分支保持证书缩小完整目标 |
| 链证书 | 原 guard 所需；start0-B 给初项，输出正性与 add-B 给下一点的严格路径及 LglB。没有链点判等、全分支高层比较或 k>0 回灌 |
| 闭例专门性 | Ω₁ 前缀是为交付嵌套闭项而选的明确子族；tail 的 seed 参数化，但这不等于全 Only0 结构递归 |
| 第 4 层义务 | 只在 YiK2bValue 新增关系定理，证明闭例不低于原 ψ⁰ 的参照输出；一般节点与原链的关系仍未证 |
| 第 4 层逼出 | 无；未为值验收改前三层定义 |

干净导入只保证不引用记号，不说明这些定义没有受记号启发。
本轮只新增 YiK2b*.lagda.md，没有改冻结接口或已有数学文件，没有提交或推送。

## 冷编与审计

最终复核采用只删除本轮四件模块各自的 .agdai、依赖用缓存的冷编，
每次单进程 `+RTS -M6G -RTS`，直接读取退出码；不使用 ignore-interfaces。

2026-11-10 冷编清单：

| 模块 | 堆上限 | 退出码 | 有目标 Checking |
|---|---|---|---|
| YiK2bBase | 6G | 0 | 是 |
| YiK2bNested | 6G | 0 | 是 |
| YiK2bValue | 6G | 0 | 是 |
| YiK2b | 6G | 0 | 是 |

配方（库文件含 stdlib 2.4、cubical 0.9；逐一替换文件名）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK2b.lagda.md +RTS -M6G -RTS
```

Base／Nested／入口的源码本地导入闭包分别为 23／24／25；
`importclosure.py` 的禁用表命中及 `--only` 越界均为 0。
此次 `--only` 的完整参数为 OCF.Align.LevelFix、OCF.Align.Yi、
OCF.Align.RR4CoordRoot、OCF.Align.RR4RegOmega2、OCF.BTBO、OCF.Free.Level。
Value 明标为第 4 层，源码本地闭包 56，不要求它闭包干净。
四件各自的编译器 dependency-graph 与源码本地模块集合完全一致。

成功 HTML 的定义切片：Only0 21、next 44、chain-grow 48、
certificate-coherence-required 73、closed-B 89、closed-legal 102、
nested-lower 258 个块，记号模块及记号词均为 0。
正对照 Value.ts-vlab 为 563／92／65，脚本确实能发现记号依赖。
切片是语法近似，不把验收文件的这一条零依赖切片冒称其导入闭包干净。

四件代码均为 safe／without-K，无公设、洞、停机或正性绕过、函数外延；
无本机绝对路径和尾随空白。没有删除或重编依赖的共享接口。
