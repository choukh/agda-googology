# K2 交付：加法链可由规则增长，全 Legal 域缺 gt 初项

**判决：部分完成，全域四行折叠未交付。** 对纲领与目标的意义是：
在原块上，不比较坐标便能由加法规则生成严格增长的链及其守卫；
规范 Ω₁ 的根折叠已有合法闭项和序数值验收。
但原 Legal 允许下界不合法的第 0 层结点，那里根本没有可入坐标。
所以以“对每个 Legal 输入都启动原守卫 gt 链”为要求的完整折叠不能定义。
这条必要接口被编译否定；不否定加法链、规范生成域或乙线本身。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2 where

import OCF.Align.YiK2Base
import OCF.Align.YiK2Stop
```

## 交付 (a)：构造与合法性，以及全域停点

四行方案在 [Base](YiK2Base.lagda.md#四行的选择与义务) 先列明：
零取 1，后继取 n 份复制，极限逐项，gt 取链上子折叠的极限。
前三种写法来自甲的 EBO 规则模板；gt 链改成 `γ + ψ(g γ)`，
下一点的增长、合法性和原守卫均随构造给出。

| 定理或构造 | 文件 | 已编译的精确范围 |
|---|---|---|
| `ψᶜ-legal`、`ψᶜ-cp`、`ψᶜ-read-legal` | [Base](YiK2Base.lagda.md) | 原 Raw 0 上可数折叠保持 Lgl、第一位置，读回满足原 Legal |
| `Chain.next`、`Chain.chain-grow` | [Base](YiK2Base.lagda.md) | 有可入初项时，规则生成下一点及守卫，全部相邻点有原 Dn；无 Grow 前提 |
| `Chain.collapse-legal` | [Base](YiK2Base.lagda.md) | 根为 gt、分支为 Raw 0，显式给分支 Lgl／Cp 单调证据时，链上折叠输出合法 |
| `closed`、`closed-read-legal` | [Base](YiK2Base.lagda.md) | 规范 Ω₁ 的根折叠闭项及原 Legal 证明，链初项为字面 1 |
| `coordinate→bound-legal`、`bound-legal→coordinate` | [Stop](YiK2Stop.lagda.md) | 有可入坐标当且仅当下界满足原 Lgl |
| `source-legal`、`no-coordinate`、`no-gt-chain` | [Stop](YiK2Stop.lagda.md) | 一个完全合法的第 0 层源没有任何原守卫坐标，因此任意链都不能启动 |
| `no-start-all` | [Stop](YiK2Stop.lagda.md) | 否定全 Legal 域上的 gt 初项生产器这一必要接口 |

反例下界是 `lim (1,0,0,…)`，其第一个相邻步要求 1 是 0 的第一位置。
Legal 不读取下界合法性；取第一支及全部 Ω 分支为 0，原六字段均可实填。
由任意守卫坐标的合法性沿其第一位置回传，就会得到这个非法下界合法的矛盾。
反例源是闭项，结点层只有 0；不是不满足某个额外前提的条件反例。

`Chain` 的条件也有闭实例：`Canonical` 取恒等分支，守卫提供分支合法性及单调性，
`start` 为 1，`canonical-is-Ω₁` 将该源与原块规范 Ω₁ 字面相等地连接起来。
这里没有嵌套 gt 的完整递归器，不能用这个局部实例替代任务要求的全域保持。
一般 Chain 的 Raw 证据是充分条件，没有从原 LF 源的 Legal 反推这些证据；
读回后的 CP 不能冒充 Raw 的 Cp。

## 交付 (b)：值

第 4 层文件 [Value](YiK2Value.lagda.md) 的无条件定理 `same-on-Ω₁`：

```text
read closed ≈ᵛ Value.ψ⁰ Value.Ω₁
```

即规范 Ω₁ 的这份加法链根折叠与原折叠序数值互相 `≼`。
证明先把 Raw 0 加法、可数折叠读到已有可数树，再双向模拟 RR4 的加法链，
最后用 RR4 的规范 Ω₁ 值定理。没有新增一般节点保值或 EBO 下界。

## 止损与未完成项

全域要求在 gt 行的初项义务已被否定，发生在输出合法性证明之前。
因此本轮没有“输出已经构造、某一行保持失败”的反例，也未计作第二次保持失败。
任意链都缺初项，换一次加法链形状也无法修复，故不更换链写法。
完整折叠及其 `Legal → Legal` 定理未交付；不缩小全域后冒称任务成功。
若另行选择携带合法下界证据的输入域，本否定不适用；该域上任意嵌套 gt 的
完整互递归、第一位置保持及合法性仍未实现，本轮不擅自转入。

没有修改 Raw、Gd、Lgl、Legal；没有迁移整线、上高层、添加默认输出或实施 D8。
没有链点判等、全分支高层比较、值关系驱动的计算或 Funext。

## 翻译账

| 部分 | 来源及本轮所做 |
|---|---|
| 零、后继、极限、gt 输出形状 | 参考 JiaExactFold 的 EBO 模板；定义文件不导入它，不称这些行由树侧唯一推出 |
| 链的写法来自哪里 | RR4ChainAdd 的加法链设想，经作者 D10 许可；右递归加法在原 Raw 0 上直接实现，不从 EBO 基本列逐项读出 |
| 增长证据 | 树侧逼出：ψᶜ 输出有从 0 出发的严格第一位置路径，固定左加法运输该路径；不是待填的 Grow 假设 |
| 守卫与初项 | 原 Gd 强制链点合法且包含原下界；恰等价于下界 Lgl，反例说明原 Legal 不提供它，没有改旧定义补字段 |
| 第 4 层义务 | 仅在 YiK2Value 对规范 Ω₁ 证与原链同值；一般节点与嵌套 gt 的值关系仍未证 |
| 第 4 层逼出 | 无；没有为值验收反改前三层 |

干净闭包只说明不引用记号；规则仍有上述模板及 RR4 的研究来源，不称树已自足。

## 验证

2026-11-10 冷编清单（只删除各模块自己的字面接口，依赖用缓存）：

| 模块 | 单进程堆上限 | 退出码 | 目标模块 Checking |
|---|---|---|---|
| YiK2Base | 6G | 0 | 有 |
| YiK2Stop | 6G | 0 | 有 |
| YiK2Value | 6G | 0 | 有 |
| YiK2 | 6G | 0 | 有 |

编译配方，分别代入四件文件；全部带 `+RTS -M6G -RTS`，直接读取进程退出码：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiK2.lagda.md +RTS -M6G -RTS
```

Base／Stop／入口的源码本地闭包分别为 5／6／7，库叶均为 13；
`importclosure.py --only` 仅准本轮、LevelFixCore／Val、Free.Level、OCF.BTBO，
三件禁用表与越界模块均为 0。成功冷编同时生成 HTML 和编译器依赖图，
三件图的本地集合与源码闭包逐一相同。
Value 是明标的第 4 层验收，源码本地闭包 36，与编译器图相同；不要求其记号闭包干净。

成功 HTML 的定义切片：ψᶜ-legal 35、next 43、chain-grow 46、closed-read-legal 71、
source-legal 31、no-start-all 40 个块；记号模块／记号词均为 0。
正对照 Value 的 ts-vlab 为 563／92／65，确认脚本能发现记号。
切片仍是语法近似，不认证值或树自足；干净导入闭包是更强的引用边界检查。
四件代码禁用构造、洞、Funext 均为 0，无绝对路径、临时日志路径或尾随空白。
工程记录另见 [LOG](../../LOG.md)。
有限测试：无。以上正面、否定及值关系均为编译定理；未完成部分逐项如上。
