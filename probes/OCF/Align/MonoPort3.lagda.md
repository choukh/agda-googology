# 一族关系 $R_{c,c'}$: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件.
>
> 1. **与关系无关的和结构核 (HOLDS).** [MonoPort3Gen](MonoPort3Gen.lagda.md): 对**任意实例** $\Lambda$、任意输入层、任意输入世界与进入路径、**两边不同的动作**, 和结构的十四种情形 (`n0`, `n1`, `⨾`, `nl`, `tr` 两种, 单位四种, 结合四种, 部分和, 极限) 都是对语义的一步引理. 输出关系、上下文关系、输入关系都是参数, 只要列出的律.
> 2. **`snd` 两边动作不同 (HOLDS, 实例 $\Lambda=2$).** [MonoPort3Two](MonoPort3Two.lagda.md) `snd₂`: $x\sqsubseteq x'$ ⇒ 对一切满足三条 `HA` ($ii$, $jj$, $ij$) 的动作对, 两个读数都可比. 和结构的情形全部由核给出, 本文件只写律的实例 (12 条由构造子直接给, `Lpre`, `Llim` 各 3 行) 与节点的一步 `niS₂`.
> 3. **`ChainLe (hs (hs hz))`, `MonoStep 3`, $T_3<T_4$: 没有做** (未完成, 不是否定). §3 列出还缺的件. 没有找到反例, 没有否定定理.

## 1 核用到哪些律 (回答 `StrRel` 的接口问题)

输出关系 `_≼_` (在 `Df W` 上; 多层时是各层目标上关系的积):

| 引理 | 用到的输出律 | 上下文律 |
|---|---|---|
| `n0S` | `L0` | 无 |
| `n1S` | 无 (动作前提) | 无 |
| `⨾S` | `L⨾` | `cxL`, `cxR`, `cx⨾` |
| `nlS` | `Lnl`, `L⨾` | `cxL`, `cxR`, `cx⨾` |
| `trS`, `trS′` | `Ltr` | `cxL` 或 `cxR` |
| `u0ˡS`, `u0ʳS` | `Lu0*`, `Lu1*`, `L⨾`, `L0` | `cx0ˡ`, `cx0ʳ` |
| `u1ˡS`, `u1ʳS` | `Lu1*` | 无 |
| `asˡS` … `asʳ′S` | `Las*` (两条: 一条给输出, 一条给状态), `L⨾`, `Ltr` | `cx⨾`, `cxas`, `cxas′` |
| `preS` | **`Lpre`**, `Lasˡ′`, `L⨾`, `L0`, `Lu1ˡ` | `cx⨾`, `cx0ˡ`, `cxpre` |
| `limS` | **`Llim`**, `Lasʳ`, `L⨾`, `L0`, `Lu1ʳ`, `Ltr` | `cx⨾`, `cx0ʳ`, `cxlim` |

**只有 `limS` 用 `Llim`** (左极限截断). 一个结构关系 (不含 `lim⊑`) 不会有 `lim⊑` 构造子, 所以 `snd` 不调 `limS`, 不需要 `Llim`; 其余律对结构关系都是构造子. 输入关系 `In` 只在上下文律里出现.

**但第 0 层坐标.** 本组第 0 层坐标按值对齐, 第 0 层输入的比较经 `DValCanon.Gen`, 而 `Gen` 要 `lim-leP`, 即 `limS`, 即 `Llim` 在第 1 层输出上成立. 所以只要节点的分支坐标是第 0 层且按值对齐, 输出关系就必须带 `Llim`. 想不要 `Llim`, 就要第 0 层坐标也按结构关系对齐 (不经规范形). 这是判断, 没有编译的否定.

## 2 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `OutLaws`, `PreLaw`, `LimLaw`, `CxLaws` | MonoPort3Gen | 律的陈述 | 定义 |
| `PreOut.O≡`, `rPre` | MonoPort3Gen | 部分和的输出字面是各段输出的部分和; 部分和自比 | 定理 |
| `n0S` … `limS` (14 条) | MonoPort3Gen | 和结构的一步, 两边动作不同 | 条件定理 (律, 动作前提) |
| `OL`, `pre≼`, `lim≼` | MonoPort3Two | `MonoPort2Rel` 的 ⊑ 满足全部输出律 | 定理 |
| `cl` | MonoPort3Two | 上下文取 $\top$ 时的上下文律 | 定理 |
| `branch`, `niS₂` | MonoPort3Two | 节点一步, 两边动作不同 | 条件定理 (三条 `HA`) |
| **`snd₂`** | MonoPort3Two | 第 1 层, 两动作, 两读数 | 条件定理 (三条 `HA`) |
| `MonoStep 3`, $T_3<T_4$ | — | 纸面: 方法应能走通 | 判断, 未做 |

## 3 到 `MonoStep 3` 还缺什么 (判断)

实例 $\Lambda=3$, 目标 $T_0,T_1,T_2$. 核给出一切和结构的情形; 还要:

1. **关系.** $\sqsubseteq_1$, $\sqsubseteq_2$. 第 2 层树里有两种节点: 第 1 层的 (分支坐标是第 1 层树, 按 $\sqsubseteq_1$ 对齐) 与第 0 层的 (来自第 1 层输入在 $T_2$ 上保留的节点, 坐标按值). 第 1 层的上下文在这一实例里**被读作坐标** (第 2 层节点的 `Ai`), 其中有 `nw self _`, 所以 $\sqsubseteq_1$ 要多 `nwˡ`, `nwʳ` (只在 `self` 上; `Run (nw self x) self` 定义性地就是 `Run x self`), 上下文律 `cx*` 由 $\sqsubseteq_1$ 的构造子给出 (`cxas` 要 `nw` 与 `⨾` 交换, 由 `nwˡ`, `nwʳ`, `as*` 拼出).
2. **观测.** `_≼_` 取 $T_1$ 上 $\sqsubseteq_1$ 与 $T_2$ 上 $\sqsubseteq_2$ 的积; 律逐层给.
3. **节点的一步, 按目标分两类.** 节点层 $k$, 目标层 $e$: $e\le k$ 上升, 输出是链, 链的点在层 $k$, 读 $T_e$ (所以第 1 层节点在 $T_0$, $T_1$ 都上升); $e>k$ 保留, 输出节点的分支是 `BNi`. 上升要层 $k$ 的链引理 (`chain₂` 的推广: 点按层 $k$ 的关系, 输出读到 $T_e$, 用 `Lnl`); 保留要 "先在层 $k$ 走坐标再走分支" (`branch` 的推广: 层 $k=0$ 用 `cong0₂` 的三读数版, 层 $k\ge1$ 用层 $k$ 的 `snd`, **不要规范形**).
4. **第 0 层的三读数版.** `MonoPort2Zero` 的 `Obs` 多一层; 用核 (`TW = A`, 上下文取值 $\le$) 加 `Gen`, 估计 150 行.
5. 外层链、起点、`mono₃`, `grow₃₄`: 照 `MonoPort2Chain`.

对一切有限高度一次写成 (一族 $R_{c,c'}$ 的一步定理): 要把 1 到 3 对层数参数化. 核已经对层、实例、观测参数化; 缺的是节点一步对 "目标层与节点层的比较" 的统一陈述, 以及层 $k$ 的 `snd` 作为层 $k+1$ 的参数 (归纳假设). 没有写.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 律的记录 `OutLaws`, `CxLaws` | `MonoPort2` 两个文件的和结构证明只用这些 | 树侧, 抽象掉重复 |
| 输入世界与路径的参数 (`TW`, `Path`) | 第 0 层要一切路径 (`nw`); 第 1 层以上只在 `self` 上取分支, 用单点类型让路径定义性地是 `self` (不开 K 时匹配 `W ≡ W` 不可用) | 树逼的 (`--without-K`) |
| 两边动作不同 | 下一层的节点上升时两条链各用自己的 `Ai` | 树逼的 (折叠的形状) |

**按 `AGENTS.md` 归类: 提供信息 (摆脱重复一步).** 没有新构造子或节点字段, 没有改折叠, 没有 `Lab`, 没有记号. 核不按站写, 对一切实例与输入层. 没有序数值验收.

## 5 账

| 文件 | 行 | 内容 |
|---|---|---|
| `MonoPort3Gen` | 321 | 律, 状态, 语义, 十四条一步 |
| `MonoPort3Two` | 111 | 律的实例, 节点一步, `snd₂` |
| 入口 | 4 | |
| 合计 | 436 | |

## 6 审计

- **导入闭包** (`--only` 同 [MonoPort](MonoPort.lagda.md)): 入口 35 个模块 (本地 25), `Gen` 30, `Two` 34; 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片**: `MonoPort3Two:snd₂` 316/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不出现 `Funext`.
- **编译**: 删掉本组的 `MonoPort3*.agdai` 后重编, 入口退出码 0 (6 秒, 峰值 1.0G).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort3 where

import OCF.Align.MonoPort3Gen
open import OCF.Align.MonoPort3Two using (snd₂; OL; pre≼; lim≼) public
```
