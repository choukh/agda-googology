# 一族关系, 结构版: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义.
>
> 1. **一族的底 $R_0$, 对一切实例、一切观测 (HOLDS).** [MonoPort4Zero](MonoPort4Zero.lagda.md) **`snd₀ᴳ`**: 第 0 层输入按 `StrRelDef` 的结构关系 $\sqsubseteq_0$ 相关, 则对任意高度 $\Lambda$、任意世界、任意满足 `OutLaws` 与 `PreLaw` 的观测 (只多一条: $T_0$ 分量是 $\sqsubseteq_0$), 两边动作不同时输出相关. **不要 `LimLaw`, 不经 `Gen`.** **`chain₀ᴳ`**: 第 0 层节点上升的链, 输出值 $\le$ 且 $\sqsubseteq_0$. 和的结构全由 [MonoPort3Gen](MonoPort3Gen.lagda.md) 的核给, 本文件只写上下文律、`nw` 两条、自比与分派.
> 2. **`StrRel` 的关系接得上 (HOLDS).** [MonoPort4Inst2](MonoPort4Inst2.lagda.md): 实例 $2$, 观测 $T_0$ 上 $\sqsubseteq_0$、$T_1$ 上 $\sqsubseteq_1$ 满足全部输出律与 `PreLaw` (`O₂`, `pre₂`); `snd₀²` 是 `StrRelZero.snd₀` 的两动作版.
> 3. **第三站 (`ChainLe (hs (hs hz))`, `MonoStep 3`, $T_3<T_4$), 一族的一步 $c\to c+1$, 跨世界版: 没有做** (未完成, 不是否定). §2 是剩下的件, 每件说明由什么给出. 没有找到反例, 没有否定定理.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `cl₀` | MonoPort4Zero | 上下文取 $\sqsubseteq_0$ 时核的九条上下文律 (由 `sq`, `wl`, `wr`, `tr`, `u1*`, `al`, `ar′`, `nwd`, `nwd′` 拼出) | 定理 |
| `rO` | MonoPort4Zero | 第 0 层一切树自比 (对树归纳) | 条件定理 (动作 `HA`) |
| **`snd₀ᴳ`** | MonoPort4Zero | $x\sqsubseteq_0x'$ ⇒ 两动作下输出相关, 一切实例与观测 | 条件定理 (三条 `HA`, 观测律) |
| **`chain₀ᴳ`** | MonoPort4Zero | 第 0 层节点上升的链 | 条件定理 (同上) |
| `O₂`, `pre₂`, `o₀pre`, `o₁pre` | MonoPort4Inst2 | `StrRelDef` 的两层关系满足观测律 | 定理 |
| `snd₀²` | MonoPort4Inst2 | 实例 2 的 `snd₀ᴳ` | 条件定理 |
| 第三站, 一步 $c\to c+1$, 跨世界 | — | 见 §2 | 判断, 未做 |

## 2 第三站还缺的件 (判断)

实例 $\Lambda=3$, 目标 $T_0,T_1,T_2$, 观测取三层关系的积 ($T_0$ 上 $\sqsubseteq_0$, 满足 `proj₀`). 第 0 层输入: **`snd₀ᴳ` 与 `chain₀ᴳ` 直接用** (实例取 3, 观测取三层的积). 还要:

1. **$\sqsubseteq_1$ 加 `nw` (只在 `self`).** 在实例 3 里第 1 层的上下文被第 2 层节点的 `Ai` 读作坐标, 其中有 `nw self _` (`Run` 的 `⨾` 句). `StrRelDef` 的 $\sqsubseteq_1$ 没有 `nw`, 要加 `nwˡ`, `nwʳ` (语义一行: `Run (nw self x) self` 定义性地是 `Run x self`); 核的上下文律取 "$\sqsubseteq_1$ 且两边自比", 九条由构造子拼出 (同 `cl₀`, 多带自比).
2. **$\sqsubseteq_2$.** 两种节点: 第 1 层节点 (坐标按 $\sqsubseteq_1$), 第 0 层节点 (坐标按 $\sqsubseteq_0$, 来自第 1 层输入在 $T_2$ 上保留的节点). 上下文不被读 (取 $\top$, 同 `MonoPort3Two`).
3. **观测律.** 三层逐层给, 同 `O₂`; `PreLaw` 用三条 `o_e pre` 等式.
4. **节点一步, 按节点层 $k$ 对目标层 $e$.** $e\le k$ 上升: $k=0$ 用 `chain₀ᴳ`; $k=1$ 要第 1 层的链 (`chain₀ᴳ` 的同形物, 点按 $\sqsubseteq_1$, 一步用第 1 层的 `snd`), 且要在 $T_0$ **与** $T_1$ 两个目标上读 (输出各是 `nl`, 由 `Lnl` 的分量给). $e>k$ 保留: 分支是 `BNi`, "先在层 $k$ 走坐标、再走分支": $k=0$ 用 `snd₀ᴳ`, $k=1$ 用第 1 层的 `snd`, **都不要规范形**; 写法同 `MonoPort3Two.branch`.
5. **第 1 层的 `snd`** (实例 3): 核加节点一步 (第 0 层节点: $T_0$ 上升, $T_1$, $T_2$ 保留). **第 2 层的 `snd`**: 核加两种节点各三个目标.
6. 外层链 (点在第 2 层)、起点、`mono₃`, `grow₃₄`: 照 `MonoPort2Chain`.

**一步 $c\to c+1$ 的形状.** 上面 4 与 5 对 $k$ 是同一句话: "层 $k$ 的 `snd` (两动作, 一切目标) ⇒ 层 $k+1$ 的节点一步". 要一次写成, 需要把观测按目标层数参数化 (向量或对层数递归的积), 与节点一步对 "$e\le k$ 或 $e>k$" 的统一陈述. 核与 `snd₀ᴳ` 已对实例与观测参数化; 缺的是这一层的参数化. 没有写.

**跨世界版.** 本组一切都在一个世界里, 路径只在 `self` (第 1 层以上) 或任意 (第 0 层, 世界不起作用). 跨世界要把观测改成对两边各自世界里的目标比 (`KValSem` 的路径一致那一套), 核的 `Obs` 是同一世界里的; 不便宜, 没有做.

## 3 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 观测要有 $T_0$ 分量 $\sqsubseteq_0$ (`proj₀`) | 节点上升时链的下一个点是上一段的 $T_0$ 输出, 又作坐标 | 树逼的 (`Chn` 的字面) |
| 上下文律由 $\sqsubseteq_0$ 的构造子拼出 | 第 0 层的上下文是坐标 | 树逼的 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 没有改折叠, 没有 `Lab`, 没有记号. `snd₀ᴳ`, `chain₀ᴳ` 不按站写, 对一切实例与观测. 没有序数值验收.

## 4 账

| 文件 | 行 | 内容 |
|---|---|---|
| `MonoPort4Zero` | 103 | 上下文律, 自比, `snd₀ᴳ`, `chain₀ᴳ` |
| `MonoPort4Inst2` | 42 | 观测律的实例, `snd₀²` |
| 入口 | 4 | |
| 合计 | 149 | |

审计: 导入闭包 (`--only` 同 `MonoPort` 加 `OCF.Align.StrRel`) 入口 34 个模块 (本地 24), 三个文件退出码 0, 禁用表 0, `--only` 之外 0; 无禁用构造; 删掉本组 `.agdai` 后重编退出码 0 (4 秒, 峰值 0.8G).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort4 where

import OCF.Align.MonoPort4Zero
open import OCF.Align.MonoPort4Inst2 using (O₂; pre₂; snd₀²) public
```
