# 极限高度上严格增长: 入口

> **判决: HOLDS (编译过的定理, 无前提), 范围是一切不含 Ω-极限的高度.** `MonoL` (`HtCrossVInst.Hl.N.MonoL n`) 对一切 `hl f` (各 $f(n)$ 不含 Ω-极限) 成立 (`MonoPort7Lim.Lim.monoL`), 于是 $T_{f(n)} < T_{\mathrm{hl}\,f}$ (`Lim.growL`); 特例高度 $\omega$: `growω : ∀ n → asuc (TΛ (N n)) ≤ TΛ (hl N)`. 同一个引理也给出一切不含 Ω-极限的 $\Lambda$ 的后继一步 (`Suc.monoS`, `Suc.growS`), 所以在一切可数高度上沿 $\ll$ 严格增长: `grow≪ : a ≪ b → TΛ (emb a) < TΛ (emb b)`. 第一个 Ω-极限高度 `Ωᴴ` 未做 (§3). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义, 不改已有文件.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Rel`, `RelN`, `CxN`, 输出律, `rΩ` | MonoPort7Rel | `MonoPort6Rel` 的结构关系推广到层 `hl f` (原来是 $\top$): 同一个 `RelM`; `Fin` = 不含 Ω-极限 | 定义, 定理 (脚本生成) |
| `IntMK`, `IntMS` | MonoPort7Int | 源层带节点的 `Int` 单调, 对层 $L$ 写一次 (`hs`, `hl`), 节点任意 | 条件定理 (分支三条单调; 同 `MonoPort6Int`) |
| `L.*`, `HAKN` | MonoPort7Lay | 层 $L$ 的核实例 | 定理 / 条件定理 |
| `chainK`, `brnK`, `Node.step`, **`sndS`, `sndArg`** | MonoPort7Snd | 节点一步与 (良基证明, 推导) 归纳, 对一切 `Fin` 层 (含 `hl`) | 定理 (`Fin`) |
| `HAKb`, `hSt`, `hAi` | MonoPort7Node | 不看上下文的动作前提; 常数分支节点的坐标动作前提由它直接给出 | 定义, 定理 |
| `RKb`, `conv` | MonoPort7Node | 节点输出只经 (子层良基证明, 子层位置, 坐标动作) 依赖节点; `conv` 对 `Rk` 两种值各 `refl` | 定义, 定理 |
| `relB` | MonoPort7Node | `RKb` 上的关系 (照 `Node.rkRel`, 坐标动作任意) | 条件定理 (三条 `HAK`, 状态 `Good`/`SRel`; 子层 `Fin`) |
| `nodeSelf`, `ndS`, `ndL` | MonoPort7Node | 常数分支节点 (`ss hself`, `sl m hself`) 两边 (世界、嵌入、良基证明写法可不同) 的输出相关 | 条件定理 (`HAKb`, 状态) |
| **`ΩdObs`** | MonoPort7Node | 一切 `Fin` 层 $k$, 一切实例: $\Omega_k$ 在两个世界里的两次折叠的观测相关 | 条件定理 (两个动作的 `HAKb`, 状态 `Good`/`SRel`, 底 $\le$; 实例里全部填上) |
| **`Suc.monoS`, `Suc.growS`** | MonoPort7Lim | 一切不含 Ω-极限的 $\Lambda$: `MonoStep Λ`; $T_\Lambda < T_{\Lambda+1}$ | **定理 (`Free Λ`)** |
| **`Lim.monoL`, `Lim.growL`** | MonoPort7Lim | 一切 `hl f`, `Free (hl f)`: `MonoL n`; $T_{f(n)} < T_{\mathrm{hl}\,f}$ | **定理 (`Free (hl f)`)** |
| **`grow≪`** | MonoPort7Lim | 一切 $a \ll b$ (在 $A$ 里): `asuc (TΛ (emb a)) ≤ TΛ (emb b)` | **定理 (无前提)** |
| **`growω`**, `growω₀`, `growω1`, `growω2` | MonoPort7Lim | $T_n < T_\omega$; $T_0 + n < T_\omega$; $T_\omega < T_{\omega+1}$; $T_{\omega+n} < T_{\omega\cdot2}$ | **定理 (无前提)** |
| 第一个 Ω-极限高度 `Ωᴴ` | — | 见 §3 | 未做 |

## 2 怎么绕开 `MonoPort6` §3 的障碍

`MonoPort6` §3 写下的障碍是: `MonoL` 两边的 $\Omega_{f(n)}$ 在不同世界里进入 (`{azero}` 经 `z⊲ one` 对 `{one}` 在 `C.self`), 节点嵌入 `mkOf r (⊲-tr q₀ p)` 两边不同, 而 `IntMS` 要两边同一个 `mk`. 那里写的出路 (未试) 是对 `Ωd` 这一棵树直接写动作前提. 本组照这个做, 并发现它是对的, 而且更一般:

- **不经 `IntMK`.** $\Omega_k$ 的节点分支是常数 `n1`, 坐标动作 `Ai` 在作用点上定义性地是外层动作作用在丢掉的上下文上. 只要外层动作不看上下文 (`HAKb`), `Ai` 的 `HAK` 就由它给出 (`hAi`, 一行), `mk` 与 `Int` 根本不出现.
- **世界与嵌入从输出里消失.** 折叠在节点处的输出只经三样依赖节点 (`RKb`, `conv`). 对 `ss hself`, `sl m hself`, `Kup q₀` 定义性地不动节点, 两边的 `kk` 化成同一个位置; 良基证明的两种写法 (`accᴸ`, `accL k`) 在具体节点处化成同一个 `accL j` (选择子 `Ac`, `toBs`, `toBl`). 所以只用一个世界上的关系 (`MonoPort6` 的 `Rel`), 不需要跨世界的关系.
- **`hl` 层.** `MonoL` 的 $f(n)$ 本身可以是 `hl`, 后继一步的 $\Lambda$ 也可以是 `hl`; 这要层 `hl` 上的结构关系与语义. `RelM` 本来对任意层定义, `MonoPort6` 只是把 `Rel (hl f)` 取成 $\top$. 本组把 `MonoPort6Rel`, `MonoPort6Int`, `MonoPort6Lay`, `MonoPort6Snd` 按层 $L$ 写一次 (脚本生成, 证明逐句不变; 改动列在各文件头), 新增的只有: `Rel (hl f)` 取 `RelM`, `Rel L` 与 `RelN L` 之间的定义性换写 `toN`/`fromN`, 目标 `hl` 的保留一句.
- **后继一步也是 `ΩdObs`.** `MonoStep Λ` 的两边正是 $\Omega_\Lambda$ 在两个世界里的折叠 (状态 `Y₀` 对 `(Y₀ ⊕ Step Y₀) ⊕ 0`). 所以 `MonoPort6Chain` 的外层链 (`MonoPortStep.Ch`) 不再需要: 它就是 `ΩdObs` 里节点上升时的子层链.

## 3 未做: 第一个 Ω-极限高度 `Ωᴴ` (判断)

`HtCrossVInst` 对 `hΩ` 只有换实例 (`hΩ-in′`), 没有 `hs`/`hl` 那样的展开与归约 (`hs-reduce<′`, `hl-reduce<′`). 第一个障碍在写出这一步之前: $\Omega_{\mathrm{hΩ}\,g} = 1 ⨾ \mathrm{nκ}\,\ldots$, 它在第 0 层目标上的折叠是 `RKy … hz` 的回灌: 在世界 $v(\kappa_c\,n) > 1$ 里沿 `Walk` 走 (`κc`, `κΔ`), 节点是 `sL e hself`, 读数经 `drp` 回到世界 $1$. 本组的关系只在一个世界 $W$ 上 (`Tt` 取 `C.self`), `Rel (hΩ g) = ⊤`, 且 `HtCrossVNeg.no-κ` 说明不带 nκ 的关系装不下 Ω-极限. 所以要的是跨世界、含 nκ 的关系 (方向: `StrRel7`/`StrRel8` 的 `snd⁺`). 没有否定定理, 只是没做.

另一个范围说明 [判断]: 本组的严格增长是值的定理 ($T_\Lambda < T_{\Lambda'}$), 不是强度的序数值验收.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `HAKb` (动作前提不看上下文) | `Act`, `A²`, 常数分支节点的 `Ai` 在作用点上丢掉上下文 (`Ai` 与 `Run … n1` 的字面) | 树逼的 |
| `RKb`, `conv` | `RKi` 只经 `ac′`, `kk r q₀ ll`, `Ai …` 依赖节点 (`RKi`, `BNi` 的字面) | 树逼的 |
| 选择子 `Ac` (`accᴸ` / `accL k`) | `MonoStep` 与 `MonoL` 右边的良基证明写法不同, 只在具体节点处化成同一个 | 脚手架 (工程; 定义性化简的需要, 不是序数值需要的) |
| `Rel (hl f)` 取 `RelM`, `CxN`, `toN`/`fromN` | 层 `hl` 上的节点 `sl n P` 与 `ss P` 同形; 换写是抽象层号下定义性化简的需要 | `RelM` 是树逼的 (已有); 换写是脚手架 |
| `ndL`, `Lm.inv` (部分和状态的归纳) | $\Omega_{\mathrm{hl}\,g}$ 的第二段是 `nl` of 节点, 折叠 `Rpt` 累积状态 | 树逼的 |
| `Fin` 收进 `hl` (= `Free`) | 关系需要子层的语义, `hl` 的子层是 $f(n)$ | 树逼的 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 不改折叠, 没有 `Lab`, 没有记号. 闭包定理不按站定制: 一个 `ΩdObs` 对一切不含 Ω-极限的层、一切实例, 同时给出后继与极限两种一步; 这一站新用到的字段: `Ωd` 的分支是常数 `n1` (使 `HAKb` 够用), 节点 `ss hself`/`sl m hself` 的位置是 `hself` (使 `Kup` 不动它), `hl` 的节点 `sl n P` (`ndL`, `rkRel` 的目标 `hl`). 没有加深翻译: 定义不变, 新的只有关于折叠字面的引理与工程换写.

## 5 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `MonoPort7Rel` | 236 | 生成 (`mk_rel.py`): `MonoPort6Rel` 加 `hl` |
| `MonoPort7Int` | 237 | 生成 (`mk_int.py`): `IntMS` 对层 $L$ |
| `MonoPort7Lay` | 85 | 生成 (`mk_lay.py`) |
| `MonoPort7Snd` | 172 | 生成 (`mk_snd.py`; 前半手写在 `snd_mid.txt`) |
| `MonoPort7Node` | 181 | 手写: `HAKb`, `RKb`, `conv`, `relB`, `nodeSelf`, `Ac`, `ndS`, `ndL`, `ΩdObs` |
| `MonoPort7Lim` | 110 | 手写: `Suc`, `Lim`, `grow≪`, 特例 |
| 入口 | 4 | |
| 合计 | 1025 | 其中生成 730 (与 `MonoPort6` 对应文件逐句相同的占大半), 手写 295 |

生成脚本在 `probes/Survey/scripts/monoport7/` (`mk_rel.py`, `mk_int.py`, `mk_lay.py`, `mk_snd.py` 与它们读的头注、`snd_mid.txt`), 从仓库根运行 `python3 probes/Survey/scripts/monoport7/mk_<x>.py .` 逐字节重新生成.

审计 (2026-11-05):

- 编译: 删掉本组 7 个 `.agdai` 后从入口重编, 退出码 0, 约 11 秒, 峰值常驻约 1.2G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0. 终止全由编译器的结构检查给出 (`sndS`/`IntMS` 对良基证明与推导, `Lm.inv` 对 ℕ).
- 生成文件: 四个脚本重跑, 输出与仓库里的文件逐字节相同 (md5 核对).
- 导入闭包 (`importclosure.py`, `--only` 同简报: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 入口闭包 58 个模块 (本地 48, 库 10), 禁用表 0, `--only` 之外 0. 闭包里的 `DValCanon` 与 `MonoPort6` 一样经 `MonoPort3Gen → MonoPortBridge` 带进来 (只导入不使用); 本组不用规范形, 不用左边极限截断.
- 定义级切片 (`depslice.py`): `grow≪` 到达 528 块, `growω` 508, `ΩdObs` 371, `sndS` 337, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort7 where

open import OCF.Align.MonoPort7Lim using (module Suc; module Lim; grow≪; growω; growω₀; growω1; growω2) public
import OCF.Align.MonoPort7Node
```
