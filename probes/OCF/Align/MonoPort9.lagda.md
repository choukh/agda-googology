# 回灌每一格的严格增长: 入口

> **判决: PARTIAL (编译过的定理).** 对一切合法的 Ω-极限高度 $\mathrm{h\Omega}\,g$, 分支都不含 Ω-极限 (`fg`):
>
> - `MonoPort9Cell.Cell.growC`: 对**一切** $n$ 与回灌第 $n$ 格走过的**一切**坐标 $c$, $T_{g(c)} < T_{\mathrm{h\Omega}\,g}$; `growC∃`: 每一格都有走过的坐标 (前提可满足).
> - 对 $\Omega$ 本身 (`Ωᴴ = hΩ emb`) 无前提 (`growΩᴴC`), 合上 `MonoPort7Lim.grow≪` 得 `below≪`: 对一切 $a \ll c$ ($c$ 是某一格走过的坐标), $T_a < T_\Omega$.
> - **否定** `MonoPort9Neg.no-all`: 对任何合法 $\Lambda$, "对一切可数 $a$, $T_a<T_\Lambda$" 是假的 (反例 $a=T_\Lambda$, 因为 $a\le T_a$, `id≤T`). 所以接手清单第 4 项的 "对一切可数高度 $a$, 无前提" 不可能; 能有的是 "某个界之下的 $a$". 界: 走过的坐标都在 $V_\omega$ 之下, 且 $V_\omega$ 与 $T_\Lambda$ 在值上互相 $\le$ (`Vω≤T`, `T≤Vω`).
>
> **`GoodUp` 没有证** (接手清单第 1 项). 第 2–4 项不经过它: 把全部格在同一个世界 $V_\omega$ 里重做 (`MonoPort9Walk`), 实际的格与重做的格在一切不含 Ω-极限的目标对上读数互模拟 (`ZE`, `cellE`), 重做的一边只用单世界关系. 路线 (a) 为什么没走通见 §3 (判断, 没有否定定理, 写 "未走通").
>
> 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义, 不改已有文件. 严格增长是**值的定理** ($T_a < T_\Lambda$), 不是强度的序数值验收.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `id≤T` | MonoPort9Neg | 一切合法可数 $a$: $a \le T_{\mathrm{emb}\,a}$ | 定理 |
| **`no-all`**, `no-allΩ` | MonoPort9Neg | 任何合法 $\Lambda$: $\neg\,\forall a\,(la : \mathrm{Lg}\,a).\ T_a < T_\Lambda$ | **否定, 定理** (只否定 "一切 $a$ 无条件" 这一形状) |
| `TwoF` (`DfE`, `Run-E` 一族七条) | MonoPort9Two | `MonoPort8Sim.Two` 的克隆: `at` 多前提 `Free t`; 节点层不含 Ω-极限由参数 `frk` 给 | 定义, 定理 (脚本生成) |
| `frkΩ` | MonoPort9Walk | $\mathrm{h\Omega}\,g$ 的严格下层 (节点层) 不含 Ω-极限 (分支都 `Free`) | 定理 |
| `CutE`, `Walk-E`, `WRp-E` | MonoPort9Walk | 两个世界里同一条坐标路径上的 `Walk`: 相关的上下文、状态 ⇒ 输出互模拟 | 定理 |
| `Z`, `Δ′`, `co′` | MonoPort9Walk | 全部格在世界 $V_\omega=\lim_n V_n$ 里重做 | 定义 (证明工具, 不进树或折叠) |
| **`ZE`, `cellE`, `cell≈`** | MonoPort9Walk | 实际第 $n$ 格的起始状态 / 输出 与重做的互模拟; 第 0 层的和相等 | **定理** (分支 `Free`) |
| `Walked` | MonoPort9One | 坐标 $c$ 被一次 `Walk` 走过 (照 `Walk` 三句的四个构造子) | 定义 |
| `Node.low`, `Node.strict` | MonoPort9One | 一个节点, 状态自洽且以字面起始段为最左一段, 底 $\beta\ge1$: $T_{g(c)} <$ 节点的和 | 条件定理 (`Good`, `Pfx`) |
| `WG`, `WRG`, `WRP` | MonoPort9One | 单世界: 状态自洽 ⇒ `Walk` 输出与自己相关; `WRp` 的状态保持自洽与前缀 | 条件定理 (`Good`) |
| **`WL`** | MonoPort9One | 对 `Walk` 的路径归纳: 一切走过的 $c$, $T_{g(c)} <$ `Walk` 的和 | **条件定理** (`Good`, `Pfx`, $\beta\ge1$) |
| `gZ`, `pZ` | MonoPort9Cell | 重做的状态自洽、带前缀 (对 $n$ 归纳) | 定理 |
| `wExt`, `wL4`, `L4′`, `nzCell` | MonoPort9Inh | 照 `HtFeedGrow.G.W.L4`: 每一格在第 0 层非零 | 定理 |
| `walked` | MonoPort9Inh | 每一格都走过某个坐标 | 定理 |
| **`growC`**, `growC∃` | MonoPort9Cell | 分支都 `Free` ⇒ $\forall n$, 第 $n$ 格走过的 $\forall c$: $T_{g(c)} < T_{\mathrm{h\Omega}\,g}$; 每格都有这样的 $c$ | **条件定理** (`fg`) |
| `Vω≤T`, `T≤Vω` | MonoPort9Cell | $V_\omega$ 与 $T_{\mathrm{h\Omega}\,g}$ 在值上互相 $\le$ | 条件定理 (`fg`, 只为模块参数) |
| `ex0`, `exS` | MonoPort9Cell | 第 0 格走过 $0$ 与一切 $1+m$ | 定理 |
| **`growΩᴴC`** | MonoPort9Cell | $\Omega$: 一切格的一切走过的 $c$, $T_{c} < T_\Omega$ | **定理, 无前提** |
| **`below≪`** | MonoPort9Cell | $a \ll c$, $c$ 走过 ⇒ $T_a < T_\Omega$ | **定理** (前提 $a\ll c$ 与 $c$ 走过; 由 `walked` 可满足) |
| `GoodUp` | — | 见 §3 | 未做 |

## 2 条件定理的前提与实例

- `fg : ∀ c → Free (g c)`: 对 `Ωᴴ` 是 `free-emb` (`growΩᴴC`, `below≪` 都已填上). 不满足的例子: 分支本身含 Ω-极限 (如 $\Omega\cdot2$ 一类); 那时 `TwoF` 用不上 (节点层的 `frk` 不成立), 不在本任务内.
- `growC n` 的前提 `Walked … c`: `growC∃ n` 给出每个 $n$ 的实例 (`MonoPort9Inh.walked`); 第 0 格还有具体的 `ex0` ($c=0$), `exS m` ($c=1+m$).
- `WL`, `Node.low` 的 `Good`, `Pfx`, `one ≤ β`: 由 `gZ`, `pZ`, `ptb` 对一切 $n$ 填上 (`growC` 里).
- `below≪` 的 $a \ll c$: 例如 `ex0`, `exS` 之下的一切 $a$; 对 $n\ge1$ 的格, `walked` 给出 $c$, 它之下的 $a$ 都可以.

## 3 判断与第一个障碍

**`GoodUp` 与路线 (a) (判断, 未走通, 没有否定定理).** 路线 (a) 是 "把 `≼` 改成对一切目标世界 $m\ge W$ 量化, 每个 $m$ 上用 `Rel_m`, 证明逐句换下标". 读 `MonoPort7Snd.Node.rkRel` 与 `MonoPort3Gen.Core` 后的判断: 只改输出关系不够. 核 (`Core`) 对输出关系是抽象的 (`OutLaws`), 所以和构造子那一半确实只是换实例; 但节点那一句在目标世界 $m\neq W$ 上的 "上升" 情形, 读的是世界 $W$ 里的链 (`Chn`), 链项是状态读数的折叠, 读数里有前面节点 "保留" 时的输出 `ni R′ (λ p … → BNi … (⊲-tr wm p) …)`, 它们的分支依赖路径 $p$. 在世界 $m$ 的目标上读时, 用到的是这些分支在路径 $\mathrm{wm}\neq\mathrm{self}$ 上的值, 而输入关系 `RelM` 的 `ni⊑` 只比 `C.self lW` 上的分支 (`MonoPort5Rel`). 所以输入关系也要改成对一切路径 $p:W\lhd V$ 比分支 (每个 $V$ 上用 `Rel_V`), 上下文里随之出现任意路径的 `nw`, 第 $\ge1$ 层的输入也要从任意低世界经任意路径进来 (`Core` 的 `TW`/`Path` 现在取单点). 这改的是关系的形状, 不是下标; 本组没有动手. 没有编译过的否定, 只写 "未走通".

**本组的做法与 (b) 的关系.** `MonoPort8` §3 的路线 (b) 是 "对 $\Delta_n$ 在 $V_{n+1}$ 上的读数用互模拟, 再由 `nodeSelf` 得自洽", 卡在 "互模拟 ⇒ `Rel`". 本组用了 (b) 的前一半 (放宽 `fr`, 即 `TwoF`), 但不把互模拟换回 `Rel`: 把全部格在同一个世界 $V_\omega$ 里重做, 自洽只在重做的一边要 (单世界, `nodeSelf`), 实际的一边只要和 (第 0 层的互模拟给出和相等, `sumE`). 所以 "互模拟 ⇒ `Rel`" 这一环不再需要.

**StrRel12 的 `R∀c` (判断).** 统筹转告: `R∀c` 对一切对齐目标对量化, 经 `cv` 封闭, 但与单世界 `Good` 没有互译, 自反还缺 `Al-refl`. 本组的结果不需要 `GoodUp`, 所以没有评估改从 `R∀c` 取 `GoodUp`; 若以后要 `GoodUp` 本身 (例如要在实际的世界 $V_n$ 里用 `ΩdObs`), 判断要的是 "`R∀c Y Y` ⇒ 单世界 `Good` 在抬升后的目标上" 这一条译法, 加上 `R∀c` 的自反.

**范围上的判断.** $V_\omega$ 与 $T_\Lambda$ 在值上相等 (定理). 走过的坐标覆盖 $V_\omega$ 之下的哪些 $a$ (例如 "一切 $a \ll V_\omega$ 都在某个走过的 $c$ 之下") 没有证; 判断: 每一格沿 `sum-fst` 的路径走, 路径上的后继都被走到, 应当覆盖, 但 `Walked` 与 `_≪_` 之间的引理没写. 若成立, `below≪` 合上 `no-all` 就把 "$T_a<T_\Omega$" 的范围定在 $a$ 低于 $V_\omega$ 的值附近 (判断, 没有在 $V_\omega$ 与 $T_\Omega$ 之间逐点比较).

**第一个障碍 (下一站).** 分支含 Ω-极限 (本任务外): `TwoF` 要节点层不含 Ω-极限 (`frk`), `MonoPort8Sim.no-κE` 说本组的互模拟装不下 Ω-极限层的 $\Omega_L$; 单世界 `Rel` 在 `hΩ` 层是 $\top$. 同一个障碍挡住 $T_\Omega < T_{\Omega+1}$: `MonoPort7Lim.Suc.growS` 要 `Free Λ`, $\Omega_{\Omega+1}$ 的节点层是 $\Omega$ 本身, 上升时的链读状态在层 $\Omega$ 上的读数, 读数含 `nκ`.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `TwoF`: `at` 多 `Free t`, 参数 `frk` | 实例 $\mathrm{h\Omega}\,g$ 自己是目标层 (`hself`), 它的 $\Omega_\Lambda$ 含 `nκ`, 互模拟装不下 (`no-κE`); 节点层严格低于实例 | 树逼的 |
| `Walk-E`, `WRp-E`, `CutE` | `Walk`, `WRp`, `Cut` 的字面 | 树逼的 |
| 重做 $Z$, $\Delta'$ 于 $V_\omega$ | 单世界关系只读一个世界的目标; $V_\omega$ 合法由 `κc` 的 `av`, `lv` 给出 | 证明工具 (第 4 层), 不进树、折叠、合法性 |
| `Walked` | `Walk` 的三句 (`self`, `suc`, `lim` 与 `stp (m + n)`) | 树逼的 |
| `strict` 用起始段 $\omega\cdot(\Omega_{g(c)}⨾0)$ 的第二份 | `Step` 的字面 (`ω⋅ c = nl (λ _ → c)`), `Act` 在作用点上是 `Step` | 树逼的 |
| `L4′`, `wL4` | `HtFeedGrow.G.W.L4` 的同一归纳 (节点族换成 $u$, 起点 $0$) | 树逼的 (已有形状) |
| `id≤T`, `no-all` | `Suc.growS`, `Lim.growL`, `irr` | 树逼的 |
| `Vω≤T`, `T≤Vω` | `κc` 的 `v` 与闭项 `TΛ≡` 的字面, `drp` 不改和 | 树逼的 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有记号. 闭包定理不按站定制: `growC` 对一切分支不含 Ω-极限的 $\mathrm{h\Omega}\,g$、一切格、一切走过的坐标. 这一站新用到的字段: 回灌第 $n\ge1$ 格的世界 $V_n=\mathrm{sum}\,V_{n-1}\,\Delta_{n-1}$ 与路径 `sum-fst` (`κc` 的 `suc` 一句), `Sv` 之间的 `cv` (`cvL`), `Walk` 的 `lim` 一句里的 `WRp`. 否定 `no-all` 划出不能有的陈述: 无界的 "一切 $a$".

## 5 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `MonoPort9Neg` | 24 | `id≤T`, `no-all` (手写) |
| `MonoPort9Two` | 158 | **生成** (`mk_two.py`): `MonoPort8Sim` §6–7 加 `Free t` |
| `MonoPort9One` | 171 | `Walked`, `Node`, `WG`, `WL` (手写) |
| `MonoPort9Walk` | 106 | `frkΩ`, `Walk-E`, 重做, `ZE`, `cellE` (手写) |
| `MonoPort9Inh` | 97 | `L4′`, `wL4`, `nzCell`, `walked` (手写) |
| `MonoPort9Cell` | 80 | `gZ`, `growC`, `Vω≤T`/`T≤Vω`, Ω 特例 (手写) |
| 入口 | 8 | |
| 合计 | 644 | 生成 158, 手写 486 |

生成脚本: `probes/Survey/scripts/monoport9/mk_two.py` 与它读的 `two_header.md`; 从仓库根运行 `python3 probes/Survey/scripts/monoport9/mk_two.py .` 逐字节重新生成 `MonoPort9Two`.

审计 (2026-11-05):

- 编译: 删掉本组 7 个 `.agdai` 后从入口重编, 退出码 0, 约 8 秒, 峰值常驻约 1.0G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0. 终止全由编译器的结构检查给出 (`Walk-E`/`WRp-E`/`WG`/`WRG`/`WL` 与 `Walk` 同一个度量: 坐标的结构; `wL4`/`L4′` 对第 0 层的树; `ZE`/`cellE`/`gZ`/`nzCell` 对 ℕ).
- 生成文件: `mk_two.py` 重跑, 输出与仓库里的 `MonoPort9Two` 逐字节相同 (md5).
- 导入闭包 (`importclosure.py`, `--only` 同 `MonoPort8`): 入口闭包 67 个模块 (本地 57, 库 10), 七个文件各自单跑也都是禁用表 0, `--only` 之外 0. 闭包里的 `DValCanon` 与 `MonoPort6`/`7`/`8` 一样经 `MonoPort3Gen → MonoPortBridge` 带进来 (只导入不使用).
- 定义级切片 (`depslice.py`): `below≪` 到达 698 块, `growC∃` 599, `growΩᴴC` 582, `growC` 574, `T≤Vω` 573, `no-all` 528, `WL` 505, `cellE` 194, `walked` 156, `Run-E` 150, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9 where

open import OCF.Align.MonoPort9Neg using (id≤T; no-all; no-allΩ) public
open import OCF.Align.MonoPort9Two using (module TwoF) public
open import OCF.Align.MonoPort9One using (Walked; module One) public
open import OCF.Align.MonoPort9Walk using (frkΩ; module WE) public
open import OCF.Align.MonoPort9Inh using (module Inh) public
open import OCF.Align.MonoPort9Cell using (module Cell; growΩᴴC; below≪) public
```
