# 第一个 Ω-极限高度上的严格增长: 入口

> **判决: PARTIAL (编译过的定理).** 对一切合法的 Ω-极限高度 $\mathrm{h\Omega}\,g$:
>
> - `MonoPort8Om.Om.growΩ₀`: 分支 $g(0)$ 不含 Ω-极限 ⇒ $T_{g(0)} < T_{\mathrm{h\Omega}\,g}$;
> - `MonoPort8Fin.Fn.growΩf`: 分支都不含 Ω-极限 ⇒ 对回灌第 $0$ 格世界 $V_0=\lim_m f(m)$ 的每个字面项 $f(m)$, $T_{g(f(m))} < T_{\mathrm{h\Omega}\,g}$.
>
> 对 $\Omega$ 本身 (`Ωᴴ = hΩ emb`) 两条都无前提 (`growΩᴴ₀`, `growΩᴴf`): $T_{0} < T_{\Omega}$, 且对一切 $m$, $T_{\mathrm{emb}\,f(m)} < T_{\Omega}$; `emb (f m)` 就是有限高度 $m+1$ (`embf`), 合起来是 `growΩᴴN : ∀ n → T_n < T_Ω`. 一切可数高度 $a$ 上的 $T_a < T_\Omega$ **没有做到**: 要第 $n\ge1$ 格的坐标, 第一个障碍见 §3.
>
> **对 `MonoPort7` §3 那个障碍的回答.** 那里判断 "要跨世界、含 `nκ` 的关系". 编译结果是: 对 Ω-极限高度的**某个分支** $g(c)$ 与整体的严格增长, `nκ` 的关系可以避开, 跨世界不能避开, 但跨世界所需的只是**不含回灌的折叠与世界无关** (`MonoPort8Sim.changeW`, 一个互模拟, 不是 `≤` 方向的语义, 不比路径, 不要对齐). 避开 `nκ` 的办法: 回灌 `nκ` 只在 $T_{\mathrm{h\Omega}\,g}$ 这一边出现, 第 $0$ 格的世界与走法是具体的 (`κ 0`, `Walk` 在 $V_0$ 的字面上逐句定义性地展开), 所以不需要关于 `nκ` 的关系, 只要对展开后的节点 (层 $g(c)$, 不含 Ω-极限) 用 `MonoPort7` 的单世界关系 (`ΩdObs`, `nodeSelf`). 另一边 $T_{g(c)}$ 在世界 $1$ 里, 节点在世界 $V_0$ 里, 两者之间就是 `changeW`.
>
> 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义, 不改已有文件. 严格增长是**值的定理** ($T_\Lambda < T_{\Lambda'}$), 不是强度的序数值验收.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `SimE`, `RelE`, `Re` | MonoPort8Sim | `HtCrossVSim.SimD` 两边世界各自独立; 节点对一切两条路径、两个 `Lg` 比分支; 没有 `nκ` | 定义 |
| `reH`, `reS` | MonoPort8Sim | 不含 Ω-极限的层: 位置与节点种类换世界 | 定理 |
| `Two.Run-E` 与六个同伴 | MonoPort8Sim | 两个实例、两个外层世界、一切目标对 (世界、路径、位置、`Lg` 各自任意): 相关的输入折叠出相关的输出; 共有目标层不含 Ω-极限 | 定理 |
| **`changeW`** | MonoPort8Sim | `Free Λ` ⇒ $T_\Lambda$ 与 $\Omega_\Lambda$ 在任意实例 $\Lambda'$、任意世界 $W$、任意位置 $e:\Lambda\lhd_{[W]}\Lambda'$ 上的折叠的和互相 $\le$ | **定理** |
| `no-κE` | MonoPort8Sim | $\neg$ `Re (hΩ g) (Ωd (hΩ g)) (Ωd (hΩ g))`, 一切 $g$ 与两个世界 | 否定, 定理 (只否定本关系覆盖 Ω-极限层的 $\Omega_L$) |
| `drp≤` | MonoPort8Om | `drp` 不降和 | 定理 |
| `TΛ≡` | MonoPort8Om | $T_{\mathrm{h\Omega}\,g} = \lim(\mathrm{pt}\,b\,D)$, $D_n$ 是第 $n$ 格 | 定理 (`refl`) |
| `strict` | MonoPort8Om | 第 $0$ 格的和严格高于坐标 $0$ 节点的和 (坐标 $1$ 的节点非零) | 定理 |
| `Low.low` | MonoPort8Om | `Free (g 0)` ⇒ $T_{g(0)} \le$ 坐标 $0$ 节点的和 | 条件定理 (`Free (g 0)`) |
| **`growΩ₀`** | MonoPort8Om | `Free (g 0)` ⇒ $T_{g(0)} < T_{\mathrm{h\Omega}\,g}$ | **条件定理** |
| **`growΩᴴ₀`** | MonoPort8Om | $T_0 < T_\Omega$ | **定理, 无前提** |
| `HasPfx`, `pfxRun` | MonoPort8Fin | 左脊前缀的折叠的和不高于整体 | 定义, 定理 |
| `gWR`, `iWR`, `pfxY` | MonoPort8Fin | 第 $0$ 格第 $m$ 段的状态: 自洽 (含前 $m$ 个节点的输出), 非零, 读数以 `Sv` 为最左一段 | 条件定理 (分支 `Free`) |
| **`growΩf`** | MonoPort8Fin | 分支都 `Free` ⇒ $\forall m$, $T_{g(f(m))} < T_{\mathrm{h\Omega}\,g}$ | **条件定理** |
| **`growΩᴴf`** | MonoPort8Fin | $\forall m$, $T_{\mathrm{emb}\,f(m)} < T_\Omega$ | **定理, 无前提** |
| `embf` | MonoPort8Fin | `emb (f m) ≡ N (suc m)` | 定理 |
| **`growΩᴴN`** | MonoPort8Fin | 一切有限 $n$: $T_n < T_\Omega$ | **定理, 无前提** |
| 第 $n\ge1$ 格的坐标 | — | 见 §3 | 未做 |

## 2 条件定理的前提与实例

- `growΩ₀` 的前提 `Free (g azero)`: 对 `Ωᴴ` 是 `tt` (`growΩᴴ₀`); 对一切分支是可数高度的 `hΩ g` 都成立.
- `growΩf` 的前提 `∀ c → Free (g c)`: 对 `Ωᴴ` 是 `free-emb` (`growΩᴴf`). 不满足的例子: $\Omega_{\Omega\cdot 2}$ 一类 (分支本身含 Ω-极限); 那时 `changeW` 用不上 (`no-κE` 说本关系装不下 Ω-极限层的 $\Omega_L$).
- `changeW` 的前提 `Free Λ`: 一切 `emb a` (`HtCrossVInst.free-emb`).

## 3 第一个障碍: 第 $n\ge1$ 格 (判断)

第 $0$ 格的起始状态 `Sv (κ 0)` 是 `cv` 过的 $Y_0\oplus\mathrm{Step}\,Y_0$, 它在世界 $V_0$ 的每个目标上的读数是字面的 $0 ⨾ \omega\cdot(\Omega_t ⨾ 0)$, 所以自洽 (`MonoPort7` 的 `Good`) 直接写出 (`gSv`); 格内后来加进状态的节点输出是同一世界 $V_0$ 里的折叠, 自洽由 `nodeSelf` 给 (`gWR`). 第 $n+1$ 格的起始状态是 `cv q (Sv (κ n) ⊕ Δ_n)`: 第 $n$ 格在世界 $V_n$ 里的输出 $\Delta_n$, 在更大的世界 $V_{n+1}$ 的目标上读. `MonoPort7` 的关系只在一个世界 $W$ 上, `Good` 只量化 $m=W$ 的目标 (`Tt`), 不说 $\Delta_n$ 在 $m\ne W$ 的目标上的读数. 所以要的是:

    GoodUp : ∀ {W W′} (q : W ⊲ W′) (lW′ : Lg W′) → (Δ 是世界 W 里不含回灌的节点折叠的输出, 状态 Good) →
             ∀ {t} (tm : t ⊲[ W′ ] Λ) → Rel_{W′} t (yc Δ (tg q tm lW′)) (yc Δ (tg q tm lW′))

这不是关于 `nκ` 的关系 (被读的是节点输出, 不含回灌), 是单世界关系对 "目标世界抬升" 的封闭. 两条可能的路 (都未试):

1. 把 `MonoPort6/7` 的 `Rel`/`≼`/`Good` 改成对一切目标世界 $m\ge W$ 量化 (每个 $m$ 上用 `Rel_m`), 语义随之重证. 判断: 是 `MonoPort7Rel`–`MonoPort7Snd` 那样的生成克隆, 证明逐句换下标.
2. 用 `MonoPort8Sim` 的互模拟: $\Delta_n$ 在 $(t,V_{n+1})$ 上的读数与 "在 $V_{n+1}$ 里重做同一折叠" 的读数互模拟 (要把 `Two` 的 `fr` 放宽成 "只在不含 Ω-极限的目标上比", 实例 $\mathrm{h\Omega}\,g$ 的唯一含 Ω-极限的目标是它自己, `Rel` 在那里是 $\top$), 再由 `nodeSelf` (世界 $V_{n+1}$) 得自洽. 缺的一环是 "互模拟 ⇒ `Rel`": `SimE` 允许两边节点种类不同 (`R ≠ R′`), `RelM.ni⊑` 要同一个 `r`. 抬升前后两边的节点种类是同一位置的两种写法 (`⊲ᴴ↑ q` 与否), 判断要一条位置相等的引理加 `subst`.

另有一件工程: 第 $n\ge1$ 格的世界 $V_n=\mathrm{sum}\,V_{n-1}\,\Delta_{n-1}$ 不是具体的, `Walk` 不会定义性地展开, 要对 `Walk` 的路径归纳 (节点、`suc`、`lim` 三句, `WRp` 的状态) 写一次 "每个走过的坐标 $c$ 上 $T_{g(c)}$ 低于该格的和". 本组的 `pfxRun`, `strict` 的形状都对一般的格成立, 只有状态自洽要 `GoodUp`.

与 `StrRel12` 的接口 (判断): `StrRel11Tg` 的 `cvR` 说对齐目标对上的读数关系经 `cv` 保持; 若 `StrRel12` 给出 "单世界 `Rel` 在 (同一状态, 抬升后的目标) 这一对上成立" 的可靠性, 它就是 `GoodUp`. 本组不碰 `StrRel12` 的文件.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `SimE` 两边世界独立, 分支对一切路径对比 | 两次折叠的外层世界不同 ($1$ 对 $V_0$), 读数目标的世界不同 ($m$ 对 $m'$), 折叠产出的节点分支在任意路径上取 | 树逼的 (`HtCrossVSim` 的推广, 没有新字段) |
| `reH`, `reS` | 判定一致要把 `StH m k t` 搬到 `StH m′ k t`; 不含 Ω-极限的位置里没有 `hLim` | 树逼的 |
| 比较的是链第 $0$ 项里的第一次 $\Omega_{g(c)}$ | `Step` 在层 $g(c)$ 的目标上写 $\omega\cdot(\Omega_{g(c)} ⨾ \ldots)$ (`Step` 的字面); 节点在第 0 层上升, 链从状态的读数起 (`RKi`, `Chn` 的字面) | 树逼的 |
| `HasPfx`, `pfxRun` | `Run (x ⨾ y)` 先走 $x$, 状态与上下文不变 | 树逼的 |
| 第 $0$ 格的显式项 (`r₀`, `q₀`, `Y₂`, `WR`, `Em`, `Nm`) | `κc 0`, `κΔ`, `Walk`, `WRp` 的字面; 路径 `C.lim (suc (m + 0)) (C.suc C.self)` 要写出来, 否则坐标 $1$ 的节点读数 (具体世界上 `cmpF` 可算, 化成 `nl`) 与带元变量的项对不上 | 脚手架 (工程, 定义性化简的需要) |
| `strict` 用坐标 $1$ (或 $f(m+1)$) 的节点非零 | `HtFeedGrow.G.L2` | 树逼的 (已有) |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 不改折叠, 没有 `Lab`, 没有记号. 闭包定理不按站定制: `changeW` 对一切不含 Ω-极限的层、一切实例、一切世界; `growΩ₀`, `growΩf` 对一切合法的 $g$. 这一站新用到的字段: `nκ` 回灌第 $0$ 格的世界 $V_0=\mathrm{sum}\,1\,(z\,Y_1)$ 与它的第一位置 `C.lim 0 (C.suc C.self)` (`κc`, `sum-fst` 的字面), `Walk` 的 `suc` 与 `lim` 两句, `sL` 节点 (坐标层 $g(c)$) 在第 0 层目标上上升 (`rk0`). 否定 `no-κE` 划出本关系不能有的: Ω-极限层的 $\Omega_L$.

## 5 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `MonoPort8Sim` | 266 | 两世界互模拟, 七条折叠引理, `changeW`, `no-κE` |
| `MonoPort8Om` | 139 | 闭项展开, 坐标 $0$, `growΩ₀`, `growΩᴴ₀` |
| `MonoPort8Fin` | 140 | 前缀, 第 $0$ 格的状态, `growΩf`, `growΩᴴf` |
| 入口 | 5 | |
| 合计 | 550 | 全部手写, 没有生成文件 |

审计 (2026-11-05):

- 编译: 删掉本组 4 个 `.agdai` 后从入口重编, 退出码 0, 约 8 秒, 峰值常驻约 1.3G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0. 终止全由编译器的结构检查给出 (`Run-E` 一族与折叠同一个度量, `IntE`/`irrE` 对 `AccY` 与推导, `gWR`/`iWR`/`pfxY` 对 ℕ).
- 导入闭包 (`importclosure.py`, `--only` 同 `MonoPort7`: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 入口闭包 60 个模块 (本地 50, 库 10), `MonoPort8Sim` 24 (本地 14), `MonoPort8Om` 46, `MonoPort8Fin` 59; 禁用表 0, `--only` 之外 0. 闭包里的 `DValCanon` 与 `MonoPort6`/`7` 一样经 `MonoPort3Gen → MonoPortBridge` 带进来 (只导入不使用).
- 定义级切片 (`depslice.py`): `growΩᴴN` 到达 570 块, `growΩᴴf` 564, `growΩf` 556, `growΩᴴ₀` 516, `growΩ₀` 509, `changeW` 177, `no-κE` 28, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- 没有生成文件 (所以 `probes/Survey/scripts/monoport8/` 没有建).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort8 where

open import OCF.Align.MonoPort8Sim using (changeW; TΛ-at; no-κE) public
open import OCF.Align.MonoPort8Om using (module Om; growΩᴴ₀) public
open import OCF.Align.MonoPort8Fin using (module Fn; growΩᴴf; growΩᴴN) public
```
