# 跨高度比较闭项: 换实例

> 主线 (高度树 `HtFeed`) 第一个障碍的第 1 条. 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 定义不读记号, 没有验收文件. 正面结果的前提是函数外延性 `Funext` (定理的参数, 不是公设).
>
> - **换实例做到了, 在值上** (目标 1): 两个折叠实例 (最高层 $\Lambda_1, \Lambda_2$ 与合法性证明 $l_1, l_2$ 都可以不同), 输入在一个**不看路径**的关系下相关, 层与目标到各自最高层的路径各取, 则输出在一切两边共有的目标上相关 (`Run-R`), 第 0 层的输出相等 (`inst0`). 推论: 闭项 `TΛ Λ l` 等于在任何实例 $\Lambda'$ ($\Lambda\lhd_{[1]}\Lambda'$) 里折叠 $\Omega_\Lambda$ 的读数 (`change`), 与合法性证明无关 (`lg-irr`).
> - **路径的选择是真的** (目标 3, 否定): 只换合法性证明, 输出作为树就不相等 (`path-real`), 但在不看路径的关系下相关 (`path-rel`). 所以 "差一个路径选择" 不能去掉, 只能不看.
> - **单调没有做到** (目标 2): `TΛ Λ ≤ TΛ (hs Λ)` 与 `TΛ (f n) ≤ TΛ (hl f)` **归结为一个实例之内的单调** (`hs-reduce`, `hl-reduce`, 条件定理): 大的闭项的计算里确实折叠了一次 $\Omega_\Lambda$ (`hs-unfold`, `hl-unfold`, 无条件), 但状态、上下文、输入世界都比 `TΛ Λ` 的大, 要的是折叠对它们单调. 这是第 4 层 (`CvLayer`) 的问题, 未走通. 归结给的是**严格**增长 (`hs-reduce<`, `hl-reduce<`: `asuc (TΛ Λ) ≤ TΛ (hs Λ)`, `asuc (TΛ (f n)) ≤ TΛ (hl f)`), 因为链里下一格非零 (`hs-strict`, `hl-strict`, 无条件). $\Lambda=0$ 时前提成立 (`hz≤1`, `hz<1`).

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 不看路径的关系 | `RelA a x y`: 形状相同; `ni R v ∼ ni R′ v′` 只要端点层相同, 分支在相关参数上相关 (逻辑关系, 对层的可达性递归); `Rl L = RelA accᴸ` | [HtCrossSim](HtCrossSim.lagda.md) |
| 与可达性证明无关 | `irr` (两个证明交替递归) | 同上 |
| 第 0 层 | `eq0`: 相关推出相等, 前提 `Funext` (第 0 层没有节点, 也没有 `nκ`) | 同上 |
| 嵌入保关系 | `Int-R`, `IW-R`, `Cut-R`, `Pre-R` | 同上 |
| 判定一致 | `rkT-rel`: 两个实例对同一对 (节点层, 目标) 判定相同, 路径与最高层任取; 由 `Valid` (上升 ⇒ 没有严格第一位置) 与 `irrS` (层的严格第一位置非自反) | [HtCrossRun](HtCrossRun.lagda.md) |
| 目标的关系 | `DfR`: 同目标层, 同世界路径与合法性, **目标到最高层的路径两边各取** | 同上 |
| 状态 | `StR`: 差相关, 第 0 层的和**相等** (回灌的世界是它) | 同上 |
| 折叠 | `Run-R` … `κd-R`: 与 `HtFeedFold` 的十六个函数逐个对应 | 同上 |
| 换实例 | `inst0`, `change`, `TΛ-in`, `lg-irr`, `hs-in`, `hl-in`, `hΩ-in` | [HtCrossInst](HtCrossInst.lagda.md) |
| 归结 | `hs-unfold`, `hs-strict`, `hs-reduce`, `hs-reduce<`, `MonoStep`; `hl-unfold`, `hl-strict`, `hl-reduce`, `hl-reduce<`, `MonoL`; `mono-hz`, `hz≤1`, `hz<1` | 同上 |
| 否定 | `path-real`, `path-rel`, `no-in-2` | [HtCrossNeg](HtCrossNeg.lagda.md) |

**为什么要 `Funext`.** 回灌 `κc` 的世界是第 0 层输出的和, `v = sum W (z Y)`, 下游的类型 (`St v`, `D ly v`) 依赖它. 两个实例的第 0 层输出是含 $\mathbb N$-分支的树, 逐点相等推不出相等 (没有外延性). 所以状态的第 0 层部分要求相等, 每次更新用一次 `eq0`. 别处 (分支、更高的层) 只用关系, 不用 `Funext`. 判定一致 (`rkT-rel`), 展开 (`hs-unfold`, `hl-unfold`), 否定 (`path-real`, `no-in-2`) 都不用.

**为什么不是树的相等.** 保留节点的路径是 `cmpH` 给的, `cmpH` 在 $\Omega$-分支处用 `LgH` 的单调 (`mo`) 搬路径, 不同的合法性证明给出不同的路径 (`path-real`: `sl 0` 对 `sl 1`). 一般的换实例还要换最高层, 层与目标的路径都变; 所以关系只认端点层, 不认路径. 不认路径还能保持折叠, 是因为折叠对路径只做两件事: 比较 (判定只依赖端点, `rkT-rel`) 与转换分支类型 (`outS`, `inS`, 往返是恒等, `outS-inS`).

**与壁垒.** 被比较的两个实例要有字面的公共结构: 输入是同一层的树, 目标在两边都是最高层的第一位置 (`DfR` 只在共有的目标上). `change` 要 $\Lambda\lhd_{[1]}\Lambda'$, 世界 $1$ 是闭项的世界; 对 $\Omega$-极限的高度只够到坐标 $c\le1$ 的分支 (`hΩ-in` 的前提, `no-in-2`). 没有用到任何全局比较.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `irr`, `toRl`, `ofRl` | HtCrossSim | 关系不依赖可达性证明 | 定理 |
| `eq0` | HtCrossSim | 第 0 层相关 ⇒ 相等 | 条件定理 (`Funext`) |
| `Ωd-R`, `drp-R`, `outS-inS`, `conv`, `irrS` | HtCrossSim | 小件 | 定理 |
| `Int-R`, `IW-R`, `Cut-R`, `Pre-R` | HtCrossSim | 嵌入与切段保关系 | 定理 |
| `rk-valid`, **`rkT-rel`** | HtCrossRun | 两个实例的判定一致, 路径、最高层、合法性证明任取 | 定理 |
| **`Run-R`** 与十五个同伴 | HtCrossRun | 两个实例的折叠在共有目标上相关 | 条件定理 (`Funext`) |
| **`inst0`** | HtCrossInst | 任一层的输入, 两个实例, 第 0 层输出相等 | 条件定理 (`Funext`) |
| **`change`**, `hs-in`, `hl-in`, `hΩ-in` | HtCrossInst | `TΛ Λ l ≡ TΛ-in Λ′ l′ Λ e`, 一切 $e:\Lambda\lhd_{[1]}\Lambda'$ | 条件定理 (`Funext`) |
| **`lg-irr`** | HtCrossInst | `TΛ Λ l ≡ TΛ Λ l′` | 条件定理 (`Funext`) |
| `TΛ-in-self` | HtCrossInst | `e = hself` 时就是 `TΛ` | 定理 (`refl`) |
| **`hs-unfold`**, **`hl-unfold`** | HtCrossInst | `TΛ (hs Λ)`, `TΛ (hl f)` 不低于它们计算里的一次 $\Omega_\Lambda$ ($\Omega_{f(n)}$) 折叠 | 定理, 无前提 |
| `hs-reduce`, `hl-reduce` | HtCrossInst | `MonoStep` ⇒ `TΛ Λ ≤ TΛ (hs Λ)`; `MonoL n` ⇒ `TΛ (f n) ≤ TΛ (hl f)` | 条件定理 (`Funext` + 未证的单调) |
| **`hs-strict`**, **`hl-strict`** | HtCrossInst | 上两条的严格版: `asuc (sum b₀ X) ≤ TΛ (hs Λ)` 等 | 定理, 无前提 |
| **`hs-reduce<`**, **`hl-reduce<`** | HtCrossInst | `MonoStep` ⇒ `asuc (TΛ Λ) ≤ TΛ (hs Λ)`; `MonoL n` ⇒ `asuc (TΛ (f n)) ≤ TΛ (hl f)` | 条件定理 (`Funext` + 未证的单调) |
| `mono-hz`, `hz≤1`, `hz<1` | HtCrossInst | $\Lambda=0$: `MonoStep` 成立; `TΛ 0 < TΛ 1` | 定理; 条件定理 (`Funext`) |
| **`path-real`** | HtCrossNeg | 只换合法性证明, 输出树不相等 (`idx₀`, `idx₁`: 0 对 1) | 否定, 定理 |
| `path-rel` | HtCrossNeg | 同一对输出相关 (正对照) | 条件定理 (`Funext`) |
| `no-in-2` | HtCrossNeg | 层 2 不是 $\Omega$ 在世界 1 里的第一位置 | 否定, 定理 |

**`path-real` 的前提可满足.** $g(0)=0$, $g(c)=\lim_n0$ ($c>0$); 两个合法性证明 `lgi 0`, `lgi 1` 都是 `LgH (hΩ g)` 的元素 (只差 $0\lhd\lim_n0$ 走第几支). 输入是世界 1 里坐标 0 分支上一个层 0 的节点, 目标是坐标 1 分支的 $\lim_n0$. 否定的只是 "换实例 (哪怕只换合法性证明) 给出相等的树"; 不否定值的相等 (那是 `lg-irr`).

**`MonoStep` 说什么.** 实例 $\Lambda$ 之内: 折叠 $\Omega_\Lambda$, 一边是 `TΛ` 的设置 (输入世界 0, 空上下文, 空状态, 底 1), 一边是 `TΛ (hs Λ)` 的链第 0 项里的设置 (输入世界 1, 上下文多一个 $0$, 状态多一次 `Step`, 底 $1+\omega$), 后者不低. 它是 "折叠对状态与世界单调" 的一个实例, 与 `HtFeedGrow` 所说 "要比闭包点就要折叠对世界单调" 是同一件事. `MonoL n` 同形 (状态是第 $n$ 段的状态). $\Lambda=0$ 时 $\Omega_0=1$, 两边都只走一步 `Step`, 直接成立.

## 第一个障碍

1. **单调 (状态、上下文、输入世界).** `hs-reduce` 把跨高度的单调归结为实例之内的 `MonoStep`. 证它要比较同一实例里两次折叠的值, 输入相同, 状态一大一小: 状态里的差树在上升时被重新折叠 (`Chn`), 所以要的是 "折叠对高层输入树的值单调", 即 `CvLayer` §2 停下的地方 (第 1 层树之间比折叠的值). 回灌的世界 $v$ 也随状态变大, 走的区间变长, 还要对世界单调 (`CvLayer` §3). 未走通, 没有否定定理.
2. **$\Omega$-极限.** `change` 只到世界 1 里的分支 (`no-in-2`). `TΛ (hΩ g)` 的计算里, 回灌走过 $[1,v_0)$ 的每个坐标 $c$, 在世界 $c$ 里折叠 $\Omega_{g(c)}$; 用 `Run-R` 在世界 $c$ 里换实例是现成的 (它对一切世界成立), 但比较对象是 "世界 $c$ 的闭项", 不是 `TΛ (g c)`, 中间又是对世界单调. 没有写.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 关系 `RelA` 不认保留节点的路径 | 折叠输出带 `cmpH` 选的路径, 不同实例选得不同 | **树逼的** (`path-real`) |
| 关系对分支是逻辑关系 (相关参数 ⇒ 相关输出) | 折叠把输出节点的分支参数再折叠 (`BNi` 里 `Run ac′ z`), 上下文也流进输入的分支 (`Ai` 里 `u (inS r z)`) | **树逼的** (折叠的形状) |
| 低一层的关系对可达性递归, `irr` | 分支参数在低一层; 两边的可达性证明不同 (`f₁ r₁`, `f₂ r₂`) | 树逼的 (`accL` 的形状) |
| 状态的第 0 层部分要相等, `Funext` | 回灌的世界是它的和, 类型依赖它 | **树逼的** (`κc`) |
| 目标只在共有的第一位置上比 (`DfR`) | 壁垒: 比较要字面的公共上界 | 树逼的 |
| 判定一致 `rkT-rel` | 上升 ⇒ 没有严格第一位置; 非自反 | 树侧, 一条定理对一切层 |
| `MonoStep`, `MonoL` 的形状 | 由 `Ωd (hs Λ)`, `Ωd (hl f)` 的计算展开读出 | 树侧; 是对结构参数 ($\Lambda$; $f, n$) 的一步陈述 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有新节点字段, 没有改折叠; 没有 `Lab`, 没有记号. 一步定理: `Run-R` 对一切 $(\Lambda_1,l_1,\Lambda_2,l_2)$ 与一切层; `hs-unfold` 对一切 $\Lambda$ (新用到的字段是 `hs` 的节点 `ss`), `hl-unfold` 对一切 $(f, n)$ (新用到 `hl` 的节点 `sl n`). 否定定理划出不能有的: 换实例不能是树的相等 (`path-real`); $\Omega$-极限只能在含坐标的世界里换 (`no-in-2`). 没有序数值验收 (没有参照树).

## 账

文件级 (agda 代码块里非空非注释的行):

| 文件 | 行 | 内容 |
|---|---|---|
| `HtCrossSim` | 131 | 关系, `irr`, `eq0`, 小件, 嵌入与切段保关系 |
| `HtCrossRun` | 283 | 判定一致, 两个实例的折叠 (十六个函数, 签名约占一半) |
| `HtCrossInst` | 148 | 换实例, 合法性无关, 归结与严格 |
| `HtCrossNeg` | 73 | `path-real` 与正对照, `no-in-2` |
| 入口 | 6 | |
| 合计 | 641 | |

脚手架分账 (判断): 关系与 `irr` (约 40 行) 是 "不看路径" 所需, 由 `path-real` 逼出; `Run-R` 一族逐个照抄折叠, 是折叠的形状逼出的, 与高度无关, 换一个最高层不加一行; `eq0` 与状态里的 `zR` 是回灌世界依赖第 0 层输出逼出的. 没有一行按站写.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.SumVar --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.HtCross`): 入口 (30 个模块, 本地 20), `HtCrossSim`, `HtCrossRun`, `HtCrossInst`, `HtCrossNeg` 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtCrossRun:Run-R` 162/0/0, `HtCrossInst:change` 183/0/0, `HtCrossInst:lg-irr` 184/0/0, `HtCrossInst:hs-strict` 138/0/0, `HtCrossInst:hl-strict` 152/0/0, `HtCrossInst:hz<1` 207/0/0, `HtCrossNeg:path-real` 118/0/0, `HtCrossNeg:path-rel` 182/0/0, `HtCrossNeg:no-in-2` 30/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发.
- **禁用构造**: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`. `Funext` 只作定理的参数出现.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (35 秒, 峰值 1.2G).

## 时间线

写定义前读过: `HtFeed`, `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtFeedHt`, `HtFeedGrow`, `HtFeedNeg`, `HtFeedTest`, `CumReadCF` 前半, `CvLayer` 入口, `TLRuleSpec` 的序. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCross where

open import OCF.Align.HtCrossSim using (Funext; SimD; RelA; Rl; irr; eq0; Int-R; Cut-R; irrS; outS-inS) public
open import OCF.Align.HtCrossRun using (module Val; module Two) public
open import OCF.Align.HtCrossInst using (module Cross; TΛ-in; TΛ-in-self; change; lg-irr; hs-in; hl-in; hΩ-in; module Hs; module Hl; module HsS; module HlS; mono-hz; hz≤1; hz<1) public
open import OCF.Align.HtCrossNeg using (path-real; path-rel; idx₀; idx₁; no-in-2) public
```
