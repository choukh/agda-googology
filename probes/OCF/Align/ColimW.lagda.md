# `Lev` 取并 (colim): 构造一路 (入口)

> 不含记号. 作者选定原话: "Lev 改成并 (colim)". 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.4, §3.3, §4 第 4 条 (iii). 接口 [ColimWIf](ColimWIf.lagda.md) (与否定一路 `ColimWNeg*` 共用). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **判决: 部分成立.** 前两步是定理, 第三步对有限层号是定理, 对无限层号未走通 (条件定理写出了要什么).
>
> 1. **`LevC x` 是种类结构, 对一切 `S`, 一切高度 $x$** (定理, [ColimWKS](ColimWKS.lagda.md)). 世界换成每个字面层号一个界 `GW S = A × Π_y HB (Lev y)`, `Lev x` 的世界由 `restr x` 算出; `LevC x` 是沿 `restr x` 的拉回 `pb`, `cmpK` 与 `botBd` 由拉回直接给出. 认同律 `glob` (每条只含一个种类): 一切种类的界只由它的层号与世界在那一层的分量决定. 于是最小实例里层号 `finH 1` 的三个拷贝 (`κ₂`, `κ₂′`, `κ₂ω`), 底种类的三个拷贝, ℕ-极限级 `xω` 的两个拷贝, 以及跨两级的拷贝, 界都是**同一个命题** (`refl`). 对照: 原来的和里 `κ₂` 与 `κ₂′` 的界互不推出 (`sum-no-cross→`, `sum-no-cross←`).
> 2. **`copy→⊥` 在 `LevC x₀` 里不成立的前提是逐分量合法 `LocalLg`** (定理, [ColimWCopy](ColimWCopy.lagda.md)). 形状 `CopyShape (LevC x₀)` 成立 (`shapeA`: 底种类, 两个 "证据" 是同一个 `A` 分量的两个第一位置, `toH` 节点合法), 所以由 `copy→⊥` 得 `¬localA`. 与 `AdmWNegCopy` 的三个模型比: 同 `M2` 缺的是 `LocalLg`; 区别是 `M2` 有两个分量而合法性要求它们可比, `LevC` 只有一个分量. `LevC` 的界里没有证据的存在量词 (`Bd` 是一个命题, 不是 `SupB` 的 $\Sigma$), 所以 `AdmWCoh` 的跨证据相干 `Coh≡` 与它要的 UIP 在这里不出现.
> 3. **不违反 `no-retract`** (定理 `no-retractC` + 定义形状的说明, ColimWKS §5): `LevC x` 的坐标与世界只含 `A` 与 `HB (Lev y)` ($y$ : `HB S`), 不含 `HB (LevC x)`.
> 4. **更新与一步回灌** ([ColimWRaise](ColimWRaise.lagda.md)). 有判定证书 `DecAt y₀` 就有满足接口全部律的 `RaiseG y₀` (`raiseG`, 定理, 不用 UIP); 有限层号有证书 (`decFin`). 从最小世界在层号 `finH 1` 上接 `Ωtop S₀`: 合法 (`lgW₁`), 世界变大 (`grow₁`), **`κ₂` 处含新种类节点的格有界** (`cell₂`, `root-new`), 同一证明项在 `κ₂′`, `κ₂ω`, `λ₂`, `λ₃` 处都成立; 一般形 `cell-gen`. 对照 `ChainZNeg.no-chain` (它杀的是 `growL′` 生成的一族世界; 这里的更新是选择性的, 不在那一族里, 不矛盾). 对照和的世界: 只改一个分量时, 拷贝 `κ₂′` 不跟着变 (`sum-stale`).
>
> **第一个障碍: 无限层号上的更新.** `RaiseG y₀` 的 `off` 律对裸层号陈述. `raiseG→wdec` (条件定理, 与 `CohWUpd.upd→wdec` 同族): 有 `RaiseG y₀` 就能对一切 $y$ 判定 "$y_0\ne y$ 或者非非 $y_0 = y$". 有限层号有真判定, 没问题; 第一个无限层号 (`x₀` 里坐标 `hs ω₀` 处新种类的层号 `up ω₀`; ℕ-极限级 `xω` 本身写成 `hl finH`) 要对一切 $y$ 弱判定 $y_0 = y$, 判断: `--safe --without-K` 里写不出 (纸面: 连续性). 可入版 `RaiseA` (律里层号都带 `hs y ⊲[ w ] x`) 只有类型. 判断: 它在 `GW` 上也写不出, 因为 `GW` 是裸层号上的函数, 更新要对**不可入**的 $y$ 也给出值, 而 "是不是 $y_0$" 对它们没有证据可用 (纸面: 若外层界里有与 $\omega$ 前 $N$ 项相同、之后不同的层号树, 任何连续的选择都把其中一个当成 $\omega$); 把分量改成以 (层号, 证据) 为下标又回到 `AdmWCoh` 的墙 (分量类型 `HB (Lev y)` 随层号变, 同一层号的两个证据给两条相等证明, 搬出的增量要 UIP). 这三处的形式化是否定一路的事; 这里没有写成定理.
>
> **另一处 (判断, 无定理).** 认同按字面层号: 逐点相等而字面不同的层号树 (`up ω₀ = hl (λ n → up (finH n))` 与 `hl finH`, 类型都是 `HB S₁`) 读 `GW` 的两个分量. 它们读同一个分量要函数外延; 它们读不同分量也证不出 (同样要函数外延的否定). 折叠会不会产生两种写法, 没有查.
>
> **对纲领与目标.** 不触壁垒: 没有序, 没有全局三歧; 一切比较在同一种类的同一个界之下 (`cmpK` 由拉回给出). 拷贝墙 (`CohWNeg.no-cross`, `HtTowerNStage.no-wmatch`, `AdmWNegCopy.copy→⊥`) 在 `LevC` 里由定义消掉: 拷贝不是相干的两个分量, 而是同一个分量. 代价全部移到更新上的层号判定: 这把 "按相等认同拷贝 ⇒ W" (诊断 §2.4) 写成了一个具体的位置, 有限层号过, 无限层号是第一个障碍.
>
> **交付拆成两条.** (a) 合法的构造: `LevC` (一切 $x$), `raiseG` (有证书的层号), `W₁` (一步回灌后的合法世界, `κ₂` 处含新节点的格有界). 没有新的闭项, 没有折叠. (b) 关于值的定理: **没有** (这一路不涉及序数值; `W₁` 是世界, 不是闭项).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimW where

open import OCF.Align.ColimWIf public
open import OCF.Align.ColimWKS public
open import OCF.Align.ColimWCopy public
open import OCF.Align.ColimWRaise public
```

## 接口内容

| 名字 | 内容 |
|---|---|
| `GW S`, `restr`, `LgG`, `_≤G_` | 每个字面层号一个界的世界; `Lev x` 的世界由它算出; 整体合法与世界序 |
| `LevCParts x` | `LevC x` 的种类, 坐标, 界, 第一位置, 合法, 世界序 (都沿 `restr x`); `CmpKC`, `BotBdC` 的类型 |
| `Lvl`, `LE`, `lvl`, `cE`, `BdL`, `PrL`, `Glob`, `GlobPr` | 层号映射与认同律 (每条只含一个种类) |
| `DecAt`, `RaiseG y₀` | 判定证书; 裸层号上的更新 (六条律) |
| `AdmL`, `RaiseA x w` | 可入层号上的更新 (律里层号都带公共上界 $x$ 的证据), 只有类型 |
| `S₁`, `finH`, `x₀`, `xω`, `ω₀`, `κ₂`, `κ₂′`, `κ₂ω`, `κA`, `κA′`, `κAω`, `λ₂`, `λ₃`, `Cell₂` | 最小实例 |

接口自定稿后未改 (变更记录为空).

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `pb`, `LevC` | ColimWKS | 拉回是 `KS`; `LevC x` 对一切 `S`, $x$ | 定义 (字段即证明) |
| `cmpKC`, `botBdC` | ColimWKS | 接口 `CmpKC`, `BotBdC` 的实例 | 定理 |
| `glob`, `globPr` | ColimWKS | 一切种类的界/第一位置只由层号与该层的分量决定 | 定理 |
| `lgG→`, `≤G→`, `≤G-rf`, `W₀`, `lgW₀` | ColimWKS | 整体合法/世界序推出每一级的; 合法世界的实例 | 定理 |
| `cross₂′`, `cross₂ω`, `crossλ`, `cross-lv`, `crossA′`, `crossAω`, `read₂`, `readA` | ColimWKS | 拷贝的界是同一个命题 | 定理 (`refl`) |
| `sum-no-cross→`, `sum-no-cross←` | ColimWKS | 和的世界里 `κ₂`, `κ₂′` 的界互不推出 | 定理 (否定, 只说和的世界的这一对种类); 前提可满足 `sat-a`, `sat-b`, `lg-wa`, `lg-wb` |
| `no-retractC` | ColimWKS | `no-retract` 对 `LevC x` | 定理 |
| `toC`, `toC-⊲`, `Lg-toC` | ColimWKS | 和的合法高度搬进拉回仍合法 | 定理 |
| `shapeA` | ColimWCopy | `CopyShape (LevC x₀)` 成立 | 定理 |
| `¬localA`, `illegal-W₂` | ColimWCopy | `LevC x₀` 上 `LocalLg` 不成立; `W₂C X₂ X′` 不合法 | 定理 (否定, 只说这一个形状) |
| `legal-same` | ColimWCopy | 公共上界合法时世界合法 | 定理 |
| `eqFin`, `eqFin-diag`, `decFin` | ColimWRaise | 有限层号的判定证书 | 定理 |
| `raiseG` | ColimWRaise | `DecAt y₀ → RaiseG y₀` | 定理 |
| `raiseG→wdec` | ColimWRaise | `RaiseG y₀ →` 对一切 $y$: `¬ (y₀ ≡ y) ⊎ ¬ ¬ (y₀ ≡ y)` | 条件定理 (前提 `RaiseG y₀`) |
| `W₁`, `lgW₁`, `grow₁` | ColimWRaise | 一步回灌后的合法、更大的世界 | 定理 |
| `cell₂`, `cell₂′`, `cell₂ω`, `cellλ₂`, `cellλ₃`, `root-new` | ColimWRaise | `κ₂` 与它的拷贝处含新节点的格有界 | 定理 |
| `cell-gen` | ColimWRaise | 一切世界与增量 | 定理 |
| `sum-fresh`, `sum-stale` | ColimWRaise | 和的世界只改一个分量: 原件有界, 拷贝不有界 | 定理 (否定只说这一种更新) |
| "`RaiseG (hl finH)` 写不出", "`RaiseA` 在 `GW` 上写不出", "以证据为下标要 UIP" | — | 见第一个障碍 | 判断 |
| "逐点相等的两棵层号树读两个分量" | — | 见判决 | 判断 |

## 前提实例

- `raiseG→wdec` 的前提 `RaiseG y₀`: `raiseG (decFin k)` (一切有限层号).
- `sum-no-cross→`, `sum-no-cross←`: 合法世界 `wa`, `wb` (`lg-wa`, `lg-wb`), 前提的另一半各自可满足 (`sat-a`, `sat-b`).
- `¬localA`: 形状 `shapeA` 是闭项; `LocalLg` 的两个参数各自合法 (`lgX₂`, `lgX′`); 合法的共用世界存在 (`legal-same`).
- `sum-stale`: 世界 `ws` 合法 (`lg-ws`), 原件有界 (`sum-fresh`).
- `cell₂` 一族: `W₁` 合法 (`lgW₁`), 比 `W₀` 大 (`grow₁`), 增量 `Ωtop S₀` 合法 (`Lg-Ωtop`).

## 要重做的已有脚手架 (判断)

`HB (LevC x)` 与 `HB (Lev x)` 是不同的类型 (同一种类与坐标, 不同的记录), 所以凡是把 `Lev` 的世界当作逐分量的积来用的地方都要改; 一切对任意 `KS` 成立的引理 (`⊲`, `LgB`, `cmpB`, `⊞`, `up`, `ι`, `step`, `bdec`) 原样可用, 和的合法高度经 `Lg-toC` 搬过来.

- `HtTowerU` (`L`, `U`, `θ`, `Λᵁ`): `L (k+1) = Lev (Ωtop (L k))` 换成 `LevC`; `U` 的 `sup ℕ` 本身也取并 (世界用 `GW` 的类比, 或 `CohWTy.colim`).
- `HtTowerNStage` (`L′`, `need′`, `wmatch′`, `dW`, `dWLev`): `⊕` 的右分量换成 `LevC`; `wmatch′` 的投影改为经 `restr`.
- `CohWTy`/`CohWL`/`CohWTower`/`CohWGl`/`CohWUpd`: `U⋆` 的 `Lev` 部分换成 `LevC` 后 `no-cross` 那一对种类相干 (`ColimWKS.cross₂′` 是同一形状); `CohWGl` 的 `GW` 与本篇同形, 可由本篇取代 (它有自己的层号块 `LH` 与 `H⁰`, 本篇直接用 `HB` 与 `Lev`).
- `DiagK*`, `ChainZ*` (`growL′`, `Reach`, `no-chain` 的世界族), `TelW*`: 世界的定义与生长算子要在 `GW` 上重写; `no-chain` 的结论只对它那一族世界成立, 换世界族后要重新问.
- `HtTowerFFold` 的 `RunM`/`κc₁` 与 `HtTowerFRead.rd` (回灌与读回): "换一个分量" 改为 `RaiseG` 在读到的种类的层号上接长; 无限层号处要先过第一个障碍.
- `AdmW*`: `SupB` (以证据为下标的分量) 对 `Lev` 部分不再需要; `bdec`, `cmpB₀` 留作可入版更新的工具.

保留: `HB`, `_⊲[_]_`, `LgB`, `cmpB`, `_⊞_`, `step`, `up`, `Ωtop`, `sup` (仍给种类), `Lev` (仍给种类与坐标), `no-self`/`no-retract`, 第 0, 1 层的主线 (`HtFeed*`, `HtOut*`, `MainView*`).

## 翻译账

本路不读记号. 新定义:

| 定义 | 来源 | 归类 |
|---|---|---|
| `GW S` (每个字面层号一个界) | 诊断 §4 第 4 条 (iii) 与作者原话 "改成并"; 由 `no-cross`, `no-wmatch`, `copy→⊥` 三条拷贝否定逼出; 与 `CohWGl.GW` 同形 | 树侧 |
| `restr` (世界算出来) | `CohWTy.colim` 的 `pj` | 树侧 |
| `pb` (拉回) | 一般构造, 无内容 | 脚手架 (序数值不需要) |
| `lvl`, `cE`, `BdL` | 认同律的陈述所需; `cE` 只为让检查器看见类型相同 | 脚手架 |
| `DecAt`, `eqFin`, `inc` | `--without-K` 下的选择性更新所需 | 脚手架 |
| `RaiseG` 的形状 ("在一个层号上接长, 别处不动") | `HtTowerFFold.RunM` 的 "读界, 升一个槽" (诊断 §4 第 4 条 (i) 记为翻译痕迹); 本路没有去掉它, 只把槽从 "分量" 换成 "层号" | 沿用的翻译痕迹 |

没有新构造子; 没有读自记号基本列规则的字段; 没有闭包定理, 没有验收, 没有标签. 这一步: **摆脱侧** (去掉 "`Lev` 在极限处取和" 这一条从下标塔直觉来的选择), 不加深翻译; 提供信息: 两条和世界上的否定 (`sum-no-cross`, `sum-stale`) 划出和的世界给不了的东西, 条件定理 `raiseG→wdec` 划出无限层号的更新要什么.

## 审计

- 编译: 从仓库根 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/ColimW.lagda.md +RTS -M6G -RTS`, 退出码 0 (五个文件).
- 导入闭包 (`importclosure.py OCF.Align.ColimW`, 另跑 `--only OCF.Align. --only OCF.BTBO`): 22 个模块 (本地 13: `AdmWNegCopy`, `ColimW*` 五个, `CumReadCF`, `HtFeedTree`, `HtTowerCont`, `HtTowerNeg`, `HtTowerTy`, `HtTowerU`, `OCF.BTBO`), 禁用表 0, 退出码 0. 接口 `ColimWIf` 的闭包 14 个模块 (本地 5), 禁用表 0.
- 定义级切片 (`depslice.py`, 同一个 `--html` 目录): `ColimWKS:LevC` 64/0/0, `ColimWKS:glob` 69/0/0, `ColimWCopy:¬localA` 100/0/0, `ColimWRaise:raiseG` 79/0/0, `ColimWRaise:W₁` 95/0/0, `ColimWRaise:cell₂` 100/0/0, `ColimWRaise:raiseG→wdec` 74/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- 禁用构造: 无 postulate, 无洞, 无 TERMINATING/NON_TERMINATING/NO_POSITIVITY, 无 trustMe, 不开 K, 无 Funext, 无 UIP 前提.
- 文件行数 (总行 / 非空代码行): `ColimWIf` 207/120, `ColimWKS` 250/159, `ColimWCopy` 67/35, `ColimWRaise` 200/122, 入口 `ColimW` 约 110/6.
