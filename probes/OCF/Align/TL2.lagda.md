# 树的语言, 第二对: 补四条正面判据 (构造一路, 入口与判决)

> 不含记号. 作者选定原话: "补四条正面判据"; 选项说明 (作者确认): "给 TreeLangIf 只增四条正面判据 (顺序一致, 异键对, 升界保序, 读数类型随成员变), 重试形状定理, 配对否定; 看平的候选是否被排除, 并记哪条读自 step". 本路前缀 `TL2` (构造), 与否定一路 `NegTL2` 配对, 共用接口 [TL2If](TL2If.lagda.md) ("接口定稿 2026-11-05 21:12 (首次编译通过)", 变更记录: 无). `TreeLangIf` 与上一对的文件都未改, 只导入. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **判决: PARTIAL.** 四条判据各自排除了上一对否定一路指出的候选 (定理), 并给出三条新的形状定理; 但没有推出与现有形状不同的定义: 判据推出的形状都落在现有积木 (`step`, `sup`, `Lev`, `Pos`) 上 (定理, `refl` 级). 没有新闭项, 没有值的定理.
>
> 1. **平的候选被排除.** (i) `OrdCrit` (第一位置就是坐标高度在投影世界里的 `⊲`): `Lev`, `Lv` 满足 (`LevO`, `LvO`); `Fl`, `FlL` 不满足 (`no-ord-Fl`, `no-ord-FlL`). 更一般地, 满足 (i) 的候选里一个种类的第一位置反对称 (`ord-antisym`), 所以 `Fl` 的退化机制 (两个坐标互为第一位置) 整个被排除.
> 2. **(i) 推出界下坐标可判定 (`ord-dec`).** 满足 (i) 的任一候选, 任一层, 任一级种类: 同一合法世界的界之下两个坐标相等可判定. 这是 "种类的坐标可以作升界的键" 的条件, 把 (i) 与 (ii) 接起来. 另有 `ord-mono` (合法分支对坐标单调).
> 3. **(ii) 撑开定义域.** `Cross` 要求共界的成员对都在定义域里: `supD` (对角定义域, 否定一路的 `diag-raise`) 与空定义域都被排除 (`no-cross-diag`, `no-cross-empty`); 形状定理 `cross-shape`, `cross-unique`: 合法升界在一切与被升成员共界的成员上唯一, 就是按 `bdec` 的点更新. 上一对的 `shape` 只在定义域里成立, 而定义域可以是空的 (`shrink`); 现在不行了.
> 4. **(iii) 与 `any-lowers`.** 条件形的增长律 `Grow` (与 `RsK.rs≤` 同形) **不排除** `any-lowers` (`lowers-anyway`: 同一个 `posInst` 满足 `Grow` 且降值); 无条件增长在 `F₀` 上无实例 (`grow-all→⊥`); `RaiseUp` (只对在旧读数之上的值升界) 排除降值 (`no-lower`, `lower-blocked`). 所以 "升界" 与 "置值" 的区别在 `RaiseUp` 的类型里, 不在 `Grow` 这条律里.
> 5. **(iv) 与 C6.** 读数类型随成员变 (`DRaise`, 值是成员上的截面) 解除 `raise-adj`: `DPos` 是 κHc 型的有界族 (成员 = 合法界之下的位置 $a$, 读数类型 `HB (Lev a)`), 有合法升界 `dR`, 满足 (ii) (`dCross`) 与 (iii) (`dGrow`, 世界序就是逐位置的 `step` 的 `≤⁺`); 在界 `hs hz` 之下, `raise-adj` 互相冲突的两级 (`tyL`, `tyH`) 同在, 读数各取任意值 (`Adj.adj-free`). **盲区**: 拷贝不相干 (`Copies.copies-split`); 截面取成键的函数时相干 (`keyed`); 只给单个键处的值要搬运 (判断, 未证未否定, 与 `uip→raiseA1` 同处).
> 6. **界框架 (对否定一路 `LevP` 的回应).** (i) 不排除 "世界只取一部分高度作界" 的候选 (否定一路 `NegTL2Pre.LevP`, 其定理以否定一路为准). 把 (iii) 用在 "读界的单成员框架" 上: `RaiseUp` 推出每个在当前界之上的坐标都能作某个更大世界的界 (`BdF.up→rich`); 一般形 `no-up-pred` (一切界满足 $Q$, 某个界之上有不满足 $Q$ 的坐标 ⇒ 无 `RaiseUp`); 实例 `levUp` (`step` 的新种类有); 反例 `frozen` (第一位置是 `⊲`, 界固定) 没有 (`no-up-frozen`).
>
> **对纲领与目标.** 纲领 1–4 不受影响: 只有种类结构与框架上的记录与定理, 不读记号; (ii) 的前提就是一对键的字面公共上界, 其余律都只对带证据的对; 无公理. 目标 "让树自足": 判据第一次**排除**了上一对的盲候选 (`Fl`, 对角定义域, 降值, 单一读数), 并推出可用的形状性质 (`ord-dec`, `cross-unique`, `up→rich`). 这是正面指引, 但指引的终点是现有积木: `DPos` 的世界逐字就是 `sup (界下位置) (step ∘ Lev)` 的世界 (`sup-rt₁`, `sup-rt₂`, `ord-same`, `bd-same`, 都是 `refl`). 所以本轮的判据是**验收现有形状的判据**, 不是写出新定义的判据; 而 (i), (iii) 本身读自 `step` 与 `RsK` (下面翻译账). C6 的进展: 跨级族的单一读数墙 (`raise-adj`) 在 (iv) 下不存在; 剩下的是拷贝相干与 "把 `DPos` 接到折叠真正用的世界上" (`K₁` 的世界是裸坐标积, 见 `TreeLangRaise.sup-bare→Sep`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TL2 where

import OCF.Align.TL2If
import OCF.Align.TL2Ord
import OCF.Align.TL2Raise
```

## §1 接口 (摘要)

见 [TL2If](TL2If.lagda.md) 文件头的表. (i) `OrdCrit`/`OrdCritL`; (ii) `HKey`, `CrossOn`, `Cross`; (iii) `OrdFrame`, `Above`, `Grow`, `RaiseUp`; (iv) `DFrame`, `DRaise`, `constD`, `DOrd`, `DAbove`, `DGrow`, `DCross`.

## §2 定理表

| 定理 | 陈述 (简) | 文件 | 档 |
|---|---|---|---|
| `LevO`, `LvO` | `Lev` 满足 (i), `Lv` 满足 (i) 的 `LH` 版 | TL2Ord | 定理 (实例) |
| `no-ord-Fl`, `no-ord-FlL` | 平的候选不满足 (i) | TL2Ord | 定理 (排除) |
| `ord-dec`, `ord-decL`, `ex-dec` | (i) ⇒ 同一合法世界的界下两个坐标相等可判定; 前提实例 | TL2Ord | 定理 (形状) |
| `ord-antisym` | (i) ⇒ 第一位置反对称 | TL2Ord | 定理 (形状) |
| `ord-mono` | (i) ⇒ 合法 Ω-分支对坐标高度单调 | TL2Ord | 定理 (形状) |
| `no-cross-diag`, `no-cross-empty`, `pos-cross` | `supD` 与空定义域不满足 (ii); `Pos` 满足 | TL2Raise | 定理 |
| `keydec`, `cross-shape`, `cross-unique` | (ii) ⇒ 共界成员上升界唯一, 是按 `bdec` 的点更新 | TL2Raise | 定理 (形状) |
| `posGrow`, `grow₀`, `lowers-anyway` | `posInst` 满足 `Grow`, 且降值 | TL2Raise | 定理 (盲) |
| `grow-all→⊥` | 无条件增长在 `F₀` 上无合法升界 | TL2Raise | 定理 |
| `up-of`, `no-lower`, `lower-blocked`, `posUp` | `Raise`+`Grow` ⇒ `RaiseUp`; `RaiseUp` 读数不降; `any-lowers` 的一步无居留 | TL2Raise | 定理 |
| `DPos.dR`, `dCross`, `dO`, `dGrow`, `keyed` | κHc 型有界族: 合法升界, 满足 (ii), (iii); 键函数截面相干 | TL2Raise | 定理 (实例) |
| `supW`, `sup-rt₁`, `sup-rt₂`, `ord-same`, `bd-same` | `DPos` 的世界与序就是 `sup PJ (step ∘ Lev ∘ proj₁)` 的 | TL2Raise | 定理 (`refl`) |
| `Adj.adj-free`, `tyL`, `tyH` | `raise-adj` 的两级同在, 读数各取任意值 | TL2Raise | 定理 |
| `Copies.copies-split` | 截面形升界不要求拷贝相干 | TL2Raise | 定理 (盲) |
| `D→Raise` | `constD` 上的 `DRaise` 给出 `Raise` | TL2Raise | 定理 |
| `BdF.up→rich`, `BdF.no-up-pred` | 界框架上 `RaiseUp` ⇒ 当前界之上的坐标都能作界; 界受谓词限制则无 `RaiseUp` | TL2Raise | 定理 |
| `levUp`, `levRich` | `step` 的新种类有界框架 `RaiseUp` | TL2Raise | 定理 (实例) |
| `frozen`, `frozen-ord`, `no-up-frozen`, `frozen-top` | 第一位置为 `⊲`、界固定的种类: 无界框架 `RaiseUp`; 前提可满足 | TL2Raise | 定理 |

## §3 重试形状定理: 判据推出了什么

| 问题 | 结果 | 依据 |
|---|---|---|
| 平的候选 `Fl` 是否被排除 | 是, 由 (i) | `no-ord-Fl`, `no-ord-FlL` |
| 满足全部判据的定义是否落在更窄的形状里 | 是, 在三处: 种类的第一位置是坐标高度的 `⊲` 且反对称, 界下坐标可判定 ((i)); 合法升界在共界成员上唯一 ((ii)); 界能取遍当前界之上的坐标 ((iii) 用在界框架上). 不是唯一: 级集合之外的重数 (否定一路的 `LevD`), 种类结构的其余字段都不定 | `ord-dec`, `ord-antisym`, `cross-unique`, `up→rich` |
| `any-lowers` 是否被 (iii) 排除 | 条件形 `Grow` 不排除; `RaiseUp` 排除 | `lowers-anyway`, `lower-blocked` |
| `raise-adj` 在 (iv) 下是否解除 | 是 | `Adj.adj-free` |
| κHc 一类跨级族上是否有合法升界 | 在合法界之下的位置族上有, 满足 (ii), (iii); 拷贝不相干, 单值形未定 | `DPos.dR`, `dGrow`, `copies-split` |
| 推出的定义是否与现有形状不同 | 否: `DPos` 的世界逐字是 `sup PJ (step ∘ Lev ∘ proj₁)` 的世界; 与 `ColimAIf.LevA` 的 Ω 行 (`sup` 取界下坐标) 同形, 与 `ColimAIf.GWA` (一个共享世界, 低层世界由 `restrA` 算出) 不同 (判断: 本篇的世界逐位置独立, 没有共享) | `sup-rt₁`, `ord-same`, `bd-same` |

## §4 翻译账

| 判据或结果 | 来自哪里 | 类 |
|---|---|---|
| (i) `OrdCrit` 的 `ord→`/`ord←` | **读自 `HtTowerTy.step`** 的新种类那一行 (`Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′`) | 树侧现有形状, 非记号. 作为要求是选择; 必要性有定理支持 (不要它, `Fl` 合法: `NegTreeLangFlat`; 要它, `Fl` 被排除: `no-ord-Fl`) |
| (i) `prj` | 读自 `step` (世界第一分量) 与 `sup` (逐分量) | 同上; 写 `ord→` 需要一个低层世界, 所以 `prj` 是 (i) 的形式要求 (判断) |
| `ord-dec`, `ord-antisym`, `ord-mono` | 由 (i) 加 `cmpK`, `toLt`, `antisym` 推出 | 定理 |
| (ii) `Cross` | `StallDxBdec.bdec` 说共界的对在定义域里不推出分离子; "必须含" | 树逼出的是 "可以含" (定理); "必须含" 是选择 |
| (iii) `Grow` | 读自 `RsOwnIf.RsK.rs≤` (条件形) | 树侧接口, 选择 |
| (iii) `RaiseUp` | `RsK` 的 `rs≤` 只对 `top` 之上的值; 本篇把条件挪进类型 | 选择; 效果有定理 (`lower-blocked`) |
| (iii) `dO` 的世界序 | 就是 `step` 的 `≤⁺` 逐位置 | 读自 `step` |
| (iv) 读数类型随成员变 | C6 的跨级族逼出 (`raise-adj`: 单一读数装不下相邻两级, 定理) | 树逼出 |
| (iv) 值是截面 | 读自 `ColimARaise.raiseA′` 的族增量 (不搬运) | 树侧已有出路, 选择 |
| 界框架 (`BdF`) 的读数类型取坐标类型 | 与 (i) 同源 | 选择 (取 $\Sigma$ (HB S) P 时 `LevP` 也有 `RaiseUp`) |

本路没有新构造子, 没有新结点, 没有读自记号或基本列规则的字段. `frozen` 是为说明界框架的分辨力造的对照, 不进成品. 加深翻译的标志一条都没有出现; 但 (i), (iii) 读自 `step` 与 `RsK`, 所以判据在验收现有树形, 不是从别处逼出它 (判断).

## §5 接手清单

1. **把 `DPos` 接到折叠用的世界上.** `DPos` 是抽象框架; `K₁` 的世界是裸坐标积 (`sup-bare→Sep`). 下一步: 写一个种类结构, 它的 Ω-行取 `sup (界下位置) (step ∘ Lev)` (就是 `LevA` 的 Ω-行), 证明它满足 (i), 它的新种类满足界框架 `RaiseUp`, 且整层满足 `DCross`, `DGrow`; 对照 `ColimAKS.LevC′` 的共享世界.
2. **拷贝相干.** 截面形不要求相干 (`copies-split`); 键函数形相干 (`keyed`). 需要一条判据说 "升界的值是键的函数" (类型 `(a : Key) → Vk a`, 读数 `Vᴰ j = Vk (key j)`), 那时 `DRaise` 的一个特例就够, 不搬运. 接口可只增一个 `KRaise` 记录.
3. **单值形.** 只给一个键处的值时扩成键函数要判定键相等并搬运; 有界键上 `bdec` 给判定, 搬运是否需要 UIP 未定 (与 `uip→raiseA1`, `LocUipNegLoop` 同处).
4. **重数.** 否定一路说 `LevD` (后继加两个新种类) 满足 (i) 与 Rich; 重数需要另一条判据 (上一对 §2 自由度 2), 本轮未处理.
5. **值.** 本轮全是形状; 没有序数值的定理 (交付只有 (a) 中的实例, 没有 (b)).
