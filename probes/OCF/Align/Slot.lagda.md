# 高度坐标的共享槽小实验 (构造一路的入口与判决)

> 不含记号. 本路 (前缀 `Slot`) 是构造一路, 与否定一路 `NegSlot` 配对, 共用接口 [SlotIf](SlotIf.lagda.md) ("接口定稿 2026-11-05 20:03 (首次编译通过)", 变更记录: 无). 作者本轮选定 (原话): "高度坐标的共享槽小实验". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 没有新闭项.
>
> **判决: 两半.**
>
> - **构造 (同一级的拷贝族).** 共享槽 + 一族搬运对 "一个种类沿级的和的一切路径的拷贝" 成立: `Lev (a ⊞ b)` 里 `Lev a` 的任一种类沿 $b$ 的一切路径 (下标含函数) 的拷贝, 槽是 `Lev a` 自己, 搬运对 $b$ 递归化成恒等, 不重建树 (`SlotCp.Cp.cpSlot`). 只要槽里那个种类有 `RsK`, 一族拷贝就在带证据 "每份共享世界相同" 的世界上一起满足 `RsK` (`KLv` 的 `rs≤`, `rsLg`, `rs-top`), 不判定下标 (`SlotGen.Gen.famS`). 坐标是高度的实例: `step` 的新种类 (坐标 `HB (Lev a′)`) 的拷贝 (`SlotCp.CpNew.famNew`); 落到分层塔 `StratTwTw` 的每一站 $s$ (`SlotTw.famU`), `NegStratTwDeep.κd c` 是成员 (`SlotTw.κd-rs`). 证据在基世界上有实例 (`ev0U`).
> - **否定 (坐标类型随级变的 `κHc` 一族, 原卡点 `κH f`).** 接口形状的共享槽 (读回精确) 加上这一种一起升, 对 `κHc` (下标取遍 `H₀`) 与只对 `κH f` (下标取遍 `ℕ → H₀`) 都不存在 (`SlotKH.no-slotKH`, `no-slotJx`; 定理, 依据否定一路 `NegSlotPre.no-forgetK₁`, `no-forget-jx`): 一族里同时有相邻两级的成员, 经槽一起升会让高一级成员的新界只依赖 $v$ ("忘"), 撞 `no-inflate`. 任何对 `κHc` 一致的升界都要一个对角解码 (`SlotKH.kH-Dg`). **更正:** 否定一路后来证了更强的 `NegSlotWall.no-slot-κHc : ¬ Slot K₁ tp₁ H₀ κHc Q tq κ₀` (无别的前提; 已复核编译, 退出码 0): 共享槽逼每一对可达成员的坐标类型互为收缩 (`SL.slot-ret`), 所以 `κHc` 一族连 `Slot` 本身都没有, 与升界忘不忘无关.
>
> **对纲领与目标.** 纲领 1, 2: 本路只给升界的构造与否定, 没有闭项; 构造对种类结构的构造子递归, 不判定含函数的下标. 纲领 3: 证据是一个世界上的 "每份共享世界 $\equiv\omega$", 公共值 $\omega$ 是字面的; 律逐条只含一个成员或经同一个 $\omega$ (接口 "律的定义域"); 不要求任何下标类型上的判定. 纲领 4: 本路不读记号. 目标 "让树自足": 一条树侧判据 (判断, 有两边的定理撑着): **"一起升" 能不能经共享槽, 看一族成员是不是同一个种类的拷贝 (坐标类型化到同一个) 还是含相邻两级**. 前者是构造 (`famU`), 后者是否定 (`no-slotKH`). 原卡点 `κH f` 属于后者.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Slot where

import OCF.Align.SlotIf
import OCF.Align.SlotGen
import OCF.Align.SlotCp
import OCF.Align.SlotTw
import OCF.Align.SlotKH
```

## 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `Dg`, `Slot`, `ShW`, `RsFam`, `κHc`, `tp₁` | If | 接口: 对角解码, 共享槽, 世界证据, 一致升界族, 原卡点的一族 | 定义 |
| **`Gen.invS`**, **`Gen.rsS`**, `Gen.famS` | Gen §1 | 任一共享槽 + 槽里种类的 `RsK` ⇒ 一切成员在 `subW T (ShW S)` 上有 `RsInv`/`RsK` | 构造 |
| `Gen.rs-same`, **`Gen.rs-other`** | Gen §2 | 升成员 $j$ 到 $v$ 后, 每个成员 $j'$ 的顶是 $\mathrm{cE}^{-}_{j'}(\mathrm{cE}_j v)$ (一起到 $v$) | 定理 (值) |
| `Gen.rs-least`, `Gen.share-no-loss`, `Gen.cE-inj` | Gen §2 | 升后世界最小; 带证据的世界与 "置成共享值" 互相 $\le$; 搬运单射 | 定理 (值) |
| `rsFam→Dg`, `slot→Dg` | Gen §3 | 一致的 `RsK` 族 ⇒ 对角解码; 共享槽 ⇒ 对角解码 | 定理 |
| `idSlot`, `stepSlot`, `supSlot`, `supℕSlot`, `upd-L` | Cp §1 | 共享槽沿恒等, `step` 旧种类, 并的一切分量 (下标任意), 并的一个 $\mathbb N$-分量提升 | 构造 |
| `Path`, `Cp.kupP`, **`Cp.cpSlot`**, `Cp.al0`, `Cp.ev0`, `Cp.botP` | Cp §2 | 沿一切路径的拷贝是共享槽 (对一切 `S`, `a`, `κ`, `b`); 基世界证据 | 构造; 定理 |
| `rsNew`, **`CpNew.famNew`**, `CpNew.coordNew` | Cp §3 | `step` 新种类精确置自己; 它的拷贝族 (坐标 `HB (Lev a′)`) 一起有 `RsK` | 构造 |
| `X≡`, `slotU`, **`famU`**, `ev0U`, `coordU` | Tw §1–2 | `X (s+1) ≡ a_s ⊞ B_s` (`refl`); 分层塔每站深拷贝族一起有 `RsK`; 基世界证据 | 构造; 定理 |
| `kup≡`, `κd≡`, **`κd-rs`**, `κd-other` | Tw §3 | `NegStratTwDeep.κd c` 是成员, 有 `RsK`; 升一个 `κd c` 把一切 `κd c′` 抬到同一个值 | 定理; 构造 |
| `kH-Dg`, `kHjx-Dg` | KH §1 | `κHc` (或 `κH f`) 一族的一致 `RsK` 族 ⇒ `HB (Lev c)` 之间的对角解码 | 定理 |
| **`no-slotKH`**, **`no-slotJx`** | KH §2 | 读回精确的 `Slot` 对 `κHc` / `κH f` 一族, 有槽上 `RsK` 与一个世界时, 推出 $\bot$ | 定理 (否定) |

## 前提实例

- `ShW` 不是空真: `Cp.ev0`, `SlotTw.ev0U` (基世界); 成员族非空 (`Cp.botP`, `SlotTw.pd`).
- `Gen` 的 `R₀`: `rsNew a′` (在 `Lev (hs a′)` 上).
- `no-slotKH` 的前提: `R₀ = rsNew a′`, $\omega$ = `w₀ (genLev (hs a′))`; 被否定的只是 `Slot` 这一前提 (对 `κHc`), 同一记录对拷贝族有实例 (`cpSlot`, `slotU`).

## 值 (交付 (b))

- **搬运保第一位置**: 是, 两个方向 (`Slot.pr→`, `pr←`; 拷贝实例里对 $b$ 递归化成恒等). 保合法: 两个方向 (`lgE→`, `lgE←`).
- **共享后读回丢不丢信息**: 坐标不丢 (`cE⁻-cE`, `cE-inj`); 世界在世界序里不丢 (`share-no-loss`: 带证据的世界与 "置成共享值" 互相 $\le$; 没有写成 `≡`, 那要函数外延). 代价是升一个成员就把一切成员一起抬到同一个值 (`rs-other`, `κd-other`); 这正是 "忘", 在拷贝族上无害 (没有相邻两级), 在 `κHc` 上致命 (`no-slotKH`).
- 序数值: 没有 (`famU` 没有接进折叠, 没有闭项).

## 只说什么, 不说什么

- **说**: 共享槽对同一级拷贝族是构造, 落到 `StratTwTw` 每一站的深拷贝; 读回精确的共享槽加 "先升槽再全写" 对 `κHc` / `κH f` 一族是否定.
- **不说**: 闭项与序数值; 拷贝族的读回 `rd` (所以不是完整的 `KLv`, 只是它的三条升界律 `RsK`); `famU` 与 `StratTwTw` 已有的 `KA`, `KT` 在带证据的世界上能否共处 (`KT (s+1)` 改同一分量的第二分量, 判断: 保证据; 其余未写); `κHc` 上不忘的或有损的升界 (未构造, 未否定).

## 判断 (单列)

1. **穷尽仍是判断.** "`κHc` 上剩下的形状只有: 不忘, 有损读回, 只取同一级, 换塔" 是判断, 下一路先挑战它.
2. **原卡点.** RsOwn 的 "共享槽要判定 $c\equiv$ `jx f`" 的猜测, 被细化成: 槽不必判定 (拷贝族上就不判定), 问题在族里有相邻两级. RsOwn 接手清单第 2 条 ("先对 '证据带单调搬运 τ_c' 写一条否定实验") 由否定一路的 `no-forget` 与本路的 `no-slotKH` 回答 (对读回精确的形状).
3. **拷贝在分层塔里覆盖多少.** `StratTwTw` 分量 $s+2$ 的旧种类 = `Lev (a_s ⊞ B_s)` 的种类; 其中沿 $B_s$ 路径落到 `Lev a_s` 的是拷贝 (`famU` 覆盖新种类那一份; 别的种类要 `Lev a_s` 上对应的 `RsK`, 例如底种类用 `RsOwnSW`), $B_s$ 自己的 `step` 产生的新种类不是拷贝. 后者的比例与它们对回灌的作用没有估计.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `Slot`, `ShW` | `RsOwnSW.Uf` 推广到坐标是高度; 律的定义域 (手册 §3.1) | 树逼出 |
| `Path`, `kupP`, `cpSlot` | `NegStratTwDeep.Cp.kup` 推广到一切路径; `nxtS` 的 $X_{s+1}=a_s\boxplus B_s$ | 树逼出 (种类结构自己的形状) |
| `idSlot`, `stepSlot`, `supSlot`, `supℕSlot`, `upd-L` | 对 `S₀`/`step`/`sup` 的构造子递归 | 脚手架 (提升) |
| `rsNew` | `NegKindLvUpd.upd-step` 的形状 (已有) | 沿用 |
| `no-slotKH` | 否定一路 `no-forget` + 本路 `rs-other` | 否定 (划界) |

归类 (判断): 提供信息. 没有新的构造子或节点, 不用 `Lab`, 闭包定理没有新前提. 第 4 层没有改前 3 层 (已有文件一律未改).

## 审计

- **编译.** 删本路五个模块 (`SlotIf` 除外: 否定一路在用它的接口; 其余 `SlotGen`, `SlotCp`, `SlotTw`, `SlotKH`, `Slot`) 自己的 `.agdai` (精确路径), 依赖用共享接口, 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/Slot.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4.1 秒, 峰值常驻约 0.81G. (`SlotIf` 在定稿时单独编译, 退出码 0; 定稿后只加了文件头一行, 由 `SlotGen` 的编译重新检查.)
- **禁用构造.** `python3 probes/Survey/scripts/slot/forbid.py`: 六个文件命中 0, 选项行都是 `--safe --without-K --lossy-unification`, 退出码 0. 没有 `Funext`/`FE₀`.
- **导入闭包.** `python3 probes/Survey/scripts/importclosure.py OCF.Align.Slot` (不加 `--only`): 退出码 0, 禁用表命中 0.

## 文件

| 文件 | 内容 |
|---|---|
| `SlotIf` | 接口: `Dg`, `Slot`, `ShW`, `RsFam`, `κHc`, `tp₁` |
| `SlotGen` | 一起升 (`Gen`), 值, 必要条件 |
| `SlotCp` | 三种提升; 沿一切路径的拷贝; `step` 新种类 |
| `SlotTw` | 分层塔每站的深拷贝; `κd` |
| `SlotKH` | `κHc` / `κH f`: 必要条件与否定 |
| `Slot` | 入口 |
| `probes/Survey/scripts/slot/forbid.py` | 禁用构造扫描 |

## 接手清单

1. **接进折叠:** 给拷贝族写读回 `rd` (坐标 `HB (Lev (ι_l X_s))` 与头种类 `HB (Lev (X s))` 之间一层结构搬运, 读回不需要 `≡` 律, 只要 `rd-fst`, `rd-lg`), 再证 `KA`, `KT s′` 在 `subW U (ShW (slotU s))` 上保证据 (需要 `upd` 在不同分量上不动的引理), 得到 `StratTwTw` 的一个带深拷贝回灌的闭项.
2. **一切 $s$ 与一切种类的证据合并:** 一个世界同时带一切 $s$ 的 `ShW (slotU s)` 与 `RsOwnSW.Uf` (底拷贝); 判断: 各升界只写自己的槽, 互不破坏, 未写.
3. **`κHc` 上不忘的形状:** 挑战判断 1; 否定一路的 `no-forget` 不杀 "高一级成员的新界依赖旧世界", 本路没有候选.
4. **非拷贝的深种类:** 量出 `StratTwTw` 分量里非拷贝的 `step` 新种类在折叠里是否真要回灌 (若不要, 拷贝族就够).
