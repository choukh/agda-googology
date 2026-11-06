# 一次封闭层号上带证据的回灌 (入口与判决)

> 不含记号. 本路 (前缀 `SLFb`) 是构造一路, 与否定一路 `NegSLFb` 配对, 共用接口 [SLFbIf](SLFbIf.lagda.md) ("接口定稿 2026-11-05 20:06 (首次编译通过)", 变更记录: 无). 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 作者本轮选定 (原话): "SL 上写带证据的回灌". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提 (唯一的 UIP 只作 `SLFbStuck.rsJ-top` 的前提, 不进闭项与证书). 闭项, 证书, FGH 无模块参数. 已有文件一律未改.
>
> **判决.**
>
> - **(a) 交了.** 无条件闭项 `SLFbTm.TF : A`, 证书 `Lg-TF`, FGH `fghF`. 种类结构是 `SL` 在站下标上的子结构 `SN = SNᵢ kₙ` ($k_n$ = `ofHB (tw n)`, 第 $n$ 站层号; 种类与坐标同 `SL`, 世界是 `SL` 世界的限制, 高度嵌入 `embN` 保第一位置与合法). **每站头种类** $(n,\mathrm{new})$ (坐标是第 $k_n$ 层的值 `HB (Lv kₙ)`, 是高度) **对一切 $n$ 有级回灌** (`headFb`), 包括层号含函数分支的 $n\ge2$ (`stage-lΩ`); 升界在 $\mathbb N$ 下标上点更新, 不比较层号. 深种类里, 路径不经坐标下标的 (例: 第 $n\ge2$ 站 `lΩ lz _` 的左分量的新种类) 也有回灌 (`deep2-left-fed`); 经坐标下标的有损 (`deep2-lossy`).
> - **(b) 值: 有形状定理与一条盲点定理, 没有序数值定理.** `head-rs-top` (升后头种类的顶精确是 $v$), `rd-n1` (读回看见数据), `head-ℓ1`/`head-ℓ0` (级层: 第 $n\ge1$ 站是 $1$, 第 0 站是 $0$), `SLFbRd.onlyA-rdQ` (级层 1 的读回只产生一种 $\Omega$-结点, 即第 0 层值的种类): 回灌进头种类的值都 $<\Omega_2$ 的拷贝 (判断的依据).
> - **任务第 1 条在 `SL` 本身的世界上: 未找到.** 带字面公共上界证据 (`StallDxBdec.bdec`) 判等可构造, 但 (1) `SL` 的世界以 `LH` 为下标, `ofHB (toHB k)` 与 `k` 不定义相等; (2) 换成以带证据的高度为下标的世界, 对角上的判等证明不是 `refl`, 不开 K 证不出 `rs-top`. 编译错误原文与条件定理 `rsJ-top` (前提: 该高度处的 UIP; 实例 `uip-hz`) 在 [SLFbStuck](SLFbStuck.lagda.md). 出口是把证据换成站号 ($\mathbb N$, 对角上 `refl`).
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` 的元素, FGH 在树上算; `SN` 的高度经 `embN` 是 `SL` 的高度. 纲领 2: 无公理, 检查器接受. 纲领 3: 折叠里唯一的比较是 `cmpB` (公共上界 $\Lambda^N$); 判定只在 $\mathbb N$ 与 $\top\uplus B$ 的构造子上; 不比较层号, 不比较坐标; 没有 "升一份留别份" 于含函数下标 (否定一路 `NegSLFbSep.updP-sep` 的形状不出现: `SN` 的世界没有含函数下标的分量可留). 纲领 4: 不读记号, 导入闭包与切片干净 (审计). 目标 "让树自足": 本路给出一条树侧事实: **C6 的升界难处不在 "判定含函数的下标", 在下标类型的判等是否对角 `refl`**: 带公共上界的判等有 (`bdec`), 但它的证明不唯一 (卡点 2); 下标类型换成 $\mathbb N$ (站号) 后, 含函数的层号只作数据 (`kₙ n`), 不被比较, 头种类的升界就是构造.
>
> **离 ψ₀Λ 候选闭项还差什么 (判断).** (1) **读回的级**: 头种类的级层是 1, 不是它自己的级 $k_n$; 读回只产生第 0 层值的种类的结点 (`onlyA-rdQ`). 要按自己的级读回, 需要 `KindLvRd.readL` 那样的级读回搬到 `Lv` 上 (`Lv` 的底是 `S⊥`, `lΩ` 多一个 `step` 分量, 旧种类结点经 `node` 只命题相等于 `lΩ (lvl k κ) _`, 要运输). (2) **站间的层**: $1+c$ 层一类不在站上的层的种类只作深种类出现, 经坐标下标的有损; 它们的回灌要另一种证据. (3) 没有序数值定理. 读法 (判断, 只从树形与回灌算): 最终层 $\Lambda^N$ 的树形是 $\sum_n\Omega_{k_n+1}$ (共尾到 $\Lambda$); 回灌进一切头种类的坐标都只含第 0 层值的种类的结点 (`onlyA-rdQ`) 或只含后继与 ℕ-极限 (`ad`), 所以每站头种类的分支只在 $<\Omega_2$ 的拷贝上被访问; 我判断读法不超过 ψ₀(Ω₃) 的量级, 远低于 ψ₀Λ. 这是判断, 没有编译依据.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SLFb where

import OCF.Align.SLFbIf
import OCF.Align.SLFbKit
import OCF.Align.SLFbRd
import OCF.Align.SLFbTm
import OCF.Align.SLFbStuck
```

## 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `SNᵢ`, `jN`, `resN`, `AK`, `KC`, `HdFb`, `RsSL`, `RsSLᴾ`, `RsUp`, `RsSL⊵`, `RsEv` | If | 接口 | 类型 |
| `topV`, `toB`, `kcNew`, `kcOld`, `kcℕ`, `kcL`, **`kcLv`**, `akV` | Kit | 每层里路径不经坐标下标的种类的回灌件 (加法 + 精确升界); 可读成 `A` 的种类 | 构造 |
| `deep-lossy-Lv`, `new-fed`, `lΩ-left-fed`, `akV-lΩ` | Kit | 坐标下标之下有损; 一切 `step` 新种类有回灌件; `lΩ` 层左分量的新种类有回灌件 | 定理 (`refl`) |
| `rdQ`, `rdQ-fst`, `Lg-rdQ` | Rd | 第 1 层数据读进 `HB Q` (结点取 `AK` 的种类), 合法 | 构造 |
| **`onlyA-rdQ`** | Rd | 读回只产生一种 $\Omega$-结点 | 定理 (盲点) |
| `kₙ`, `SN`, **`embN`**, `embN-⊲`, `Lg-embN`, `res-Bd` | Tm §1 | 站下标子结构, 高度嵌入 `SL` 保第一位置与合法, 界在限制下定义相等 | 构造; 定理 |
| `GN`, `LdN`, `flN`, `ΩN`, `B`, `ΛN`, `lΛN`, `one⊲N` | Tm §2–3 | `GenK`, 层 $\sum_n \Omega_{k_n+1}$ | 构造 |
| `kc→KLv`, `hdKit`, `dpKit`, `KH₁`, `KH`, `KHn`, **`lvN`** | Tm §4 | 按级回灌: 头种类级层 1 (第 0 站 0), 深种类级层 0 或有损 | 构造 |
| **`TF`**, **`Lg-TF`**, `fghF` | Tm §5 | 无条件闭项, 证书, FGH | 构造 |
| **`headFb`**, `tw-shape`, **`stage-lΩ`**, `akV-suc`, **`head-ℓ1`**, `head-ℓ0`, **`head-rs-top`**, `rd-n1` | Tm §6 | 每站头种类有回灌 (对照 `RsOwnTm.head-still-lossy`); 第 $m+2$ 站层号是 `lΩ lz _`; 级层; 升后顶精确; 读回看见数据 | 定理 |
| **`deep2-lossy`**, `deep2-left-fed`, `fb-lossyN`, `top-base-V`, `top-baseN`, `emb-head` | Tm §6 | 深种类 (对照 `NegStratTw.deep-lossy`); A-回灌仍有损 (对照 `fb-lossy`); 基世界顶是底 (对照 `top-base`); 头结点嵌成 `SL` 的站新种类 | 定理 |
| `J`, `WJ`, `rsJ`, **`rsJ-top`** | Stuck §1 | 带公共上界证据的高度为下标的世界上判等式升界; 对角精确, 前提 UIP | 条件定理 (前提 `UIPat`) |
| `decZ`, `nz`, **`uip-hz`** | Stuck §2 | `hz` 处 UIP (局部 Hedberg), 前提实例 | 定理 |

## 前提实例

- `rsJ-top` 的模块参数: 任一合法世界与合法高度 (例 `FabLFReGen` 的基世界与 `LFReTower.Λ`, `Lg-Λ`); 前提 `UIPat h₀` 的实例: `h₀ = hz` (`uip-hz`). 第 $n\ge2$ 站的 `tw n` 处的 UIP 未证, 未否定.
- `HdFb` 的实例就是 `headFb` (不是空真: `lvN` 对头种类给 `inj₁`).

## 对照表 (任务第 2 条)

| 已有定理 | 说的 | 本路对应 |
|---|---|---|
| `FabLFReGen.fb-lossy` | `SL` 上一切种类 A-回灌有损 | `fb-lossyN` 同 (A-回灌仍有损); 但回灌改走 `lv`: `headFb`, `deep2-left-fed` |
| `FabLFReGen.top-base` | 基世界顶是底 | `top-baseN` 同; 折叠里头种类的顶被 `rs` 升 (`head-rs-top`) |
| `RsOwnTm.head-still-lossy` | 后面各站头种类有损 | `headFb`: 一切站头种类有回灌, 含层号含函数的站 (`stage-lΩ`) |
| `NegStratTw.deep-lossy` | 深种类全部有损 | `deep2-lossy` (经坐标下标的仍有损), `deep2-left-fed` (左分量的有回灌) |

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `SNᵢ` (站下标子结构) | 卡点 1, 2: 下标类型要对角 `refl` 的判等; 站号由 `LFReTower.tw` 给出 | 树逼出 (`SLFbStuck` 的编译错误) |
| `kcLv` (路径不经坐标下标的种类有回灌件) | 对种类结构构造子递归; 坐标下标不判定 | 树逼出 |
| `ad = b ⊞ toB a` (第 0 级读回) | `GenFoldRun` 的 A-回灌读法 (`sum`) 搬到高度 | 沿用 |
| `rdQ` | `GenFoldRd.rd₁` 换目标 | 沿用 (脚手架: 目标是某层的值) |
| 层 $\sum_n\Omega_{k_n+1}$ | 站的新种类的 $\Omega$-结点; 树形共尾到 $\Lambda$ | 树逼出 (`SN` 只有站的新种类) |
| `topV` | `topLv` 的重写 (分量函数有名字) | 脚手架 (定义相等要求) |

归类 (判断): 提供信息. 一步定理是 "下标类型的判等对角 `refl` 即可升界" (`rsJ-top` 的条件形式与 `SN` 的构造), 这一站新用到的字段是 `sup` 的下标类型 ($\mathbb N$ 代替 `LH`); 否定侧的划界由 `SLFbStuck` 的两个编译错误与否定一路给. 没有新的构造子或节点, 不用 `Lab`. 第 4 层没有改前 3 层.

## 接手清单

1. **按自己的级读回.** 把 `KindLvRd.readL` 搬到 `Lv` (底 `S⊥`): 头种类 $(n,\mathrm{new})$ 的级层取 `hs (up c_n)` ($c_n$ 是 `SN` 里代表 $k_n$ 的高度), 读回进 `HB (Lv kₙ)`. 难点: `Lv (node k κ h)` 与 `sup (⊤ ⊎ HB (Lv (lvl k κ))) …` 只命题相等 (`E-lvl`), 要运输.
2. **站间层的种类.** 经坐标下标的深种类仍有损; 试 RsOwn 形状 1 在 `Lv` 上的类比 (同读回层的拷贝同界, 否定一路 `NegSLFbSh` 已给同级同界的边界), 或给 `SN` 的下标换成 "站号 + 有限路径" 一类对角 `refl` 的码.
3. **UIP 卡点.** `tw n` ($n\ge2$) 处的 `UIPat` 是否可证 (不开 K, 不加外延): 未证未否定; 若可证, `SLFbStuck.rsJ` 给出 `SL` 上以带证据高度为下标的升界.
4. **值.** 给 `TF` 与 `FabLFReGen.TΛ` 写序数值的比较 (至少一个方向); 或把 `onlyA-rdQ` 推到折叠的输出上 (读法上界的定理).

## 否定一路对本实例的检查 (引用, 已编译; 未复核)

`NegSLFbInst` (只读导入本路 20:08–20:13 版): `onlyA-rdQ` 的同形结论; `head-ak-lz`: 对一切 $m$, 第 $m+1$ 站头种类的读回结点的种类读回层是 `lz`; `cp1 = (3 , inj₁ (inj₂ 1 , inj₁ tt , inj₂ tt))`: 级与坐标类型同第 1 站的头, 但 `lvN cp1 ≡ inj₂ tt`, 升第 1 站的头不动它. 这正是接手清单第 2 条 (同级的拷贝在坐标下标之下有损). 否定一路的盲定理 `NegSLFbBlind.akConst` 更正了接口文件头的一句 (见接口变更记录).

## 审计

- **编译.** 删本路五个模块 (`SLFb`, `SLFbKit`, `SLFbRd`, `SLFbTm`, `SLFbStuck`) 自己的 `.agdai` (精确路径; 接口 `SLFbIf` 的留着, 否定一路在用), 依赖用共享接口, 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/SLFb.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4 秒, 峰值常驻约 0.70G. 接口变更记录 (只改文字) 之后再编译入口, 退出码 0.
- **禁用构造.** `python3 probes/Survey/scripts/slfb/forbid.py`: 六个文件命中 0, 选项行都是 `--safe --without-K --lossy-unification`, 退出码 0. UIP 只作 `SLFbStuck.rsJ-top` 的前提 (`UIPat`), 不在闭项与证书的闭包里 (切片: 前 3 层闭包里没有 `SLFbStuck` 的块).
- **导入闭包.** `python3 probes/Survey/scripts/importclosure.py OCF.Align.SLFb` (不加 `--only`): 退出码 0, 禁用表命中 0; `SLFbTm`, `SLFbStuck`, `SLFbIf` 各自也是 0.
- **依赖切片.** `depslice.py`: `SLFbTm:TF` 到达 361 块, `Lg-TF` 362, `fghF` 379, `headFb` 205, 记号块都是 0; 正对照 `Closure:fs₂` 到达 60, 记号块 54.

## 行数 (定义级切片, 口径同 `newtwr/locslice_newtwr.py`)

`python3 probes/Survey/scripts/slfb/locslice_slfb.py <H>`:

| 层 | 本路新增 | 树侧累计 | 记号模块 |
|---|---|---|---|
| 1 定义 | 20 | 386 | 0 |
| 2 + 折叠 (子结构, 回灌件, 读回, 按级回灌的折叠, 层, 闭项, FGH) | 223 | 1463 | 0 |
| 3 + 证书 | 225 | 1465 | 0 |
| 4 + 形状, 盲点, 卡点 | 368 | 1655 | 0 |

对照: 标杆 1513, `FabLFReGen.TΛ` 约 1042 (同口径, 前 3 层). 本路比 `TΛ` 多的主要是 `KindLvRun` (213, 按级回灌的折叠代替 `GenFoldRun`) 与本路 225. 切片是语法近似: `KindLvTw` 顶层的 `open KRd …` 使 `KindLvRd` (93) 与 `KindLvEmb` (45) 被计入, 本闭项不用级读回 `readL` (判断, 依据: `SLFbTm` 只取 `collLv`); 扣去后约 1327. 层 2 与层 3 只差 2 行: 回灌件与 `KLv` 的记录里带着单调与合法的字段, 证书的大部分在层 2 已被拉进.
