# 积世界上的升界: "只剩一种" 的挑战 (构造一路的入口与判决)

> 不含记号. 本路 (前缀 `RsOwn`) 是构造一路, 与否定一路 `NegRsOwn` 配对, 共用接口 [RsOwnIf](RsOwnIf.lagda.md) ("接口定稿 2026-11-05 19:21 (首次编译通过)", 变更记录: 无). 作者本轮选定 (原话): "挑战 '只剩一种升界'". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> **判决: 判断 "只剩一种" 被推翻 (就它所说的范围: 以含函数的高度为下标的并里的升界形状); 原判断点名的那一种 (精确置自己, 别处只增, 依赖分量) 对坐标是高度的种类 `κH f` 未找到.**
>
> - **新形状 1: 世界带不变式 "底拷贝同界" (`RsOwnSW`; 构造).** 世界换成 $\Sigma\,w\,(\exists a.\ \text{每份底拷贝的界}\equiv a)$ (`subW T Uf`); 升界 = 把每份底拷贝置成 $v$. `KLv` 的三条升界律 (`rs≤`, `rsLg`, `rs-top` 无前提) 对**一切**底拷贝成立, 包括下标含函数的 `κ₁ f` (`K₁` 上 `rsK₁`, `KΛc` 上 `new-lv`), 不判定下标. 它是 "同一个 $R$ 一起升" ($R\,a\,v=v$) 加一份世界证据; `NegKindLvRaise.no-upAllR` 的反例世界 `w′` 不在新世界类型里 (`w′-not-Uf`, 定理). 不撞 "留" 的分离子 (不要求留), 也不撞否定一路的 `NegRsOwnPre.ownB₁-sep` (那里要求别处**无条件**不降; 这里别处只在 `rs≤` 的前提下变大).
> - **新形状 2: 带字面公共上界的一起升 (`RsOwnBd`; 构造).** 世界带上界 $\Lambda$ (每份底拷贝 $\lhd\Lambda$), $v$ 带 $v\lhd\Lambda$ 的证据; 每份底拷贝取大 `Rᵇ`. 世界变大无前提, `rs-top` 在旧顶 $\lhd v$ 时成立. 对一切带 `ShB` 的种类结构 (`Lev c`, `Kc s`, `KΛc`), 推广 `RaiseCFba.upAllᵇ` (原来只在 `SA` 上).
> - **任务列出的其余三种挑战方向, 落在上面两种里或已知的里 (判断):** "依赖证据而不依赖下标" = 形状 1 (升界读的是世界证据里的 $a$, `tp≡a`); "经 `Lev` 的结构递归" = 形状 1, 2 的 `rB`, `rM` (对种类结构的构造子递归, 不判定下标); "带来历的世界让自己的分量可判定" = 把自己的分量搬到可判定的槽位, 即 `NegKindLvUpd.upd-step` (`step` 的新种类) 与 `KindLvTw` 未走通的互递归塔; 本路没有新构造.
> - **原判断点名的形状, 对 `κH f` (坐标 `HB (Lev (jx f))`) 未找到.** 卡点 (判断, 不是否定): `rs-top` 要在下标 `inj₂ (hs (jx f))` 处得到 $v : $ `HB (Lev (jx f))`; 对变量下标 $c$, 分量 $c$ 的世界类型是 `Wd (step (Lev c))`, 用 $v$ 造出这个类型的值要一条路径 $c\equiv$ `jx f`, 不判定下标就拿不到. 形状 1 的办法 (让同类拷贝共享一个界) 要求被一起升的拷贝坐标类型相同, 底拷贝都是 `A`, 坐标是高度的种类随级变. 没有编译错误可报 (没有写出可以送检的候选), 没有否定定理.
>
> **对纲领与目标.** 纲领 1, 2: 交出一个新的无条件闭项 `TS` (`RsOwnTm`), 塔与 `KindLvTw` 相同, 最终坍缩在带不变式的世界上, 一切底拷贝按 `KLv` 回灌. 纲领 3: 两种新形状都只在一个世界里比较, 公共上界是字面的 (形状 1 的 $a$, 形状 2 的 $\Lambda$); 不要求任何下标上的判定. 纲领 4: 本路不读记号. 目标 "让树自足": 给出一条树侧判据 (判断): **"别处只增" 的难处不在 "依赖分量", 在 "别处的旧界与 $v$ 没有字面关系"**; 世界自己带上这份关系 (同界, 或公共上界) 时, 一起升就是构造. 代价也是树侧的: 一起升让一切底拷贝的界一起变大, 与 "精确置自己, 别处不动" 的读回不同 (值上的影响没有定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwn where

import OCF.Align.RsOwnIf
import OCF.Align.RsOwnSh
import OCF.Align.RsOwnSW
import OCF.Align.RsOwnBd
import OCF.Align.RsOwnTm
```

## 形状一览 (接口 `RsOwnIf` 的记录)

| 形状 | 记录 | 状态 | 依据 |
|---|---|---|---|
| 留 (升一份留别份) | `PW.Keep` | 否定 (下标含函数时) | `NegKindLvUpd.updH₁-sep`, `NegGenFoldUpd.upd₁-sep` (定理) |
| 同一个 $R$ 一起升, 世界不带证据 | `PW.AllFam` | 否定 (底拷贝, `rs-top` 无前提) | `NegKindLvRaise.no-klv-upAllR` (定理) |
| 精确置自己 + 别处**无条件**只增 | (否定一路的 `OwnB₁`, `OwnH₁`) | 否定 | `NegRsOwnPre.ownB₁-sep`, `ownH₁-sep` (定理, 否定一路) |
| 精确置自己 + 别处在 `rs≤` 前提下只增, 依赖分量 | `PW.OwnFam` | 底拷贝: 条件实例 (`NegRsOwnPre.decJ→KLv`, 前提 `DecJ`); `κH f`: 未找到, 未否定 | — |
| **一起升 + 世界带同界证据** | `RsInv` (经 `inv→RsK` 得 `RsK`) | **构造** (一切底拷贝) | `RsOwnSW.invB`, `rsB`, `KLvB`; `RsOwnTm.rsK₁`, `new-lv` |
| **带字面公共上界的一起升** | `RsBd` | **构造** (一切底拷贝) | `RsOwnBd.BD.rsBd`, `rsBdΛ` |
| 自己的分量在可判定的槽位 | — | 构造 (已知) | `NegKindLvUpd.upd-step`, `KindLvTw.up₂` |

## 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `ShB`, `shS₀`, `shStep`, `shSup`, **`shLev`**, **`shKc`**, **`shΛ`** | Sh | 底拷贝的视图 (`Bot`, 可判定 `bot?`), 全称 `Al`, 置一切底拷贝 `rB`, 带证据逐份换 `rM`, 与它们的律; 对 `S₀`/`step`/`sup` (任意下标) 各一行, 组装到一切 `Lev c`, `Kc s`, `KΛc` | 构造 |
| `inv→RsK` | SW §1 | `RsInv T P tp κ → RsK (subW T P) (topSub tp) κ` | 构造 |
| `SW.Uf`, `SW.TU`, **`SW.invB`**, **`SW.rsB`** | SW §2 | 世界带 "每份底拷贝 $\equiv a$"; 每个底拷贝的 `RsInv`, `RsK` | 构造 |
| `SW.tp≡a`, `SW.lg-a`, `SW.tpA-bound` | SW | 底拷贝的顶就是共享的 $a$; $a$ 合法; A-回灌读的就是该拷贝的顶 | 定理 |
| `SW.genU`, `SW.ldU`, `SW.flU`, `SW.shF` | SW §3 | 坍缩所需的 `GenK`, `LgDn`, `FbLg`; 底拷贝的 A-回灌 | 构造 |
| **`SW.KLvB`**, `SW.lvU`, **`SW.lv-bot`** | SW §4 | 每个底拷贝的 `KLv` (级层 $0$, 读回 `sum`); 每个底拷贝有级回灌 | 构造; 定理 |
| **`SW.rs-all`**, **`SW.rs-least`** | SW §5 | 升后每份底拷贝恰为 $v$; 升后世界是 "比原世界大且每份底拷贝 $\unrhd v$" 的世界里最小的 | 定理 (值) |
| **`BD.rsBd`**, `rsBdΛ`, `BD.up-hi`, `BD.upUp`, `BD.pick-v` | Bd | 带公共上界的一起升满足 `RsBd`; 升后每份 $\unrhd v$ 且 $\lhd\Lambda$ | 构造; 定理 |
| `Cv.cv`, `Cv.cv-⊲`, `Cv.Lg-cv` | Tm §1 | `HB T → HB (subW T P)`, 保第一位置与合法 | 构造; 定理 |
| **`TS`**, **`Lg-TS`**, `fghS` | Tm §2 | 无条件闭项, 证书, FGH | 构造 |
| `old-lossy-lv`, `old-lossy-fb`, **`new-lv`**, `all-bot-lv`, **`head-still-lossy`** | Tm §3 | `κj f` (含函数下标的底拷贝) 在 `KindLvTw`/`GΛ` 里有损, 在这里有 `KLv`; 后面各站的头种类仍有损 | 定理 (`refl`) |
| **`w′-not-Uf`** | Tm §3 | `NegKindLvRaise.w′` 不满足同界不变式 | 定理 (否定) |
| **`rsK₁`** | Tm §3 | `K₁` 上一切 $f$ 的 `κ₁ f` 有 `RsK` (带不变式的世界) | 构造 |

## 前提实例

- `RsInv`, `RsK` on `TU`: 不变式 `Uf` 有实例 (基世界 `w₀ G , (azero , al0)`, `genU`); 所以 `RsInv` 不是空真 (接口 "盲" 一段要求的).
- `RsBd`: `Up` 的实例: 基世界 (每份 $0$) 取 $\Lambda=0$ 或任一合法 $\Lambda$ (`z⊲`); `U` 的实例: $v\lhd\Lambda$ (例如 $v=\Lambda$). 本路没有把它写成定理 (判断: 平凡).
- `w′-not-Uf`: `w′` 是 `NegKindLvRaise` 里的具体世界.

## 只说什么, 不说什么

- **说**: 两种新形状有构造, 律成立; 闭项 `TS` 合法; `κj f` 一类底拷贝在 `TS` 的坍缩里有 `KLv`; 升后世界的大小 (`rs-all`, `rs-least`, `up-hi`).
- **不说**: `TS` 的序数值 (没有 `ord` 定理, 不与 `KindLvTw.TK` 比大小; `TS` 也**没有** `KindLvTw` 里 `κ₁` (坐标是高度, 级 $1$) 的按级回灌, 所以不是 `TK` 的加强); `κH f` 上精确置自己的形状 (未找到); 共享界的语义代价 (一个底拷贝回灌时其余底拷贝的界被一起抬高) 对值的影响. 本路没有关闭任何路线.

## 判断 (单列)

1. **穷尽仍是判断.** "以含函数的高度为下标的并里, 未被否定的升界形状有: 原判断那一种, 形状 1, 形状 2" 是判断; 形状 1, 2 的共同点是 "世界带着别处旧界与 $v$ 的字面关系". 下一路应挑战: 有没有不加世界证据, 也不判定下标的形状.
2. **`κH f`.** 形状 1 对坐标是高度的种类不能照搬 (坐标类型随级变, 没有共享的槽); 我想到的变体 (世界证据里带一族搬运 $\tau_c$ : `HB (Lev (jx f))` → `HB (Lev c)`, 要求 $\tau_{jx\,f}=\mathrm{id}$) 在基世界上要给出 $\tau$, 又要判定 $c\equiv$ `jx f`; 未编译.
3. **能否接进回灌的值.** `RsBd` 要回灌值 $v$ 在世界的公共上界之下; `KindLvRun` 的 $v=\mathrm{sum}(\mathrm{top},\Delta)$ 没有现成的上界, 所以闭项用 `RsInv`. 未检查折叠能否顺带给出上界.
4. **值.** 读法不写 (没有序数值定理). 形状 1 让一切底拷贝的回灌从有损变成 A-回灌, 但 `GenFold`/`NewTwr` 的第一个障碍 (头种类有损) 不动 (`head-still-lossy`); 所以我不认为 `TS` 比 `TK` 高一档以上 (判断, 无依据可编译).

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `ShB` (底拷贝视图, `Al`, `rB`, `rM`) | 对 `S₀`/`step`/`sup` 的构造子递归 | 树逼出 (种类结构自己的形状) |
| `Uf`, `subW` | `rs≤` 的前提只管自己的顶, 别处的界要与它有字面关系 (手册 §3.1 律的定义域) | 树逼出 |
| `Rᵇ` 逐份取大 | `RaiseCBd` (已有) | 树逼出 |
| `inv→RsK`, `cv`, `Lg-cv` | 换世界类型后的搬运 | 脚手架 (换类型带来) |
| `KLvB` 的读回 `sum` | `GenFoldRun` 的 A-回灌读法 (已有) | 沿用 |

归类 (判断): 提供信息 (否定定理之外, 给出两种新形状的构造与一个划界定理 `w′-not-Uf`). 没有新的构造子或节点, 不用 `Lab`. 第 4 层没有改前 3 层 (已有文件一律未改).

## 审计

- **编译.** 删本路四个模块 (`RsOwnSh`, `RsOwnSW`, `RsOwnBd`, `RsOwnTm`) 自己的 `.agdai` (精确路径; 接口 `RsOwnIf` 的接口文件留着, 否定一路在用, 它的源文件在定稿后只加了文件头一行, 已重新检查), 依赖用共享接口, 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/RsOwn.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4.2 秒, 峰值常驻约 0.81G.
- **禁用构造.** `python3 probes/Survey/scripts/rsown/forbid.py`: 六个文件命中 0, 选项行都是 `--safe --without-K --lossy-unification`, 退出码 0. 没有 `Funext`/`FE₀` (本路没有条件定理).
- **导入闭包.** `python3 probes/Survey/scripts/importclosure.py OCF.Align.RsOwn` (不加 `--only`): 退出码 0, 禁用表命中 0.

## 文件

| 文件 | 内容 |
|---|---|
| `RsOwnIf` | 接口: `RsK`, `PW.{ViaΦ, Keep, AllFam, OwnFam}`, `RsBd`, `subW`, `topSub`, `RsInv` |
| `RsOwnSh` | 底拷贝的共享结构 `ShB` 与实例 |
| `RsOwnSW` | 同界不变式, `RsInv`/`RsK`/`KLv`, `GenK` |
| `RsOwnBd` | 带公共上界的一起升 |
| `RsOwnTm` | 闭项 `TS`; 形状定理 |
| `RsOwn` | 入口 |
| `probes/Survey/scripts/rsown/forbid.py` | 禁用构造扫描 |

## 接手清单

1. **否定一路对准判断 1:** 不加世界证据、不判定下标的升界形状 (`PW.OwnFam` 在 `κ₁ f` 上无条件实例, 或 `OwnFam ⇒ Sep`).
2. **`κH f`:** 形状 1 的类比要一个共享槽; 试 "世界证据带一族单调搬运 $\tau_c$" (判断 2), 先写否定实验 (基世界的证据是否要判定).
3. **值:** 给 `TS` 与 `KindLvTw.TK` (或 `NewTwr.TN`) 写序数值的比较 (至少一个方向的 `≼`); 或者写一条盲定理说明共享界的回灌在哪里与逐份回灌不同.
4. **合并:** 把 `KindLvTw.K1` (级 $1$ 的按级回灌) 也搬到 `TU` 上 (`κ₁` 不是底拷贝, 它的 `rs` 是 `step` 上的点更新加 `isTwo`, 与 `Uf` 不冲突; 未写).
