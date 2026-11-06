# 升界只剩一种? 否定一路的入口

> 不含记号. 本路 (前缀 `NegRsOwn`) 是 `RsOwn` (构造一路) 的配对**否定**一路 (手册 §5.2). 作者本轮选定 (原话): "挑战 '只剩一种升界'". 对着接口 [RsOwnIf](RsOwnIf.lagda.md) ("接口定稿 2026-11-05 19:21 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: 接口定稿前写的 [NegRsOwnPre](NegRsOwnPre.lagda.md) (直接对 "精确置自己, 别处只增" 写否定); 定稿后写的 [NegRsOwnShape](NegRsOwnShape.lagda.md) (接口每种形状的盲定理与边界定理), [NegRsOwnFam](NegRsOwnFam.lagda.md) (`OwnFam` 的条件实例), [NegRsOwnInst](NegRsOwnInst.lagda.md) (对构造一路 `RsOwnSh`, `RsOwnSW`, `RsOwnBd` 19:25–19:28 版的检查, 只读导入; `RsOwnTm` 的闭项用的是同一个 `SW GΛ shΛ`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在标 "条件" 的 `…→WLPO` 里作前提.
>
> **判决.** 被挑战的判断 (`NegKindLv`: 以含函数的高度为下标的并里, 升界只剩 "精确置自己的分量, 别处只增不减且按分量不同" 一种未被否定的形状) 要改写成两句:
>
> 1. **"别处只增" 有两种读法, 一种被否定.** 别处**无条件**只增 (前提只有下标不等) 与精确置自己合起来推出分离子 (`ownB₁-sep`, `ownH₁-sep`, `ownBΛ⁺-sep`, `ownHΛ⁺-sep`; 定理), rs 可以任意依赖分量. 别处**只在 `rs≤` 的前提下**只增 (`KLv`/`RsK`/`OwnFam` 的写法) 未否定: 条件实例 `decJ→KLv`, `decJ→OwnFam` 说 "⇒ ⊥" 不可证; "⇒ 分离子" 未走通.
> 2. **"只剩一种" 只在不限制世界时成立; 限制世界后, "一起升" 也活下来** (构造一路, 编译过). 共享界 (`RsOwnSW`: 世界带 "一切底拷贝同界" 的证据) 与有界取大 (`RsOwnBd`: 世界带上界, 回灌值带证据) 都满足 `KLv` 的升界律, 对一切底拷贝, 不判定下标. 但它们**不是** "精确置自己": 置一个底拷贝就精确置了一切 (`inst-all-top`, `Λ-moves0`; 定理), 在共享界的世界里读回分量的底拷贝与第 0 站的底种类分不开 (`bd-merge`; 定理). 所以 "精确置自己" 这一形状本身仍只有一种未否定的写法 (第 1 条的后者); "一起升" 换了世界后不再被 `no-upAllR`/`no-same-rs` 打到, 因为那些定理用的世界被排除了 (`wS-not-Uf`, 构造一路的 `w′-not-Uf`).
>
> **对纲领与目标.** 纲领 3 (壁垒): 本路推出分离子的定理都是 "在裸下标不等的前提下要求别处的行为与自己处不同" (`Keep`, 无条件的 `rs-gr`), 与 `NegGenFoldUpd.upd₁-sep` 同型; 律的定义域 (手册 §3.1) 在这里的具体形状是: **`rs≤` 的前提 "旧顶 $\lhd v$" 是精确置自己能活下来的条件**, 去掉它 (允许把自己降到 $v$ 而别处仍不降) 就是分离子. 纲领 1, 2: 本路没有新的闭项; 构造一路的闭项 `RsOwnTm.TS` 合法 (不在本路否定之列). 目标 "让树自足": 给出两条树侧判据 (定理): (a) **一个升界只能精确地服务一个种类**, 除非世界把这些种类的界绑在一起 (`no-same-rs` 对一切共用一个 rs 的两个可判定地不同的底拷贝; 共享界下 `sh-all-top`); (b) **坐标类型随分量变的种类 (`κH f`) 要共享界, 编码必须对每个 $f$ 满射** (`inv→surj`), 经第 0 个分量的编码不满射 (`no-sh-ι0`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRsOwn where

import OCF.Align.NegRsOwnPre
import OCF.Align.NegRsOwnShape
import OCF.Align.NegRsOwnFam
import OCF.Align.NegRsOwnInst
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| **`ownB₁-sep`**, `ownAll₁-sep`, **`ownH₁-sep`**, **`ownBΛ⁺-sep`**, **`ownHΛ⁺-sep`** | Pre §1–3 | 精确置自己 (无前提) + 下标不同的拷贝无条件不降 ⇒ 分离子 (底拷贝 / 坐标是高度; `K₁` / `step KΛc`) | 定理 (否定) |
| `ownB₁→WLPO`, `ownH₁→WLPO`, `ownBΛ⁺→WLPO`, `ownHΛ⁺→WLPO` | Pre | 同上 ⇒ WLPO | 条件 (`FE₀`) |
| `topOnly₁-top`, `grOnly₁-gr`, `topOnlyH₁-top`, `grOnlyH₁-gr`, `own∘-top`, `own∘-gr`, `decJ→ownB₁` | Pre | 两半各自可满足; 可判定处同时成立; `DecJ` 下整个前提成立 | 定理 (前提实例) |
| `DecJ`, `decH→decJ`, **`decJ→sep`** | Pre §4 | 下标判定 (经典地成立) 推出分离子 | 定理 |
| **`decJ→KLv`**, `WithDecJ.rsJ` 及其律 | Pre §4 | `DecJ` 下 `κ₁ f` 上有精确置自己, 别处不动的 `KLv` | 条件 (`DecJ`) |
| **`no-ownJoin`**, `pair≤Lg-≤`, `pairLgV-*`, `pair≤V-*` | Pre §5 | 带前提不降 + 合法 + 某分量含 $v$ ⇒ ⊥ (`no-joinA`); 三条两两可满足 | 定理 (否定; 前提实例) |
| `rsK∘`, `keep∘`, **`rsK-moves`**, `moves-κH`, `moves-strict`, `decJ→RsK` | Shape §1 | `RsK` 的实例; `RsK` 不管别处 | 定理 (盲) / 条件 |
| **`keepFam-sep`**, **`keepFamH-sep`**, `decJ→keepFam` | Shape §2 | `RsK` 族 + `Keep` ⇒ 分离子 | 定理 (否定) / 条件实例 |
| **`all→own`**, **`own→all`** | Shape §3 | `AllFam` 与 `OwnFam` 逻辑等价 | 定理 (盲) |
| **`no-same-rs`**, **`no-allFam`**, `wS`, `wS-0`, `wS-1` | Shape §3 | 两份可判定地不同的底拷贝共用一个 rs ⇒ ⊥ | 定理 (否定) |
| `rsBd-empty`, `rsBd-triv`, **`no-bd-top`** | Shape §4 | `RsBd` 不定 `U` 时盲; `rsᵇ-top` 的前提被逼 | 定理 (盲; 否定) |
| `rsInv-empty`, `ShJ`, **`sh-same`**, **`sh-all-top`**, `wS-not-sh`, `Psh`, `sh-Psh`, `z₁-Psh` | Shape §5 | 共享界的世界里底拷贝分不开 | 定理 (盲) |
| **`inv→surj`**, `embι`, `no-ι0`, **`no-sh-ι0`**, `z₁-PE` | Shape §5 | `κH` 共享界要满射编码; 第 0 个分量的编码不满射 | 定理 (否定) |
| **`decJ→OwnFam`** | Fam | `OwnFam` 的条件实例 | 条件 (`DecJ`) |
| `uf-shJ`, `wS-not-Uf`, **`inst-all-top`** | Inst §1 | 构造一路的共享界 (`K₁`) 是 `ShJ`; 置一个拷贝就置一切 | 定理 |
| **`Λ-same`**, **`Λ-moves0`**, **`bd-merge`**, `bd-merge′`, `w₀Λ` | Inst §2 | 最终的 `KΛc` 上读回分量的拷贝与第 0 站底种类界相同 | 定理 |
| `bd-same-rs` | Inst §3 | 有界取大对两份下标不同的拷贝是同一个升界 (`refl`) | 定理 |

## 前提实例 (前提要可满足)

- `ownB₁-sep` 等: 两半各自可满足 (`topOnly₁`, `grOnly₁`, …); 可判定下标上同时成立 (`own∘`); 下标含函数时整个前提在 `DecJ` 下成立 (`decJ→ownB₁`), `DecJ` 经典地成立 (判断). 分离子经典地成立 (判断); `FE₀` 在 Agda 里证不出也否证不了.
- `keepFam-sep`: `keep∘` (可判定处), `decJ→keepFam` (`DecJ` 下).
- `no-same-rs`, `no-allFam`: 只要 `rs-top` 与同一个 rs: `NegKindLvRaise.upAllR (λ a v → v)`; 只要 `rs≤` 与同一个 rs: 恒等; 两个 `RsK` 各自: `decJ→RsK`.
- `no-ownJoin`: `pair≤Lg`, `pairLgV`, `pair≤V` (两两).
- `no-bd-top`: `rsBd-triv` 说 `RsBd` 本身可满足; 去前提的那一条单独可满足 (`topOnly₁`).
- `no-sh-ι0`: `PE embι` 有世界 (`z₁-PE`); `RsInv` 本身可满足 (`rsInv-empty`, 构造一路 `invB`).
- `sh-all-top`, `inst-all-top`, `Λ-moves0`: 世界取基世界 (`z₁-Psh`, `w₀Λ`); `invB`, `rsB` 是构造一路的无条件构造.

## 只否定什么, 不否定什么

- **否定** (编译的): 精确置自己 + 下标不同的拷贝无条件不降 (分离子); `RsK` 族 + `Keep` (分离子); 两份可判定地不同的底拷贝共用一个满足 `rs-top`, `rs≤` 的 rs (⊥), 包括 `inV` 不分 $j$ 的 `AllFam`; 带前提不降 + 合法 + 某分量含 $v$ (⊥); `RsBd` 的 `rsᵇ-top` 去掉前提 (⊥); `κH fω` 上经第 0 个分量编码的共享界 `RsInv` (⊥).
- **不否定**: `OwnFam`/`KLv` 形状 (每个种类自己的 rs, 精确置自己, `rs≤` 带前提) — 未走通; 构造一路的 `RsInv` (`invB`), `RsK` (`rsB`), `RsBd` (`BD.rsBd`), 闭项 `TS`; `κH` 上经满射编码的共享界; 有损回灌. 本路**没有关闭任何路线**.

## 判断 (单列)

- **"精确置自己 + 带前提的只增" 的状态.** 单次调用的分离子论证在这里失效: 相等的情形是不等情形结论的特例 (`NegRsOwnPre` §4 末). 在函数可读连续模的模型里, 这一形状也许可以实现 (未写成定理); 若如此, "⇒ WLPO" 不可证. Agda 里的构造需要从世界读出它在自己下标处的连续模, 不可得 (判断). 所以这一形状可能既构造不出也否定不了.
- **共享界的值.** `bd-merge` 说在 `TU` 里读回分量的底拷贝不提供第 0 站底种类之外的界; 这是否让 `RsOwnTm.TS` 不高于不按它们回灌的版本, 没有 `ord` 定理.
- **"穷尽"**: 本路没有说 "剩下的只有这几种"; 上面第 1, 2 条的分类 (无条件只增 / 带前提只增 / 限制世界后的一起升) 是对本轮看到的形状的分类, 不是穷尽定理.

## 审计

- **编译.** 删本路五个模块的 `.agdai` (精确模块名) 后从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegRsOwn.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 5 秒, 峰值常驻约 0.8G. 依赖用共享接口; 对着的构造文件: `RsOwnIf` (19:21), `RsOwnSh` (19:27), `RsOwnSW` (19:25), `RsOwnBd` (19:28), `RsOwnTm` (19:26).
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0.
- **禁用构造**: 五个文件的代码块没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; `FE₀` 只作 `…→WLPO` 的前提; 没有 UIP 前提.

## 文件

| 文件 | 内容 |
|---|---|
| `NegRsOwnPre` | 接口定稿前: 无条件只增的否定, `DecJ` 条件实例, `no-ownJoin` |
| `NegRsOwnShape` | 接口每种形状的盲定理与边界定理 |
| `NegRsOwnFam` | `OwnFam` 的条件实例 |
| `NegRsOwnInst` | 对构造一路实例的检查 |
| `NegRsOwn` | 入口 |
