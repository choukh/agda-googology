# 事件历史世界 (方向 B): 入口与判决

> 不含记号. 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §5.2. 作者选定的方向原话: "B 事件历史世界". 方向 A (`AdmW*`) 另有两路, 本组文件不导入它们.
>
> **判决: PARTIAL.** 构造与第一条引理成立 (定理); 第二条 (同一坐标两个证据下的重放) 是**否定** (编译过的反例), 方向与证据无关是定理; 带证据的种类上事件表是一个种类结构 (`KS`); 一级回灌的格链写出来了, `κ₂` 的坐标类型上含新种类节点的格有界 (与 `ChainZNeg.no-Ω-cell` 对照); 外层界沿 `⊞` 长高时重放不变 (条件: 合法证明相干, 且增量的合法数据在自环上给 `hself`). **没有折叠, 没有值定理, 强度没有提高.** 第一个没过的地方: 外层界长高后, 旧世界里的高度改贴新种类时的合法性 (判断, 见 §3).

## §1 构造 (交付 a)

- **世界**: 外层 $(w, b)$ 固定时, 世界是事件表 `EvT.Hist` (事件 = 坐标, 在 $b$ 之下的证据, `HB (Lev c₀)` 的合法增量). 下标是表的位置. ([EvWBase](EvWBase.lagda.md) §2.)
- **界**: `Rp.rp H c p` 由重放算出: 对每个事件 `cmpS p p₀` (`cmpB` 加 `toLt`), 在上者 (含相等) 接 `emb⊲ q δ`, 严格在下者不动.
- **种类结构** `EvKS.evKS`: 种类是带证据的坐标 $(c, p)$, 坐标类型 `HB (Lev c)`, 世界是事件表, 序是 "前面加事件", 比较是 `cmpB`. 内层世界取固定的合法族.
- **格链** `EvWFeed.Feed`: 在一个种类 $(c_0,p_0)$ 上逐格加事件, 增量由读回参数给出; 格链的 ℕ-极限合法.
- **长高** `EvWBase.Wk⊞`, `EvWGrow.Grow`, `EvWGrow.GrowKS`: 外层界 $b\mapsto b\boxplus\delta$, 事件证据接 `⊞-fst`, 新界合法证明取 `Lg-⊞`.

## §2 关于它的定理与否定 (交付 b)

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `rp-mono`, `rp-suf` | EvWBase | 加事件只增界 (字面第一位置, 任意内层世界) | 定理 |
| `new-self` | EvWBase | 新事件证据字面 `hself`: 新界 = 旧界 ⊞ δ (`refl`) | 定理 |
| `new-gen` | EvWBase | 一般证据: 新界 = 旧界 ⊞ (δ 沿某个自环 $c_0\equiv c_0$ 的搬运) | 定理 |
| `rp-below`, `rp-above` | EvWBase | 严格在下不动; 在上接 `emb⊲ q δ` (某条 $q$) | 定理 |
| `Lg-rp` | EvWBase | 重放的界合法 | 定理 |
| `dir-indep` | EvWBase | 是否累加只看坐标, 与证据无关 | 定理 |
| `wk-suc`, `wk-⊞` | EvWBase | 外层界接不含 $\Omega$ 的增量 (合法证明相干), 重放不变 | 定理 |
| `evKS` | EvWBase | 带证据的种类上事件表是 `KS` | 构造 |
| `no-indep` | EvWNeg | 同一坐标两个证据下的界相等或互为第一位置: 否 | 否定 |
| `no-cmp∃` | EvWNeg | 不带证据的种类 (界取 "存在证据") 上没有比较 | 否定 |
| `no-lb-indep`, `no-wk` | EvWNeg | 重放依赖外层界的合法证明; 外层长高而合法证明不相干时重放可以不可比 | 否定 |
| `cell-bd`, `cell-later`, `cell-step`, `cell-faith`, `Lg-lim`, `low-fixed` | EvWFeed | 格链: 有界, 之后一直有界, 单调, 忠实 (沿自环), 极限合法, 严格在下的坐标的一切证据拷贝不动 | 定理 |
| `new-cell`, `inst-new` | EvWFeed | 后继坐标 $\mathrm{hs}\,y$, 读回取 `Ωtop (Lev y)`: 每一格含新种类节点且有界 | 定理 |
| `same-type`, `contrast` | EvWFeed | `κ₂` 的坐标类型 = 坐标 `hs hz` 的槽; `growL′` 可达世界里 当前界 ⊞ `Ωtop S₀` 不有界, 事件世界里有界 | 定理 (两个不同种类结构上的两条) |
| `cmpF-self`, `cmpB-⊞Ω`, `wk-⊞Ω` | EvWGrow | 外层界接含 $\Omega$ 的增量, 在 `RL` (自环给 `hself`) 下重放不变 | 定理 |
| `bd→`, `bd←` | EvWGrow | 长高前后两个事件世界之间, 界双向相同 | 定理 |

**前提实例.** `EvWNeg`: `la₀`, `lbΩ`, `lbΩ′`, `lΩz`, `lv₀`, 证据 `p₁`, `p₂`, `pz` 都是闭项. `EvWFeed`: `inst-K2` (外层 `azero`, 界 `hs hz`), `inst-new` (一切合法 $y$, 证据 `hself`, 空事件表). `EvWGrow`: `RL` 对 `Ωz`, `ΩA` 成立 (`rΩz`, `rΩA`), `inst` 给出 $0\boxplus\Omega_A$ 的实例.

## §3 第一个障碍 (判断)

根子 (判断): 本组的种类带证据 $(c,p)$, 证据相对外层界 $b$, 所以种类依赖外层界; 外层界一长, 种类就要换一套. 方向 A 的接口 (`AdmWIf`, 未复核) 取了另一边: 种类不带证据 ("种类出现在高度的结点里, 不能依赖世界"), 于是碰到拷贝墙. 本组的 `no-cmp∃` 说种类不带证据时比较不存在, 与这一边一致; 本组没有碰拷贝墙, 代价是下面这一条.

外层界长高后 (`GrowKS`), 旧事件世界 $K_0$ 的种类 $(c,p)$ 对应新世界 $K_1$ 的 $(c,\mathrm{wk}\,p)$, 界双向相同 (定理). 但 $K_0$ 上的合法高度改贴 $K_1$ 的种类后, 它的 $\Omega$-节点要对 $K_1$ 的**一切**世界给单调数据, 而 $K_1$ 的世界不都是 $K_0$ 世界的像 (新事件可以落在只在 $b\boxplus\delta$ 之下的坐标上). `step` 的 `up` 之所以保合法, 是旧种类的界只看旧世界分量; 这里旧种类的界经重放与一切事件 (含新坐标的事件) 相关. 没有写成定理. 其次: 外层的 `A`-世界也长时还要两条相干条件 (`EvWGrow` 文件头); 内层世界族固定, 槽内部的界不由事件驱动.

## §4 导入

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvW where

open import OCF.Align.EvWBase public
open import OCF.Align.EvWNeg
open import OCF.Align.EvWFeed
open import OCF.Align.EvWGrow
```
