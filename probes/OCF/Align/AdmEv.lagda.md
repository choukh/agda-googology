# 与 B 合流: 种类带证据, 比较取 `cmpB₀` (入口与判决)

> 不含记号. 作者选定的方向原话: "与 B 合流: 种类带证据". 配合 [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2, §2.4, §5.2. 本组把方向 B ([EvW](EvW.lagda.md): 事件历史世界, 种类带证据 $(c,p)$) 的比较换成方向 A 的 [AdmWCmp](AdmWCmp.lagda.md) `cmpB₀` (对角上给 `hself` 的比较), 按 `EvW` §3 的接手清单逐条做. 不改任何已有文件; `EvT`, `Cm.contrib`, `emb⊲`, `cmpB₀` 原样导入.
>
> **判决: PARTIAL.** 清单第 1, 2, 3 条是定理 (第 3 条在写明的两条相干条件下, 其中一条是对世界数据的选择, 另一条有实例, 去掉它有编译过的反例). 第 4 条只写出了回灌的骨架 (读回作参数): 外层界随回灌长高, 每一站的高度合法 (要第 2 条的 `Lg-rl`). **没有写出 `RunM` 在 `evKS₀` 上的折叠, 没有序数值定理, 强度没有提高.**
>
> **对纲领与目标.** 这一步是摆脱侧: 它去掉 `EvW` 里两处来自比较方式的条件 (自环搬运, `RL`), 并把 `EvW` §3 判断为障碍的一条 (改贴种类后的合法性) 证成定理; 新加的定义 (`rest`, `rl`, `Stage`) 都由树侧的要求 (合法性, 字面公共上界) 写出, 不读记号. 它没有提供任何值判据, 所以对 "读法到 ψ₀Λ" 没有贡献 (判断).

## §1 定理表

| 名字 | 文件 | 陈述 (白话) | 档 |
|---|---|---|---|
| `new-gen₀` | AdmEvBase | 对一切证据 $p$, 在 $(c,p)$ 加事件后那里的界 = 旧界 ⊞ δ (命题相等, 无自环) | 定理 |
| `rp-mono`, `rp-suf`, `Lg-rp`, `rp-below`, `rp-above`, `dir-indep`, `evKS₀`, `bd-new` | AdmEvBase | `EvWBase` 的律在 `cmpB₀` 下照样成立; 加事件后新界字面有界 | 定理 / 构造 |
| `fac` | AdmEvGrow | 因子化: `cmpB₀ (p ⨾ ⊞-⊲ b σ) Y` = 先比 `cmpB₀ (⊞-⊲ b σ) Y`, 得 $c_0\lhd b$ 的 $r$ 时再比 `cmpB₀ p r` (旧界, 旧合法证明); 得 $b\lhd c_0$ 的 $s$ 时是 $p⨾s$. 对一切合法 ε, σ | 定理 |
| `diag-tr`, `inj₂-strict` | AdmEvGrow | `cmpB₀ X (p₀ ⨾ X) ≡ inj₁ p₀`; `inj₂` 结果严格 | 定理 |
| `cmp-wk`, `wk-⊞₀` | AdmEvGrow | 外层界接上**任意合法** δ (可含 Ω-节点), 弱化的证据之间比较不变, 重放不变. 去掉了 `EvWGrow.RL` | 定理 |
| `rest`, `rest-wm`, **`sim`** | AdmEvGrow | 新世界 $H$ 在一切旧种类上的读数 = 旧世界 `rest H` 的读数; `rest ∘ wm = id` | 构造 / 定理 |
| **`Lg-rl`**, `rl⊲`, `bd→`, `bd←` | AdmEvGrow | 旧事件世界上的合法高度改贴新种类 $(c,p)\mapsto(c,\mathrm{wk}\,p)$ 后在新事件世界上合法, 无附加条件 | 定理 |
| `lg⊲-tr`, `cmpF-tr` | AdmEvGrowA | 坐标证据接上 $q$: 坐标合法证明与 `cmpF` 都等于沿 `lg⊲ q la′` 的旧值 | 定理 |
| `cmp-↑`, `wk-A` | AdmEvGrowA | 外层 `A`-世界长高 $a\lhd a'$: 在 (C1) 旧合法证明 = `lg⊲ q la′` 与 (C2) `NatB` (界的 `st`, `mo` 对世界自然) 之下, 比较与长高交换, 重放不变 | 条件定理 (条件是树侧数据, 不是 Funext) |
| `nat-ΩA`, `inst-A` | AdmEvGrowA | (C2) 对 `EvWGrow.ΩA` 与一切 $q$ 成立; $a'=\mathrm{asuc}\,a$ 时 (C1) 定义地成立 | 定理 (前提实例) |
| `no-up-inv` | AdmEvGrowA | 只有 (C1): 对一切合法外层界, `A`-世界长高后重放与原来相等或可比 — 否 | 否定 |
| `no-indep₀` | AdmEvNeg | `cmpB₀` 下同一坐标两个证据的界仍可以不可比 (拷贝仍在, 种类仍须带证据) | 否定 |
| `not-image` | AdmEvNeg | 新事件世界不都是旧事件世界的像 (`EvW` §3 的前一半); 不妨碍 `Lg-rl` | 否定 |
| `cell-faith₀`, `cell-strict`, `Lg-lim` | AdmEvFeed | 外层界固定的格链: 新格字面 = 旧格 ⊞ 读回; 读回头部非零时严格增长; 极限合法 | 定理 (严格增长档, 不是强度) |
| `Tower.Run.tower`, `legal`, `b-strict`, `new-kind` | AdmEvFeed | 外层界随回灌长高的塔: 每一站高度合法 (由 `Lg-rl`), 外层界严格增长, 每站有不是旧种类之像的新种类 | 构造 / 定理 (严格增长档) |
| `Inst.T₃`, `inst-strict`, `inst-new` | AdmEvFeed | 闭项实例: $a=0$, 读回恒 $\mathrm{hs}\,0$ | 闭项 / 定理 |

**前提实例.** `Lg-rl`, `sim`, `wk-⊞₀`: 对一切合法 $a,b,\delta$ 与一切合法内层族, 无条件 (实例: `AdmEvFeed.Inst` 每一站都用到). `wk-A`: `nat-ΩA` 给 (C2), `inst-A` 给 (C1). `no-up-inv`: 外层界 `lbw` 合法 (闭项), 世界 $a_0=\lim_n 1$, 长到 $\mathrm{asuc}\,a_0$. `no-indep₀`: `EvWNeg` 的闭项. `not-image`: 一切头部非零的合法 δ.

## §2 第一个障碍

1. **清单第 1 条已过.** `new-gen₀`: 换比较后字面忠实, 对一切证据.
2. **清单第 2 条已过, 而且不是障碍.** `EvW` §3 的判断 "新世界不都是旧世界的像" 是对的 (`not-image`, 定理), 但合法性不需要像: 需要的是新世界在旧种类上的读数等于某个旧世界的读数 (`sim`). `sim` 的证明落在 `fac` 上: 新事件的证据在 $b\boxplus\delta$ 之下, 与旧种类的比较沿新界下降, 到 $b$ 时化成旧证据之间的比较; 这一步要 `cmpB₀` 在 Ω-结点坐标相同时不调用 δ 的单调数据. 换回 `cmpB` 时这里要 `RL` 一类条件 (判断, 依据 `EvWGrow.RL` 的来源; 没有写成否定).
3. **清单第 3 条: 两条条件都是真需要的一半.** (C2) 有编译过的反例说明不可省 (`no-up-inv`); (C1) 不可省的反例是 `EvWNeg.no-lb-indep` 的 `A`-世界版, 本轮没有写 (判断: 构造同形). 外层 `A`-世界长高后的**改贴**合法性 (第 2 条的 `A`-版) 没有做: 新 `A`-坐标进入证据后, 新事件与旧种类的比较不一定化回旧证据 (要比较的两个 `A`-坐标一个在 $a$ 之下, 一个只在 $a'$ 之下, `cmpF` 的结果经 `mo` 搬运, 不必是任何旧路径). 这是下一条要判定的引理 (判断).
4. **清单第 4 条: 第一个没过的地方是塔的 ℕ-极限** (判断). 各站的高度在不同的 $K_n$ 里; 合到极限界 $\mathrm{hl}\,b$ 之下要沿 `hlim n hself` 与 `stepsᴮ` 的复合改贴, `fac` 只对 `⊞-⊲ b σ` 形状的长高路径; 把 $b_m$ 写成 $b_n\boxplus(\cdots)$ 要 ⊞ 的结合律, 在 ℕ-极限处是逐点相等 (要函数外延才能变成相等). 其次是 `RunM` 本身: 它的数据树 (`HtTowerFTree`) 以 `A × H₀` 为世界, 搬到 `evKS₀` 上的工作没有做.

## §3 翻译账

- **来自记号的规则**: 无. 本组不读记号, 不导入记号模块 (审计见报告).
- **由树的要求逼出的**: `rest` (新世界在旧种类上的读数要等于某个旧世界, 才能用旧高度的单调数据; 比较用新界这个字面公共上界); `NatB` (界的合法数据是以世界为参数的数据, 世界长高时要相干, `no-up-inv` 说不可省); `Stage` 里带合法证明 (`EvWNeg.no-wk`: 合法证明是世界的数据).
- **来自 `RunM` 的形状** (此前已记账的翻译痕迹, `StallDiagnosis` §4 (i)): "读回给外层界一个增量, 低层搬回" 在 `Tower` 里保留 (读回作参数); "搬回" 在这里是 `rl` (改贴种类), 不是投影. 这一步让缺陷变浅还是变深: 判断, 变浅 (改贴是对一切合法高度的定理, 不按阶段定制).
- **新增脚手架**: `fac` 与它的路径代数 (`tr-assoc`, `⊞⊲-tr`, `⊞-steps`, `fst-⊲`), `inj₂-strict`; 是序数值需要的还是翻译带来的: 都是让 "比较在长高后不变" 成立的树侧引理, 与值无关 (判断).

## §4 导入

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEv where

open import OCF.Align.AdmEvBase public
open import OCF.Align.AdmEvGrow
open import OCF.Align.AdmEvGrowA
open import OCF.Align.AdmEvNeg
open import OCF.Align.AdmEvFeed
```
