# 分层的 $\approx$: `limᴼ` 作低层 (判决: `limᴼ` LOW ONLY; 到 `HS` 的桥 BLOCKED)

> 接 [LevelK](LevelK.lagda.md) 写着 "没有做的第二个设计" 那一段. 底座 [LvStratBase](LvStratBase.lagda.md), [LvStratEq](LvStratEq.lagda.md), [LvStratObs](LvStratObs.lagda.md), [LvStratOrd](LvStratOrd.lagda.md), [LvStratGood](LvStratGood.lagda.md), [LvStratClose](LvStratClose.lagda.md), [LvStratFin](LvStratFin.lagda.md), [LvStratLvP](LvStratLvP.lagda.md), [LvStratTr](LvStratTr.lagda.md), [LvStratTower](LvStratTower.lagda.md), [LvStratUnion](LvStratUnion.lagda.md), [LvStratOmega](LvStratOmega.lagda.md), [LvStratChain](LvStratChain.lagda.md), [LvStratNeg](LvStratNeg.lagda.md), [LvStratY](LvStratY.lagda.md); 并排陈述 [LvStratCoexist](LvStratCoexist.lagda.md). 全部不含记号.
>
> **判决: `limᴼ` LOW ONLY. 目标 $\Omega_1+1$, $\Omega_1\cdot2$ 的层号证书是闭的定理, 对任何 `S`. $\psi_0(\Omega_{\Omega_2})$ 与 $x_3$ 的 `HS` **没有达到**, 这个设计给不出: 第一个障碍是目标 0, 理由是编译过的 (`¬mono-0`, `self-bound`, `floor-y→WLPO`, `CV-y→WLPO`). EBO 没有定义出来. 这里只有层号的证书, 不说任何强度.**
>
> **设计 (任务 1), 与 [LevelK](LevelK.lagda.md) 的草图有一处不同.** 草图说 "上一阶段的 $\approx$ 作参数". 实际不要: `b≈` 的分支用来回搬运的存在式 (Aczel 式, `toLv x ≈ toLv x′` 与 `g x ≈ g′ x′` 都在正的位置), 一个关系, 严格正, 没有阶段参数. 草图里参数要解决的 `≈-refl` 的停机问题由保留字面的 `o≈` 解决. 地板对上一阶段的依赖还在: 新地板的定义读上一阶段的 $\approx$.
>
> **编译过的定理 (无条件).**
>
> 1. **$\approx$ 与传递性 (`LvStratBase`).** `≈ᴮ-refl`, `≈ᴮ-sym`, `≈ᴮ-trans`, `path≈`, `≈⊑`, `wf≈`, `rp≈`, `mn≈`, `lo≈`, `Ωlv`, 都含 `b≈`.
> 2. **搬运只在地板上 (`LvStratBase.tr`, `LvStratTr`).** `tr`, `res` 是对两个层号的结构递归, 不读证据, 对原始的树是总函数 (头不合给 0). 规格只对地板: `resOK`, `trOK`. 它们只用上一阶段的 `tr-A` 与 `Rp`.
> 3. **闭包, 与阶段无关 (`Good-ψ`, `ψ≃`, `wf`, `Cert-top`, `K-stage.Cert`, `Cert∀`, `Cert∀ₙ`).** 对任何 `Stage`, 没有对阶段的递归. `Stage` 去掉 `low-≈`, `low-noo`, 换成 `low≈`, `tr-A`, `low-cx`, `twA`. 代价是树的可容许性 `Tw`, 与 "折叠的输出含低层" 改成对 `Eq` 递归 (`ZpΨ`).
> 4. **加一层 (`Next`), 任何并 (`UnionG`).** 新层 `new` 可以含 `limᴼ`, 新的低层是 $\approx$ `new` 的全部层号, `tr-A′` 就是它们之间的地板封闭.
> 5. **闭实例 (任务 2, `LvStratOmega`).** `TopΩ.Cert-Ω₊`: $\psi_{\Omega_1+1}(\Omega_{\Omega_1+2})$. `TopΩ2.Cert-Ω·2`: $\psi_{\Omega_1\cdot2}(\Omega_{\Omega_1\cdot2+1})$. 低层含 $\Omega_1=$ `limᴼ 0 toLv` 与全部 $\Omega_1+n$. 第 0 层的世界是 $\omega$, 第 1 层是 $\psi_1(1)+1$, 其余 $\Omega_{\ldots}+1$. **这是最小的世界**, 第 0 层的地板只有自然数.
> 6. **新的 $\approx$ 真的用到 (`both-low`, `copy-sim`, `copy-lv`).** $\Omega_1$ 与 $\Omega_1'$ 同时低, 不字面相同; $\Omega_{\Omega_1+1}$ 与 $\Omega_{\Omega_1'+1}$ 相似, 层号 $\approx$. 旧的 `o≈` 写不出这个.
> 7. **`¬both-low` 不再适用, 新旧并排 (`LvStratCoexist.Both`).** **改变的前提恰好一个: `Stage` 没有 `low-≈`** (`low-noo` 同时去掉, 对应 `¬lowΩ₁`). `old-¬both` 的前提 `low-≈` 在 $T_0$ 上是假的 (`new-¬low-≈`), 所以不矛盾.
> 8. **到 `Family` 的桥, 只有等价 (`Bridge.T-from`, 与 `Must.must`, `must-step`).** $\psi_0(\Omega_{\Omega_k})$ 的 `HS` 等价于目标 0 上那一族. 这一族没有证.
>
> **条件定理.**
>
> - `Chain.WithHE`: 目标 $K$ 的链上每一点好, 层号好. **条件于 `he`** (`S` 在链点层号上正确).
> - `ChainL.WithHE`: 任何 `BL` 的好目标 $L$ 的链 (目标 $\Omega_1$ 是 $x_3$ 的第一条链). **条件于 `oks`, `he`**. 没有证明这两个前提可满足. `only-floor`: 它们只问地板的路径.
> - `Stage` 的字段都是参数: 用 `Cert-top` 的陈述对具体阶段才是定理. 闭的阶段只有 `LvStratOmega` 的那些.
>
> **编译过的否定.**
>
> - `¬mono-0`, `lv⊑`, `cx-y`: **第一个障碍.** 第 1 层的树 $y$, 层号好, 地板含 2. $y'=g_3\,2$ 满足 $y'\sqsubseteq^A y$, 而 $\psi_0(y')\not\sqsubseteq^A\psi_0(y)$: 目标 0 上节点上升, 链卡在 1 (`ch-stuck`), 看不到地板元 2. 所以 `limᵢ-r₀`, `suc-path`, `Ω-path`, `mono-lv` 在目标 0 上是假的, 这不是 `¬Zt₀` 的技术限制.
> - `self-bound`: 第 0 层节点的链都低于 $L_0$, 输出就 $\sqsubseteq^A L_0$. `¬X∈A₀`: 闭实例的第 0 层地板不含任何 $\psi_0(\Omega_a)$. 世界的 `Cx` 在 `Next` 里是前提, 所以阶段的次序在目标 0 上是倒的.
> - `floor-y→WLPO`: 第 0 层地板含全部 `y s` ([LvIRNeg](LvIRNeg.lagda.md) 的反例族) 与 $\omega+1$, 就是 WLPO, 对任何 `Stage`. `¬y∈A₀`: 闭实例的地板不含它们. `CV-y→WLPO`: 判决在全部 $(y_s,\omega+1)$ 上正确就是 WLPO, 这是 `ask` 的站点.
> - `¬CV-copy`, `cv-ω′→ext`: `CV` 的穿透是字面的. 副本对目标没有正确的判决 ($\Omega_1'$: 矛盾; $\omega'$: 给外延性的实例). **这是分层的代价**: 第 0 层的世界比 $\omega$ 大时, `ask` 的站点上 `CV` 不够宽.
> - `no-Ω₂′`: 第 1 层分支全称, `LvG (toLv Ω₂)` 就推出 WLPO. `¬Reg-floor`: 地板不能同时含 $\omega_0+1$, $\omega_1+1$.
>
> **`S` 在哪里被问 (任务 4).**
>
> | 东西 | 问 `S` 吗 | 只问地板吗 |
> |---|---|---|
> | 地板的定义 | 不问 (`w₀-free`, 世界由 `Ω` 算) | |
> | `Cert-Ω₊`, `Cert-Ω·2` | 不问: 对任何 `S`, 模式是字面的 (`lit` 同分支, `okB`) | |
> | `Cert-top`, `Cert` 的陈述 | 由前提 `OK`, `LvP` 问 | 输入层号 `Lo` 时是 (`lo-adm`), 否则高层的分支全称 |
> | `Chain.WithHE` | `he` | 是 (`lo-y` 同形) |
> | `ChainL.WithHE` | `oks`, `he`, 每个节点都问 | 是 (`only-floor`) |
> | $\psi_0(\Omega_{\Omega_2})$ | 字面地含目标 $\omega+1$ (`LvIRReach.hard`, `ask`) | 这个设计里没有达到, `CV-y→WLPO` 限制它 |
>
> 对任何 `S` 成立的结果都只是**合法性**: `S` 不正确时闭项也有定义, 值不对, 这里不说值.
>
> **壁垒对照 (任务 5).**
>
> | 地板 | 上界 | 比较来源 | `Reg`, `y s` | 可判定成员吗 |
> |---|---|---|---|---|
> | 第 0 层 | $\omega$ | 这个 $L$ 的 `<-decᴬ` | 不含 `y s` (`¬y∈A₀`) | 不要: 折叠不读 `A` |
> | 第 1 层 | $\psi_1(1)+1$ | 同上 | 高层不适用 | 不要 |
> | 第 $k\ge2$ 层 | $\Omega_k+1$ | 同上 | | 不要 |
> | $\Omega_1$ 及其副本 | $\Omega_{\Omega_1}+1$ | 同上, 只比同一个字面层上的元 | | 不要 |
> | $\Omega_1+n+1$ 及其副本 | $\Omega_{\Omega_1+n+1}+1$ | 同上 | | 不要 |
>
> `bounded`: 新地板元都严格低于 $L$, 不是 `Ordᴰ` 的精确初始段, [Barrier](../Barrier.lagda.md) 的前提不成立 (判断, 形式对比没有编译). 全局三歧, 全分支比较都不要. **搬运带来新的比较义务吗: 没有.** `cmpA` 只用在 `A-dir`, `GenΩ.cxΩs`, `Next.cmp′`, `UnionG.cmp∞`, `¬Reg-floor`, `floor-y→WLPO`; `<-decᴬ` 只用在 `Next.cmp′` 与没有使用者的 `K-stage.cmp` (grep 检查, 语法级). `tr`, `res`, `resOK`, `trOK`, `b≈` 只用 `Rp` 与 `tr-A`, 不比较, `tr` 只看层号的头 (判断: 这是读定义, 语法检查). 搬运带来的是**判决的义务** (`¬CV-copy`), 不是比较的义务.
>
> **第一个障碍, 精确位置 (任务 3).** `Cert∀` 差的不止 "目标 0 上节点上升, 链点在 `Bs` 里". 三件事, 都编译了:
>
> 1. **序.** `mono-lv` 经地板元走, 目标 0 上是假的 (`¬mono-0`). `Good-ψ` 的上升支要 `hm`, `hm` 要跨链的 $\Omega$ 单调. 观测前序到目标 0 时, 右规则必须带边条件 "地板元低于链" (判断: 这就是 [UniformLv](UniformLv.lagda.md) 的 `Goodᴺ` 的 `gc`, "界不高于第 0 个链点").
> 2. **地板.** 第 0 层有界的地板要先框住输出 (`self-bound`), 无界的地板含 `y s` (`floor-y→WLPO`, `CV-y→WLPO`). 两难.
> 3. **目标.** $\psi_0(\Omega_{\Omega_2})$ 里有目标 $\omega+1$ (`LvIRReach`), 所以第 0 层世界比 $\omega$ 大的塔绕不开, 而那里字面的 `CV` 不够宽 (`cv-ω′→ext`).
>
> **没有做 (如实).** 第 0 层世界大于 $\omega$ 的塔: 低层要先含世界的全部前驱, 要沿世界的树造塔, 没有写. 所以副本只在 $\Omega_1$ 的层上有闭的实例, 自然数以外的可数层没有. `CV` 的非字面穿透没有写 (判断: 改动在 `limᵢ-r`, `ΩB`, `ψ≃`, `Good-ψ`, 约 100 行, 不越过障碍 1). 目标 0 的第二个设计没有写: 障碍 1 的边条件要树带界, 这是 `LvKey*`, `LvCert*` 那一路的形状, 我判断在这个层号证书的框架里补不上, 没有投入.
>
> **有限测试.** 没有. **判断** 都标明了. 全文 `--safe --without-K` (`LvStratBase`, `LvStratEq`, `LvStratTr`, `LvStratChain` 加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStrat where

open import OCF.Align.LvStratBase using (tr; res; Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LvStratTr using (module TrSpec)
open import OCF.Align.LvStratFin using (IsK; module Fin)
open import OCF.Align.LvStratLvP using (module LvPs)
open import OCF.Align.LvStratTower using (St₀; NewLevel; World; module Next; module Step; module Worlds; tower; canon)
open import OCF.Align.LvStratUnion using (module UnionG)
open import OCF.Align.LvStratOmega using (module GenΩ; module Closed; module Base; module NextS; module TopΩ; module TopΩ2; w₀-free)
open import OCF.Align.LvStratChain using (module AtK; Cert∀; Cert∀ₙ; module Chain; module ChainL; module Bridge)
open import OCF.Align.LvStratNeg using (module Copy; module Mono0; module Floor0; module SelfBound; module NegK; ¬Reg-floor; bounded)
open import OCF.Align.LvStratY using (floor-y→WLPO; module InClosed; module Site)
open import OCF.Align.LvStratCoexist using (module Both)
```
