# 带守卫的层号: 读回是定理, 树有定义, 界与证书还没有 (判决: PARTIAL)

> 底座 [LvGuardBase](LvGuardBase.lagda.md) (层号), [LvGuardUni](LvGuardUni.lagda.md) (读回的闭包定理), [LvGuardFeed](LvGuardFeed.lagda.md) (实例), [LvGuardNeg](LvGuardNeg.lagda.md) (否定), [LvGuardNext](LvGuardNext.lagda.md) (下一层), [LvGuardTab](LvGuardTab.lagda.md) (`kdec`), [LvGuardTree](LvGuardTree.lagda.md) (树), [LvGuardRead](LvGuardRead.lagda.md) (第二层读回). 都不用记号的定义. 记号只在验收 [LvGuardAccept](LvGuardAccept.lagda.md). 接 [ScafOmega2](ScafOmega2.lagda.md), [LvKey](LvKey.lagda.md), [LvCert](LvCert.lagda.md), [EBOTop](EBOTop.lagda.md).
>
> **判决: PARTIAL. 决定性检验通过: $F\,\theta=\psi_1(\Omega_\theta)$ 与 $\mathrm{Lv}_5=\psi_1(\Omega_\Omega)$ 读回成好层号, 对一切 $\theta:\mathsf{Ord}^\mathsf I$, 无条件 (`Cf-F`, `Cf-Lv₅`). 这棵新树对任何好层号有定义 (`T₀`), 所以 $\psi_0(\Omega_{\psi_1(\Omega)})$ 与第 5 站第一次是闭项, 种类检验通过. 但没有证书 (`Goodᴺ` 没有写), 界的问题只修了一半 (`c-bra*`), $\psi_0(\Omega_{\Omega_2})$ 的树没有写, `good-feed` 对层号下标只有定义. 所以不是 VIABLE. 没有编译过的否定挡住它, 所以也不是 FAILS.**
>
> **任务 1: 带守卫的层号 (编译).**
>
> - `lc c t g` ([LvGuardBase](LvGuardBase.lagda.md)): 第一支 $t$, 分支 $g\,\eta\,e$ 只在 $e:c\sqsubseteq\eta$ 上. 定义域 `Dom` 是参数. `Dom₀ = Ordᴵ`. `Up.NextDom 𝔻`: $D\uplus$ 上一层的好层号. `𝔻ₙ`, `Ωₙ`, `Cf-Ωₙ`: $\Omega_{n+1}$ 对一切 $n$ 是同一个定义 `Up.Ω⁺` 的实例, 没有标签, 没有表.
> - **比较 (`cmpF`, `cmpP`): 第一路径 (不走 `bra`) 对任意路径, 第一位置对任意路径, 没有世界.** 不用 `<ᴵ-dec`, 分支值从不被比较. `cmpW` ([LvGuardNext](LvGuardNext.lagda.md)): 分支 $x$ 自己就是局部上界, 这是 [ScafOmega2Family](ScafOmega2Family.lagda.md) 的 `cmpW` 在 `Ordᴵ` 之外的形式.
> - `WF` (弱, `⊴ʷ`, `⊑ⁿ`) 与 `WFˢ` (强, 带转移, 上升也是 `⊴`). 第二层 ($x\mapsto x$) 只有 `WF`: 那里 `⊴` 的上升是假的, `no-↑` 的形状.
>
> **不适用的理由, 逐条.**
>
> | 否定 | 状态 | 依据 |
> |---|---|---|
> | `no-read`, `no-read-GL` | **仍然成立, 在这个层号上也是** | `no-read-GLG` (编译): 好层号上的目标判决是 WLPO. `first-Ω`, `first-Ωˡ` (编译): 第一路径到不了分支, 所以 `cmpF` 不是这个判决. 守卫切开反例族: `G-exclᴸ` (编译), 不全排除: `G-y-inᴸ` (编译) |
> | `¬G-tri` | **仍然成立** | `¬Gᴸ-tri`, `Gᴸ-unbounded` (编译) |
> | `¬tri`, `noBT`, `dec→WLPO`, `Trich₂→WLPO` | **全分支比较仍是 WLPO** | `no-bra-cmp` (编译): $\Omega$ 上两条任意路径三歧推出 WLPO. `cmpF` 不是它的特例. 树用的 `bd` 只在表给出字面界的同一节点上. `kdec` 同 [LvKey](LvKey.lagda.md): 输入是证据 |
> | `dec-A→WLPO` | 不适用 (判断) | 没有成员判定: `Adm (cov π)` 是静态的, 证据缺失给 `o0`, 不判定 |
> | `self-bound` | 不适用 (判断) | 第 0 层没有地板. `oŝ c` 的 $c$ 先于链, 只要目标与同键的帧. 与 [ScafOmega2](ScafOmega2.lagda.md) 同理 |
> | `Toy.loop`, 壁垒 | 不撞 (判断, 没有形式对比) | `LG` 没有全局三歧 (`no-bra-cmp`), 不是 `Ordᴰ` 的精确初始段的形状 |
>
> **任务 2: 读回 (编译, 无条件).**
>
> - `F`, `Lv₅`, `WF-F`, `self-F`, `Cf-F`, `F-mono`, `WF-Lv₅`, `Cf-Lv₅` ([LvGuardUni](LvGuardUni.lagda.md)): 对一切 $\theta$, 对任何 `Dom`. 模块参数 `𝔻` 是定义域, 不是假设, 实例 `Dom₀`, `𝔻ₙ` 是闭的. `Fᵍ`, `Lv₅ᵍ` ([LvGuardFeed](LvGuardFeed.lagda.md)): 好层号.
> - **`base⊑zero` 由什么取代: 没有原子.** $\Omega$ 是真的闭包 (`Ωᴸ`, `Cf-Ωᴸ`), `¬Ω⊑zero`. `Good→WF₁` 是出口.
> - **闭包定理与底部的序无关.** [LvGuardUni](LvGuardUni.lagda.md) 是 [Uniform](Uniform.lagda.md) §0–§7 的脚本克隆, 只改底部: 用到 `≈→⊴`, `⊴-trans`, `⊴-lim-r`, `⊴-lim-l`, `⊴-suc-r`, `⊴-fst`, `⊴-zero` 七条. 这是这一轮最便宜也最重要的发现. **由证明的形状读出 (判断): `⊴` 的搬运从不改变分支值, 也不换节点.** 这解释了为什么全部表上的转移成立, 与 [LvKeyStep](LvKeyStep.lagda.md) 的 `no-↑` 不矛盾: `no-↑` 问的 $\Omega+3\sqsubseteq\Omega\cdot2$ 在读回的步进里不出现.
> - **对层号下标: 只有定义.** `F⁺` ([LvGuardRead](LvGuardRead.lagda.md)), `rbO`: `oŝ c t g` 读成 `lc c t g`. `F⁺` 的 `WF` 没有写: 要 [LvGuardUni](LvGuardUni.lagda.md) 在 `O` 上的版本. 判断: 不要 `dy`, 所以不碰 `noW`; 这是 `good-feed` 的剩余工作.
>
> **任务 3: 树 (编译, 定义).** `T₀ : (L : LG) → Cfˢ L → Z` ([LvGuardTree](LvGuardTree.lagda.md)), 对任何带证书的层号, 一个定义. 与 [LvKeyTree](LvKeyTree.lagda.md) 的差别: 层没有高度 (没有 `base`, `oi`, `oc₀`); 树里没有世界, 节点的可容许性是静态的 (`Adm (cov π)`); 折叠立刻计值 (没有 `oev`), 目标在闭包之下时闭包落成字面的 `oŝ`, 输出不带这个帧 (`cmpK`). 键仍是 `kdec` (`noTag` 排除 $\mathbb N$ 标签). 目标的 `at a`: **没有做, 见第一个障碍.**
>
> **任务 4: 目标 (有限测试, [LvGuardAccept](LvGuardAccept.lagda.md), 全部 `refl`).**
>
> | 目标 | 比较器, 深度, 宽度 | 结果 |
> |---|---|---|
> | $F\,\theta$ 对 $\psi_1(\Omega_\theta)$, $\theta=0,1,2,3$, 含字面分支 | `dfL`, `dfB`, 7–8, 2–3 | 一致, 对照 `ctl₁`, `ctl₂` 报告不一致 |
> | $\mathrm{Lv}_5$ 对 $\psi_1(\Omega_\Omega)$ | 同上, 6–7, 2 | 一致, 对照 `ctl₃` |
> | $\psi_0(\Omega_\Omega)$, $\Omega+1$, $\Omega\cdot2$, $\Omega\cdot2+1$, $\Omega\cdot3$ | `dfZ`, 10–12, 2 | 一致, 对照 `ctl₄` |
> | $\psi_0(\Omega_{\psi_1(1)})$, $\psi_0(\Omega_{\psi_1(\Omega)})$, **第 5 站** | `dfZ`, 10, 2 | 一致, 对照 `ctl₅`, `ctl₆` |
> | $\psi_1(\Omega_{\psi_1(\Omega)})$ (`F⁺`) | `dfL`, 6, 2 | 一致, 对照 `ctl₇` |
>
> 这些测试不看界, 闭包只走第 0 个孩子. **它们不说明有证书 (`noW`, `noCert₂`).** $\psi_0(\Omega_{\Omega_2})$ 没有测: 这棵树只在 `Dom₀` 上. 层号 $\Omega_2$ 有 (`Cf-Ωₙ`), 树没有.
>
> **界 (有限测试, 看界, `refl`).** `c-tight2`, `c-tight5`: $W=\dot\Omega_D$ 对紧的目标路径, 界是 2, 活的帧 $\tau$ 不进界. `c-bra2`, `c-bra3`, `c-bra5`: 同一个目标, 路径穿过分支 $\tau$ 时界是 $\tau+1$.
>
> **第一个障碍: `tight`.** [LvCert](LvCert.lagda.md) 的 `noW` 有两半. 第 3 步 "`ι (db τ)` 把 $\tau$ 加进保留的闭包" 这里没有了 (`c-tight*`, 闭包立刻计值). 但目标自己的路径穿过分支 $\tau$ 时, 界读到 $\tau$ (`c-bra*`). 目标 $L+a$ 从分支 $\tau$ 里的节点来, 路径是 `bra τ …`, 要的是最小的分支 $a+1$. 这是树上的第一个具体缺口. **我认为 $\psi_0(\Omega_{\Omega\cdot2+1})$ 在这棵树上因此没有证书 (判断, 没有移植 `noCert₂`: 否定是对旧树编译的).** 要的东西 (判断, 未编译):
>
> 1. 闭包要有 "最小分支" 的算法. 对 $g$ 不是黑箱时直接: 对 $\eta$ 递归. 对一般的 `lc`: `Str`: $g\,a\prec^f g(a+1)$ (由 `cmpF` 判断路径落在哪一支), `Cont`: $g(\lim)$ 的路径落在某个 $g(f\,n)$. 两条都不提分支值的比较.
> 2. 两条对读回成立 (判断): 在 `gi` 上加字段 `suc (f z) ⊑ᵒ f (suc z)` 与连续性, 所有 `Good-*` 重证. `suc (up z) ≅ up (suc z)` 使 `Ω` 的那一行平凡, 穿透行要 "$a+y$ 的第一路径含 $a$". 估计 300 行. 没有写.
>
> **第二个障碍: 证书.** `Goodᴺ` 没有写, 新树上一条正面的证书定理也没有, $\psi_0(\Omega_\Omega)$ 也没有. 所以 `noW` 之外还有什么挡路, 不知道. **第三个: 第二层的树.** 闭包在 `Dom₀` 之外时目标 $\le1$ 要的是第 1 层的待计值链, 要 `Z` 的第 1 层版本与 $\hat F$ 的 `WF`. 这要先做 `F⁺` 的 `WF`. 没有两个设计败在同一点: 只写了这一个设计.
>
> **任务 5: 判据.**
>
> - 逐阶段的输入: 层号 ($\Omega\cdot m$, $F$, $\mathrm{Lv}_5$, $\Omega_n$) 没有. 树没有 (`T₀` 一个定义). 闭包定理 ([LvGuardUni](LvGuardUni.lagda.md)) 没有, 对任何 `Dom`. 还要的是: 层号的 `Cfˢ`.
> - **$\Omega_{\Omega_\eta}$ 以上: 否.** `𝔻ₙ` 对 $n:\mathbb N$ 递归, 没有 $\eta:\mathsf{Ord}^\mathsf I$. 判断: `Lvl : Ordᴵ → Set` 仿 `Ord₊`/`U` 对 `◃` 证明递归写得出 (定义域 `U i r = Σ (Lvl i) (WF i)`, 隐式层号下降), 没有试. 再往上 (`Ω_Ω` 作层索引) 要下标是层号自己, 那是 `Λ` 的不动点, 判断要新的东西.
> - 读了记号的: 定义没有读. 但 `oŝ`, `Mlev`, `bound`, 第一支的形状沿用旧树, 当初是看记号定的. **树侧逼出的:** 守卫的 `lc` 读回 `oŝ`; 第一路径 (`first-Ω`, `no-bra-cmp`); 没有原子 (`¬Ω⊑zero`); 紧的界要目标自己 (`c-bra*`). 这一轮的设计是看 `noW` 的编译反例与 `ScafLadder` 的说明定的.
>
> **审计.** `depslice.py` (语法级): `LvGuardUni:WF-F`, `LvGuardUni:Cf-Lv₅`, `LvGuardFeed:Fᵍ`, `LvGuardNeg:no-bra-cmp`, `LvGuardNext:Cf-Ωₙ`, `LvGuardTab:kdec`, `LvGuardTree:T₀`, `LvGuardRead:F⁺` 到达的记号定义都是 0 (到达 65 到 233 个定义块). 正对照 `LvGuardAccept:c-tf5` 是 48, `c-F1` 是 47. `importclosure.py` (编译器保证): **`LvGuardBase`, `LvGuardUni`, `LvGuardFeed`, `LvGuardNext`, `LvGuardTab` 闭包干净 (退出码 0): 读回的定理的导入链到不了记号.** `LvGuardNeg` (经 `ScafOmega2Family`, `Symbolic`), `LvGuardTree`, `LvGuardRead` (经 `Uniform3Base`, `Prefix`, `Symbolic`, 为了 `bound`, `Mlev`, `Z`) 不干净, 退出码 1. 全文 `--safe --without-K` (`LvGuardBase`, `LvGuardTab`, `LvGuardTree`, `LvGuardRead`, `LvGuardAccept`, 本文加 `--lossy-unification`; `LvGuardUni` 不加), 无公设、无洞、无停机或正性编译指示. 模块参数 `𝔻` 不是假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvGuard where

open import OCF.Align.LvGuardBase using (Dom; Dom₀; module Lv)
open import OCF.Align.LvGuardUni using (F; Lv₅; Cf-F; Cf-Lv₅; F-mono)
open import OCF.Align.LvGuardFeed using (Fᵍ; Lv₅ᵍ; ¬Ω⊑zero; Cf-Ωᴸ; ofLᵍ)
open import OCF.Align.LvGuardNeg using (no-read-GLG; no-bra-cmp; first-Ω; first-Ωˡ; G-exclᴸ; G-y-inᴸ; ¬Gᴸ-tri; Gᴸ-unbounded)
open import OCF.Align.LvGuardNext using (𝔻ₙ; Ωₙ; Cf-Ωₙ; module Up)
open import OCF.Align.LvGuardTab using (kdec)
open import OCF.Align.LvGuardTree using (T; T₀; module Fold)
open import OCF.Align.LvGuardRead using (F⁺; rbO)
```
