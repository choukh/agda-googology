# 值验收: 层号去头不改值, $\psi_1(1)\cdot n$ 与 $\psi_1(2)$

> **判决 (编译过, `--safe --without-K --lossy-unification`): PARTIAL.** $\dot\Omega_n(\mathrm{lv}\,y)$ 与 $\dot\Omega_n(\mathrm{lv}\,y')$ 的比较做完了 (`V-≃`). 主线的行对 $\preccurlyeq$ 的值验收 (`VV`) 到: 码 $\omega\cdot2$ 的一切可数行, 码 $\omega^2$ 里位置 $\omega\cdot(i+2)$ 的一切可数行, 以及**无条件的** $\psi_0(\Omega_{\psi_1(2)})$. $\omega^\omega$, $\varepsilon_0$, `T⊤` 未走通 (暂停, 没有否定).
>
> 这是验收文件. 带 `OZ`, `LZ`, `B` 的模块与 `NF`, `Top`, `Inst*`, `Stop` 读记号; 树, 折叠, 证书没有改动, 也不依赖标签.
>
> ## 编译过的定理
>
> | 定理 | 陈述 | 文件 | 档 |
> | --- | --- | --- | --- |
> | `V-≃` | 对一切 `HtB`: $a\simeq b\Rightarrow V_ma\approx^{\mathsf v}V_mb$ | [EmbVVMain](EmbVVMain.lagda.md) | 定理, 不读记号 |
> | `succ-gap` | $\mathrm{suc}\,\omega\simeq\mathrm{suc}\,\omega^+$, 两向都不 $\sqsubseteq^{\mathsf I}$ | [EmbVVGap](EmbVVGap.lagda.md) | 定理, 不读记号 |
> | `force≃`, `Hd→≈ᵛ`, `Hd-lvl` | 去头相关的 `Z` 计值 `Hd⁰` 相关; `Hd⁰` 推同值, 推层号 $\simeq$ | [EmbVVForce](EmbVVForce.lagda.md) | 定理, 不读记号 |
> | `simᴴ` | 对一切 `HtB`, 开关 `dr`: $\alpha\simeq\alpha'$ $\Rightarrow$ 主线的行与去头的行 `≈ᴴ` | [EmbVVSame](EmbVVSame.lagda.md), [EmbVVSim](EmbVVSim.lagda.md) | 定理, 不读记号 |
> | `Y-val` | 主线的行与参照树的计值同值, 右边的证书任给 | [EmbVVMain](EmbVVMain.lagda.md) | 定理, 不读记号 |
> | `NF-ψ⁺` | $\theta$ 标准, 可数, $<\psi_0(\Omega_{\psi_1(1)\cdot(k+2)+\Omega\cdot(m+1)})$ $\Rightarrow$ $\psi_0(\Omega_{\psi_1(1)\cdot(k+2)+\Omega\cdot m+\theta})$ 是 `NF₁` | [EmbVVNF](EmbVVNF.lagda.md) | 定理, 读记号 |
> | `vv-M₂`, `vv-M₂-1` | 码 $\omega\cdot2$ 第 $\alpha$ 行, $\psi_0(\Omega_{\psi_1(1)\cdot2+\theta})$; $\alpha=1$ | [EmbVVInstM2](EmbVVInstM2.lagda.md) | 值验收 |
> | `vv-E`, `vv-E₀`, `vv-E-1` | 码 $\omega^2$ 的位置 $\omega\cdot(i+2)$, 对一切 $i$: 第 $\alpha$ 行, $\psi_0(\Omega_{\psi_1(1)\cdot(i+2)+\theta})$; $\alpha=0$; $\alpha=1$ | [EmbVVInstO2](EmbVVInstO2.lagda.md) | 值验收 |
> | `vv-ω²`, `vv-ω²-via` | `VV` ($V_{\mathrm{end}}0$) $\psi_0(\Omega_{\psi_1(2)})$; 后者就是 `vv-ω²-if` 的前提实例 | 同上 | 值验收, 无条件 |
> | `no-Sb-ψ²`, `no-NF-ψ²` | 这一版 `Sb` 没有 $\psi_1(2)$, $\psi_0(\Omega_{\psi_1(2)})$ 不是这一版的 `NF₁` | [EmbVVStop](EmbVVStop.lagda.md) | 定理, 不否定路线 |
>
> **条件定理.** `vv-row` ([EmbVVTop](EmbVVTop.lagda.md)): 对一切 `HtB`, 开关, 前缀结构 `PxB`: 只要 `NF₁` $\psi_0(\Omega_{P_m\theta})$ 和 $\alpha\simeq$ `toLevel Y`, 就有 `VV`. 前提 `PxB` 和 `NF₁` 现在只对上面的实例给出.
>
> **有限测试 (不是证明).** `shift-0`, `shift-1`, `shift-2`: `refl`, 比较器是 `fsn` 的字面计算, 只算 3 项. 盲区: 只说基本列, 不说码的位置.
>
> **判断 (没有编译).**
>
> - `Hd` 与 `BTBOVal` 的 `Le` 不是同一件事. `Le` 单向, 嵌入 $E$ 要给出来. 闭包节点的层号由上一步计值喂回, 两个独立的单向推导拼不回链上层号的精确嵌入, 要判断极限点 (`lim⁻`, `suc⁻` 那样的前提). `Hd` 对称, 按位置模拟, 直接交出层号的 $\simeq$ (`Hd-lvl`), 喂回就走得通. 所以选 `Hd`, 由 `CrossMSim` 机械改写得到. 主线版 `Le`, 也包括 `BTBOFullEmb` 的 `PEmb`, 都没有写. 这是取舍, 不是否定它们.
> - $\simeq$ 不确定 ($\omega\sim\omega^+$), 字面的 `lt-pres` 不成立, 但分派不会只因值相同而分叉 (`clash≃`, `clash≃′`).
> - `ω·n` 的定理是码 $\omega^2$ 内的位置, 它的层号值判断是 $\omega\cdot(i+2)$. 自己的码 `ω·ᶜ k` 只做了 $k=1$. $k\ge2$ 没做, 也不算在结论里.
>
> **第一个障碍 ($\omega^\omega$, $\varepsilon_0$, `T⊤`), 都还没试到底, 只写暂停.**
>
> 1. $\psi_1(2)$ 以上要新的 `Sb` 族. 报错原文:
>
>    `[] != OCF.Align.EBO.PT.ψ [] [] ∷ OCF.Align.EBO.natT 0 of type Data.List.List OCF.Align.EBO.PT when checking that the inferred type of an application Sb (ψ¹ ∷ OCF.Align.EmbVVLZStandardOmega.Ωᵐ 0 _c_1) matches the expected type Sb (ψ² ∷ [])`
>
>    对自然数下标的和判断是机械的: `sψ⁺` 换成一般的词, 13 处叶子都有对应. $\psi_1(a)$, $a$ 含 $\Omega$-可见参数时不机械: `visψ¹` 那种 "可见参数都是 $0$" 不再成立, 要真的用 `Bnd₁`. `T⊤` 的 $\psi_1(\gamma_n)$ 就是这种.
>
> 2. `ω^ωᶜ` 的块长不一样, 块末的行与基本列错开 2 位 (判断, `shift-*` 只验基本列一半), `≃ᴵ` 与 `HdM` 只有 0 或 1 位. 要加一种开关和一个 `≃ᴵ` 构造子, 判断是小改动.
>
> 3. $\varepsilon_0$ 和 `T⊤` 的码 (`expω`, $\lceil\mathrm{lv}\,T_n\rceil$) 要一条一般的 "码的读法", 现在的 `PxB` 是逐码手写的, 对一般的码还没有.
>
> ## 不是证书克隆, 但有克隆
>
> `EmbVVTree` 是树的克隆, 只加开关 `dr`. 它没有 `Goodᴺ` 闭包定理, 计值来自标签类的 `Goodᴸ`, 那读记号. 标签世界克隆了 28 个模块 (`EmbVVOZ*`, 5989 行), 外加 `EmbVVB*`, `EmbVVLZ*`, `EmbVVForget`; 全由脚本生成. 手写 1505 行.
>
> ## 审计
>
> - `importclosure.py`: `LadderOrd`, `LadderOrdMain`, `CrossM`, `CrossMClosed`, `EmbVVEq`, `EmbVVForce`, `EmbVVGap`, `EmbVVMode`, `EmbVVTree`, `EmbVVSim`, `EmbVVSame`, `EmbVVMain` 退出码 0. 正对照 `EmbVVTop`, `EmbVVInstM2`, `EmbVVInstO2` 退出码 1.
> - `depslice.py` (到达块, 记号块, 词命中): `LadderOrdMain:GᴺTᵠ` 1023, 0, 0; `CrossMClosed:T⊤` 1193, 0, 0; `EmbVVForce:force≃` 54, 0, 0; `EmbVVSame:simᴴ` 350, 0, 0; `EmbVVMain:V-≃` 1163, 0, 0; `EmbVVMain:Y-val` 1262, 0, 0. 正对照 `EmbVVInstM2:vv-M₂-1` 2821, 78, 389; `EmbVVInstO2:vv-ω²` 4749, 78, 688. 切片是语法级的.
> - 生成脚本 `Survey/scripts/embvv/` (`mk_sim.py`, `mk_world.py`, `mk_nf.py`) 重跑, 50 个 `EmbVV*` 文件逐字节不变.
>
> ## 导航
>
> | 文件 | 内容 |
> | --- | --- |
> | [EmbVVEq](EmbVVEq.lagda.md) | $\simeq^{\mathsf I}$, $\simeq^{\mathsf z}$, 去头的搬运 |
> | [EmbVVForce](EmbVVForce.lagda.md) | `Hd⁰`, `force≃` |
> | [EmbVVGap](EmbVVGap.lagda.md) | `succ-gap` |
> | [EmbVVMode](EmbVVMode.lagda.md), [EmbVVTree](EmbVVTree.lagda.md) | 开关, 去头的树 |
> | [EmbVVSim](EmbVVSim.lagda.md), [EmbVVSame](EmbVVSame.lagda.md) | 主线与去头的树的模拟 |
> | [EmbVVMain](EmbVVMain.lagda.md) | `V-≃`, `Y-val` |
> | `EmbVVLZStandardOmega`, `EmbVVLZExtra`, [EmbVVNF](EmbVVNF.lagda.md) | 扩展的 `Sb`, `NF₁`, `NF-ψ⁺` |
> | `EmbVVOZ*`, `EmbVVB*`, `EmbVVForget`, [EmbVVTop](EmbVVTop.lagda.md) | 标签世界, `vv-row` |
> | [EmbVVInstM2](EmbVVInstM2.lagda.md), [EmbVVInstO2](EmbVVInstO2.lagda.md) | 实例 |
> | [EmbVVStop](EmbVVStop.lagda.md) | 这一版停在哪 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVV where

open import OCF.Align.EmbVVEq public using (_≃ᴵ_; _≃ᶻ_)
open import OCF.Align.EmbVVForce public using (Hd⁰; Hd-lvl; Hd→≈ᵛ; force≃)
open import OCF.Align.EmbVVGap public using (succ-gap)
open import OCF.Align.EmbVVMode public using (HdM)
import OCF.Align.EmbVVMain
import OCF.Align.EmbVVSim
import OCF.Align.EmbVVSame
open import OCF.Align.EmbVVNF public using (NF-ψ⁺)
import OCF.Align.EmbVVTop
open import OCF.Align.EmbVVInstM2 public using (Px-M₂; vv-M₂; vv-M₂-1)
open import OCF.Align.EmbVVInstO2 public using (Px-ω²; vv-E; vv-E₀; vv-E-1; vv-ω²; vv-ω²-via)
open import OCF.Align.EmbVVStop public using (no-Sb-ψ²; no-NF-ψ²; shift-0; shift-1; shift-2)
```
