# 累加树在 $\psi_0(\Omega_{\Omega+1})$ 的第 4 层: 判决 PARTIAL

> **验收文件.** 对象: [CumUpW](CumUpW.lagda.md) 的 `TΩ+1 = Tψ 1 one one g₀ C.self`. 目标 1 成立. 目标 2 **未走通**: 序数值验收的上界一条也没有, 下界只到 $\psi_0(\Omega_\Omega)$ 之上严格一步, 没有对照树 $\psi_0(\Omega_{\Omega+1})$ 第 1 项及以后的比较. 没有掉值或超值的见证, 也没有证明不掉不超. 这不是否定, 没有任何路线被关闭.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 切片脚本: `probes/Survey/scripts/om1cum/locslice_om1cum.py`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1Cum where

open import OCF.Align.Om1CumGrow using (T-strict; TΩ≺TΩ+1; step-Ω+1; ladder)
open import OCF.Align.Om1CumIdx using (_≼ᶜ_; ≼ᶜ→≼; V2ᶜ; no-V2; module Base; next-Eb; Fʸ-next)
import OCF.Align.Om1CumTest
```

## §1 定理

| 定理 | 陈述 | 文件 |
|---|---|---|
| `T-strict` | 对一切 `NL p a`, $\psi_0(\Omega_{\Omega\cdot p+a})\prec\psi_0(\Omega_{\Omega\cdot p+a+1})$ | [Om1CumGrow](Om1CumGrow.lagda.md) |
| `TΩ≺TΩ+1` | `TΩ ≺ TΩ+1` | 同上 |
| `step-Ω+1` | `suc BTBOᴵ ≼ fr TΩ+1`, `BTBOᴵ` 过基本列验收 | 同上 |
| `V2ᶜ` | $x\preccurlyeq^c y$ 则 `ordᴰ x` 的前驱保序映到 `ordᴰ y` 的前驱, 不要 `St` | [Om1CumIdx](Om1CumIdx.lagda.md) |
| `no-V2` | 只留 $\preccurlyeq$, 去掉 `St` 和结构序, 这个嵌入是假的 (常值极限) | 同上 |
| `Base.Eb-base`, `base-id` | 加法左边的下标上映射恒等 | 同上 |
| `Fʸ-next` | $x\preccurlyeq^c y$ 则 $\psi^0(\Omega_{\eta+x+1})\preccurlyeq\psi^0(\Omega_{\eta+y+1})$, 没有上下文 | 同上 |

## §2 账

**实测** (定义级切片, 口径同 `locslice_station.py`, 计 agda 非空非注释行, 不排除任何层).

| 路线 | 定义 | 加证书 | 加第 4 层 | 第 4 层净增 |
|---|---|---|---|---|
| 累加 `Tψ`, $\psi_0(\Omega_\Omega)$ (`TΩ≈`) | 393 | 2019 | 6283 | 4264 |
| 累加 `Tψ`, $\psi_0(\Omega_{\Omega+1})$ 严格下界 (`step-Ω+1`) | 393 | 2019 | 6382 | 4363 |
| 其中只有 `T-strict` | 393 | 2019 | 2107 | 88 |
| 不累加 `T⁰`, $\psi_0(\Omega_\Omega)$ | 829 | 997 | 4059 | 3062 |
| 不累加 `TΩᴺ`, $\psi_0(\Omega_\Omega)$ (定义依赖证书, 两列相同) | 1777 | 1777 | 5500 | 3723 |

- $\psi_0(\Omega_\Omega)$ 这一站, 累加的 4264 行与 `T⁰` 的 3062 行公共 3036 行 (主要是标签和对照树: `Standard`, `Level`, `Uniform`, `Bachmann`, `Label`). **只在累加这边的 1228 行就是这一站毛刺的实测**, 占净增 29%: `BTBOFullEb` 206, `BTBOFullV1` 167, `CumUpAcceptVal` 148, `CumValZ` 143, `BTBOFullV3` 99, `CumReadCF` 93, `BTBO` 81, 其余 291. 其中 `CumValZ`, `CumReadCF` 是桥, 把 `Tψ` 接回上一轮的树, 不全算累加本身的代价.
- $\psi_0(\Omega_{\Omega+1})$ 这一站到目前新增: `T-strict` 切片 88 行 (判断: 不是毛刺造成的, 只用第一位置); `Fʸ-next` 新块 73 行 (毛刺造成的). 文件代码行: `Om1CumGrow` 117, `Om1CumIdx` 118, `Om1CumTest` 43, 本文 5.
- 对照树 `GᴺΩ̇` 证书 4354 行, 加标签 `TΩ-label` 11865 行, 两条路线在这一站共用, 不算累加的账.

**估计, 不是实测** (标定件的代码行: `BTBOFullLe`+`Emb` 426, `CumUpAcceptSim`+`CumValZ` 401, `CumUpLe` 146, `BTBOFullLv`+`St` 419, `BTBOFullEb`+`V1`+`V3`+`CumUpAcceptVal` 739).

| 还缺的件 | 新增行 (估计) | 其中毛刺 (估计) |
|---|---|---|
| 左 `𝓞` 对右 `O`, `Ordˢ`, `Z` 的跨树关系, 带基底嵌入, `add`, `rep`, `Ω`, 链, `ψ`, `ψ₀` | 1200 到 2000 | 700 到 1200 (同下标的结构部分不累加也要) |
| 对照树输出的值严格 (`St`, `SV`), 在 `Gᵀ` 上重做 | 800 到 1600 | 全部 |
| 下标: 带基底的 `V1`, `V3` | 200 到 400 | 全部 |
| 组装 `Low`, `Upp` | 200 到 300 | 全部 |
| 合计 | 2400 到 4300 | 1900 到 3500, 约 8 成 |

## §3 判断 (未编译)

1. **`CumVal` 的 "两边的值严格性" 可以少一边.** `V2ᶜ` 是定理, 下标这一层左边不要 `St`. 要它用上, 折叠单调的结论要写成 $\preccurlyeq^c$ 而不是 $\preccurlyeq$. 从形状看可以 (`ψ₀` 的输出逐项对应, 链的下标映射严格增), 这一步没写.
2. **右边的值严格性看来省不掉.** 把 `toLevel` 层号嵌进累加, 要在 $x\prec f_{m+1}$ 时判定 $x$ 是否 $\prec f_m$. `V1` 靠 `SV` 给的字面前驱 $c_m$ 做有界三歧. 只有 $f_m\sqsubseteq^\mathsf{I}f_{m+1}$ 时没有公共字面上界. 这是壁垒定理的同类情形, 这里没有写成定理.
3. **同下标结构模拟 ($\Phi:A\to$ `Ordᴵ`) 单独不够.** 外层闭包的分支可以同下标对应, 但 $\psi_\Omega(1)=\omega\cdot\Omega_\Omega$ 使第 1 项里就有 $W+\Omega_\eta$, $W$ 是闭包, 内层闭包的链又是累加对 `toLevel`, 第 0 层目标还把值 (`em`) 放回项里. 所以关系在每层都只能是 $\preccurlyeq$, 下标的差隔离不到最外层.

## §4 第一个障碍

项上的第一个实际卡点: `⊴` 没有传递. `T-strict` 只到链的第 1 项. 第 2 项起的严格性 ($z_n+1\trianglelefteq z_{n+1}$, 对 $n$ 归纳) 要串两个 `⊴`; `rf` 情形要把节点搬到结构等价的节点上, 世界只模 $\approx^A$. 临时文件的报错:

    error: [UnequalTerms]
    u′ != u of type A
    when checking that the expression q′ has type u ⊲ _v_75

这只说这样写不通, 不是否定. 目标 2 的第一个硬件是 §2 表第一行的跨树关系, 没有开始写.
