# 一切深度 (十一): 判据的裁决

> 接 [UniformNF3D3Z](UniformNF3D3Z.lagda.md), [UniformNF3D3Accept](UniformNF3D3Accept.lagda.md), [UniformNF3D3Neg](UniformNF3D3Neg.lagda.md). 结论先说:
>
> 1. **深度与阶段无关, 没有逐 $d$ 的支配论证.** `RFΘf n` 对一切 $n$ 同一个项; `Row`, `FF₁`, `Step1` 对深度只有隐式参数, 证明不对 $d$ 归纳. 对 $d$ 递归的只有**定义** (`Sp`, `Fr`, `FlU`, `WSp`, `SG`, `Rais`) 与两处两行的分支 (`flRep`, `raisAt`/`raisM`).
> 2. **吸收者没有新的: 只有 `clk`/`FlOver`.** 新的是门槛: 点里的地板集 $\mathcal F$, 与世界的 Kripke 单调 `upX`.
> 3. **D2U §4 怕的 "底抬高封闭性" 是假的, 也不需要.** `¬BaseRaise` 编译. 副本只在头值压过 $F_a\,P\,s$ 的脊上被读 (`Rais`).
> 4. **没有第一个不可证的字段**: `Gᴺ-Ψ3`, `Gᴺ-Ω̂ n`, `Gᴺ-Ω⁺` 都编译, 验收都过.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3V where

open import OCF.Align.UniformNF3D3Z using (Gᴺ-Ψ3; Gᴺ-Ω̂ᶜ; Gᴺ-Ω⁺)
open import OCF.Align.UniformNF3D3T using (RFΘf)
open import OCF.Align.UniformNF3D3Neg using (¬BaseRaise)
```

## §1 D2U §4 错在哪里

D2U 想要 `Frm` 相对化, 再问 `fo2 O X P Q ∈ 𝓚` 能不能推出 `fo2 O X P B ∈ 𝓚`. 相对化是对的, 后半句问错了.

副本 $P_m=F_a^{m+1}P$ 作为帧被读时, 脊的头被某一行抬过: 新底 $B$ 满足 $B\sqsupseteq P_m\,Q$ (头值压过帧在旧底上的值), 不只是 $B\sqsupseteq Q$. 这时对任意尾巴 $t$,

$$F_t\,P\,B\;\sqsupseteq\;P\,B\;\sqsupseteq\;B\;\sqsupseteq\;P_m\,Q\;\sqsupseteq\;P_0\,Q\;=\;F_a\,P\,Q,$$

所以上下文 `fo O X (P,B)` 压在 $a$ 上下文 `fo O X (P,Q)` 之上, `clk` 直接给出成员. 同一个 $O$, 没有新吸收者 (`Row.kUp`, `upm` 的 `Bk₂`). `¬BaseRaise` 说只有 $B\sqsupseteq Q$ 不够: 小尾巴 $t=0$ 处 $X\,B$ 低于 $F_a\,Q$, 即便类满足 `clk`, `cgk`, `ho`.

## §2 四个新件

**`Fr`/`Sp` (D3O): 反柯里化.** `fold1` 只在后继行碰脊的头, 其余行是 `Run` 层的定义性计算, 对未知的 $d$ 也算. 这解除了 `Obs` 随深度增长: 只有一个 `fo1 {d}`. 规则层 (D3N, D3G, D3C, D3CF) 是 D1 的脚本克隆, 一条规则也没有多. 与原树的联系只在 D3B 一处, 经 `Cor`.

**$\mathcal F$ (D3W `Base`): 点的门槛.** 第 $m+1$ 份的类族是 $\mathcal P\wedge$ `Kp`, 它对 $a\sqsupseteq F_a\,P\,s$ 封闭, 不对 $a\sqsupseteq$ 底封闭. 所以闭包的门槛必须跟点走. D2C 的 `Cp` 是这件事的影子, 现在没有了.

**`RF`/`SG`/`Rais` (D3W): 世界.** `RF d w X`: $X$ 在世界 $w$ 上好. 脊的每一格带 `(P, w, RF d w P)` 作为数据, 所以 `SG` 与世界都停在 `Set₁`, 带世界的脊停在 `Set₂`, 宇宙不随深度增长. **这是能写下 "一切深度" 的原因**: 如果 `SG` 对世界存在量化, 世界又要含 `SG`, 宇宙层级会循环.

**`w′` (D3R): 副本的世界.** 点 $b_1\in w'$: 压在 $X$ 的一个好点 $b^\dagger$ 之下, $\forall O\in\mathcal P_1$ `fo1 O X (P,t) ∈ 𝓚`, $P_0\,t\in\mathcal F_1$. `RFm` 的五个字段都是直接算的.

## §3 与带标签路线的对照

| 带标签 (Uniform3Depth2*) | 这里 | 来历 |
|---|---|---|
| `Wd c d X u` 的 $\forall c'\succeq c$ | `RF` 的 `upX` + `Rais` | 形状受指导, 世界的内容是树侧的 |
| `Rd d X X′` | `_≈U_`, `_≈S_`, `fold-≅U` | 同形, 反柯里化后不需要按深度的行引理 |
| `FLΩ[c]` | `𝓕b`, `cl`, `flX` | 树侧的 |
| `copyW`, `limWd` (后继行落到深度 $d$) | `repU`, `flRep`, `RFm` | 形状受指导 |
| 对 $d$ 没有归纳 | `Row`, `FF1`, `Step1` 的隐式 $d$ | 判据本身 |
| 标签 $\rho$ 记录底 | 脊 `WSp` 带 `RF` | 树侧的 |

读过的带标签文件只用来定形状, 构造里没有标签. 切片: 从 `Gᴺ-Ω⁺`, `Gᴺ-Ψ3`, `Gᴺ-Ω̂`, `Gᴺ-Ω̂ᶜ` 出发的定义级依赖不到 `EBO`, `Correspond`, `StandardOmega`, `GoodLBase`, `Uniform3Full`.

## §4 没有做的

$\psi_0(\Omega_{\Omega+1}+1)$, $\psi_0(\Omega_{\Omega+1}\cdot2)$ 与 `Ω⁺` 为底的塔: 没有试. 它们要把底换成 `Ω⁺ X`, 塔的底 `∅U` 现在是写死的; `WSp` 的形状不挡这件事, 但 `ws` 要改.

`¬BaseRaise` 编译的是深度 1 的例子. 深度 2 的同形例子 (比较 $X\,P\,B$ 与 $X(X\,P)\,Q$) 只在纸面.
