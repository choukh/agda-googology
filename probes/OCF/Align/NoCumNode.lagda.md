# 不累加, 第 0 层是值: $\psi_0(\Omega_{\Omega+1})$

> **判决: PARTIAL.** 证书 HOLDS, 严格高于 $\psi_0(\Omega_\Omega)$ HOLDS, 对过基本列验收的树的互模拟 **未走通 (没有开始写, 暂停)**. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞. 定义和证书不含记号; 记号只在 [NoCumNodeAccept](NoCumNodeAccept.lagda.md).
>
> ## 做法: 不加节点, 不克隆
>
> 上一轮 [Om1HnAccept](Om1HnAccept.lagda.md) 的障碍: `NoCumW.add⁰` 在第 $(0,0)$ 层对闭包写 `oc (W⊕x) (W⊕h)`, 计值时链点读 $W\oplus x$ 的输出 (`Om1HnNeg.shift`). 这里没有加 `oĉ` 节点. 改的是第 0 层的地位: **目标 $(0,0)$ 不再是数据上的折叠, 而是对一切层的项直接计值** ([NoCumNodeE](NoCumNodeE.lagda.md) 的 `E`, `val`). 于是
>
> - `os`: $\psi_0(x+1)=\lim_n\psi_0(x)\cdot n$, 乘法是树上的加法 `_+₀_`. 数据的 `add` 不会碰到第 $(0,0)$ 层的闭包: 那一层根本不出现在数据里.
> - 上升到 $(0,0)$ (`rv`): 链是值, $z_{n+1}=\ulcorner\psi_0(h\,z_n)\urcorner$, `⌜_⌝` 把值读回成只有 `o0`, `os`, `ol` 的数据, 世界是 $1$. 其他层的上升仍走数据的折叠 (`rg`).
> - 闭包 `oc` 在任何层都按链计值 (`Oc`), 链点读 $\psi_0$ 的输出, 守卫同上一轮.
>
> `NoCumW`, `NoCumEq`, `NoCumPsi`, `NoCumLe`, `NoCumMain` 一行不动, 直接导入. 上一轮估计的克隆 1850 行**全部省掉**; 代价是新的计值 `NoCumNodeE` (代码 481 行) 与上下文的输出换型 (`Om1Hn*` 的 Cx, Gd, Add, Omega, Psi 由脚本改写, `idC` 与 `Tm` 手写, 规则不变).
>
> ## 定理
>
> | 定理 | 文件 | 说的 | 档 |
> |---|---|---|---|
> | `G₁ : Ev (Ω̇ 1 one) …`, `T₁`, `HS-T₁` | `NoCumNodeMain` | $\psi_0(\Omega_{\Omega+1})$ 的证书, 无条件, 闭项 | 证书, 定理 |
> | `G-N : Root p a → Ev (Ω̇ p a) …`, `root₀/₁/₂`, `Gᵖ₁`, `GΩ` | `NoCumNodeMain` | 一切 $(p,a)$ 只差根上义务; $a\le2$ 无条件 | 证书, 定理 |
> | `X`, `XR` | `NoCumNodeX` | 出口: `Gd 𝓖 x` 且 `idC` 在类里, 则 $\psi_0(x)$ 有证书, 一切层 | 定理 |
> | `Psi`, `AddG.Add`, `ΩG` | `NoCumNodePsi`, `NoCumNodeAdd`, `NoCumNodeOmega` | 与 `Om1Hn` 同一组闭包定理, 输出换成 `Tm` | 定理 |
> | `val≅`, `E-tr`, `val⊴`, `E-dn` | `NoCumNodeE` | 证书无关, 沿 $\approx$ 搬, 第一位置单调, 往下搬 | 定理 |
> | `V-Q` | `NoCumNodeBase` | 高度 0 的项的值 $\cong$ `CumReadCF` 的 `ord ∘ ψ` | 定理 |
> | `anyΩ`, `same-Ω`, `same-T⁰` | `NoCumNodeAccept` | $\psi_0(\Omega_\Omega)$ 这一站不变: 对任何证书 $\cong$ `BTBOᴵ` (基本列逐项一致) | 基本列验收, 定理 |
> | `BTBO≺T₁` | `NoCumNodeAccept` | `BTBOᴵ ≺ fr T₁`, 严格; 由第 1 项 $\trianglerighteq\psi_0(\psi_\Omega(1))\trianglerighteq\psi_0(\Omega_\Omega)+1$ (`term1`, `lemmaX`, `repStep`) | 序数值下界, 定理 |
> | `label-Ω` | `NoCumNodeAccept` | `Lab` 探路 | 探路 |
>
> ## 没有做的
>
> 对过基本列验收的 $\psi_0(\Omega_{\Omega+1})$ 的树 (`OCF.Free` 的 `GᴺΩ̇ 1`) 的互模拟. 要一个跨树关系: 左边 `𝓞 p a u` 与它的值, 右边 `O c φ`, `Ordˢ`, `Z`, 加地板与 `tr`. 判断: 基本列第 1 项起可能逐项一致 (第 0 层的加法现在是值上的, 与 `ĉᴸ` 读 `toZ t₀` 同一个语义), 但没有编译. 估计 1200 到 2000 行 (`Om1Cum` §2 表第一行同一件). 这是估计.
>
> ## 翻译账
>
> | 东西 | 来源 |
> |---|---|
> | 第 0 层是值 (`E`, `val`) | 树逼的: `shift` 说数据上的加法把 $W$ 带进链点. 改法与 `OCF.Free.Prefix` 的 `ĉᴸ` 同一个语义 (链与输出分开), 那个形状是标签路线 (`Prefix`, `UniformS`) 为对上 EBO 的链写的, 依据是 $a+\lim\chi_n=\lim(a+\chi_n)$. 这里**没有照抄 `ĉᴸ` 的字段**, 只用了它的语义; 所以如实写: 受记号影响, 间接 |
> | `os` 行 $\lim_n\psi_0(x)\cdot n$ | 旧折叠的 `rep`, 即 Buchholz 的 $\psi(a+1)=\psi(a)\cdot\omega$, 上一轮已有, 不是新读的 |
> | `rv` 的链从 $1$ 起 | 照旧折叠 `chainᵒ` 从 $\Omega_0$ 起 |
> | `Nz`, `Is0`, `⌜_⌝`, `Tm` | 树逼的: 上升到 $(0,0)$ 时链只能是值; 上下文要能收值 |
> | `Root`, 类, `𝓥`, `Bb` | 同 `Om1Hn` |
>
> **这一步算提供信息, 不算加深** (判断, 按 AGENTS.md 的标志): 没有新构造子或节点; 闭包定理没有新增前提 (`Root` 与 `Om1Hn` 相同); 验收用的是序数值 (`BTBO≺T₁`) 和基本列 ($\psi_0(\Omega_\Omega)$ 站), 不只是 `Lab`. 但互模拟没写, "基本列与记号的差" 还没给出, 所以这一判断是暂时的.
>
> **`oĉ` 是不是读自记号.** `OCF.Free` 的 `ĉᴸ c t₀ g o₀ o` 来自 `Prefix` (LOG: "前缀 + 待计值的链" 与 "ψ 作用于第 0 层的待计值链"), 那一轮的目标是对上 EBO 的标签 (规则 6 的链点带同一个栈, "EBO 的 $b[\gamma_k]$ 含整个前缀"). 所以 `ĉᴸ` 的形状是记号引导的; 它的语义 (加法不重跑链) 是序数算术. 照 `ĉᴸ` 加节点算加深翻译; 这里没有加.
>
> **`TLRule` 的和节点能否替代.** 判断, 没有编译: 两边是同一件事的两种写法. `TLRule` 把加法做成数据的构造子 (`⨾`), 值是加法 (`sum⊞`), 链不会因加法重跑; 这里把第 0 层做成值, 加法是值上的 `_+₀_`. 差别: `TLRule` 只到 $\psi_0(\Omega_\Omega)$, 第 0 层没有闭包, 所以 "加法碰到闭包" 这件事在那边还没出现; 这里在 $\Omega+1$ 已经过了闭包. 要替代, `TLRule` 的和要扩到高度 $\ge1$ 的闭包, 没做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNode where

open import OCF.Align.NoCumNodeMain using (G₁; T₁; HS-T₁; G-N; Root; root₀; root₁; root₂; Gᵖ₁; GΩ)
open import OCF.Align.NoCumNodeX using (X; XR)
open import OCF.Align.NoCumNodeBase using (V-Q)
```
