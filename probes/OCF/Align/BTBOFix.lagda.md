# BTBO 折叠的四行补丁 (暂不合入 src)

> [BTBOSemantics](BTBOSemantics.lagda.md) 判定现有 BTBO 的折叠在两处偏离 Buchholz 的规则, 后果是层号到 $\omega$ 以后全部压平到 $\psi_0(\Omega_\omega)$. 本文把修复写成对 [BTBO](../../../src/OCF/BTBO.lagda.md) `Ord-Ord` 模块的四行改动, 在 probes 中完整记录并编译; 是否合入 src 由作者决定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFix where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open BoundedTrich hiding (_+_)
open Ord-Ord
```

## §1 两个缺陷

1. `ψ<` 的 `injᵇ` 分支 (目标层 $i$ 低于极限的下标 $j$) 写的是 `lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)`: 链上每一步只经过目标层的 $\psi_i$, 从不经过共尾层的 $\psi_j$. 结果是 $\psi_i$ 把 $i+1$ 以上的所有层当成 $i+1$ 层 (压平). [BTBOSemantics](BTBOSemantics.lagda.md) §4 对目标层 0 在 Agda 中证明了 $\psi_0(\Omega_{\mu+1})\approx\psi_0(\Omega_1)$ 对一切 $\mu$.
2. `ψ₀` 在后继层是逐层一步折叠的复合, 在极限层 $\lambda$ 是对 $\lambda[n]$ 的对角: 每一项先把 $\Omega_\lambda$ 换成 $\Omega_{\lambda[n]+1}$ 再折叠. $\Omega_\lambda$ 从不以常量身份进入计算, 所以 $\psi_0(\Omega_\lambda+1)$, $\psi_0(\Omega_{\lambda+1})$ 都退回 $\psi_0(\Omega_\lambda)$.

两者合起来: $\psi^n(0)$ 从 $n=2$ 起恒为 $\psi_0(\Omega_\omega)$ (估计, 见 BTBOSemantics §7, §10 的置信度表).

## §2 补丁

**补丁 1**: `injᵇ` 分支的链改为经过共尾层 $j$ 的直接折叠 `ψ< q`, 其中 $q:j<\ell$ 是 `limᵢ` 节点自带的证明. 这就是 Buchholz 规则 6 ($\gamma_{k+1}=\psi_j(f\,\gamma_k)$, $\psi_i(a)[n]=\psi_i(f\,\gamma_n)$). `injᶜ` 分支 ($i=j$) 原本就是这条链, 不动.

**补丁 2**: `ψ₀` 改为直接折叠. 后继层与极限层统一用 `ψ< (z<nz _)`, 不再复合, 不再对角. `z<nz` 是 `BoundedTrich` 现成的引理.

其余 (`Ω`, `_+_`, `lfp`, `ordᴰ`, `ψⁿ`, `BTBO`, `FGH`) 一字不动. 下面是补丁后的定义, 加上标 `ᶠ` 以免与原模块冲突:

```agda
ψ<ᶠ : ∀ {i ℓ} → i < ℓ → Ord ℓ → Ord i
ψ<ᶠ p zero     = Ω _
ψ<ᶠ p (suc a)  = lfp (ψ<ᶠ p a +_)
ψ<ᶠ p (lim f)  = lim (ψ<ᶠ p ∘ f)
ψ<ᶠ {i} {ℓ} p (limᵢ {i = j} q f) with <-dec q p
... | injᵃ j<i  = limᵢ j<i (ψ<ᶠ p ∘ f ∘ coe)
... | injᵇ _    = lim (λ n → ψ<ᶠ p (f (coe₀ (iter (ψ<ᶠ q ∘ f ∘ coe₀) zero n))))   -- 补丁 1
... | injᶜ refl = lfp (ψ<ᶠ p ∘ f ∘ coe₀)

ψ₀ᶠ : ∀ {ℓ} → Ord ℓ → Ord₀
ψ₀ᶠ {ℓ = zero}    a = a
ψ₀ᶠ {ℓ = suc ℓ}   a = ψ<ᶠ (z<nz _) a                                           -- 补丁 2
ψ₀ᶠ {ℓ = lim f _} a = ψ<ᶠ (z<nz _) a                                           -- 补丁 2

ψⁿᶠ : ℕ → Ord₀
ψⁿᶠ = iter (ψ₀ᶠ ∘ Ω ∘ ordᴰ) zero

BTBOᶠ : Ord₀
BTBOᶠ = lim ψⁿᶠ

_ : ℕ
_ = FGH BTBOᶠ 99
```

终止性: `injᵇ` 分支里两个递归调用的树参数都是 `f` 的像, 是 `limᵢ q f` 的子项; 第一个参数换成 `q` 不影响度量. `ψ₀ᶠ` 不再对 `ℓ` 递归.

## §3 定义性核对

补丁前后在第 1 层以内没有区别 ($\psi^1(0)=\omega$ 仍成立); 区别从跨两层开始. 原来 $\psi_0(\Omega_2)$ 的链只经过 $\psi_0$ (BTBOSemantics 核实它与 $\psi_0(\Omega_1)$ 同链), 现在经过 $\psi_1$:

```agda
_ : ψⁿᶠ 1 ≡ ω
_ = refl

n₂ : Ordᴰ
n₂ = suc (suc zero)

chainᶠ : ℕ → Ord (suc zero)                      -- γ₀ = 0, γ_{k+1} = ψ₁(↑γ_k)
chainᶠ = iter (λ x → ψ<ᶠ zero (↑ zero x)) zero

_ : ψ₀ᶠ (Ω n₂) ≡ lim (λ n → ψ<ᶠ (suc zero) (↑ zero (chainᶠ n)))
_ = refl
```

即 $\psi_0(\Omega_2)[n]=\psi_0(\gamma_n)$, $\gamma$ 是 $\psi_1$ 的链, 与 Buchholz 规则 6 一致 (链起点 0 而非 $\Omega_1$, 只差一个平移).

## §4 与 ψᴱ 的关系, 以及仍是估计的部分

[Finite](Finite.lagda.md) §3 的 `ψᴱ` 等于本文的 `ψ<ᶠ` 再加两处外观修正: $\Omega_0=1$ (`Ωᴱ zero = suc zero`) 和链起点 $\Omega_j$. 这两处不改变 $\ge\varepsilon_0$ 的值 (BTBOSemantics §10), 但对齐证明需要基本列逐项相同, 所以分支 2 用 `ψᴱ` 而不是 `ψ<ᶠ`.

补丁后 `BTBOᶠ` 的值: 对角 $x_{k+1}=\psi_0(\Omega_{\mathsf{ord}^\mathsf{D}x_k})$ 每一步都是 Buchholz 基本列的无停滞延拓, 极限估计为 $\alpha\mapsto\psi_0(\Omega_\alpha)$ 的最小不动点, 即扩展 Buchholz 记号的 $\psi_0(\Omega_\Omega)$ (BTBOSemantics §9). 这是估计, 不是定理; 把它变成定理要走分支 2 的对齐路线 (Finite, Omega1, 再到有限下标与对角), 还要处理 `ordᴰ` 的累积和使层号基本列与 EBO 只共尾不逐项同的问题.

## §5 若合入 src 需要同步改的文字

- `ψ<` 定义上方的公式: `injᵇ` 情况改为 $\lim(n\mapsto\psi_p(f(\gamma_n)))$, $\gamma_0=0$, $\gamma_{k+1}=\psi_q(f(\gamma_k))$.
- `ψ₀` 定义上方的公式: 三种情况合并为 "$\ell=0$ 时为恒等, 否则为 $\psi_{0<\ell}$".
- 例子 `ex2`–`ex4` 的注释 ($\psi(\Omega_\omega)$, $\psi(\Omega_\mathsf{BO})$, …) 与 "BTBO = $\psi(\Omega_\Omega)$" 的陈述: 改为估计口吻, 并注明依据.
- 结尾 "累积和不改变最终极限的估值" 一句: 保留, 但同样标为估计.
