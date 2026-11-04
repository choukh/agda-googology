# 已发表 BTBO 的值验收: 判决 PARTIAL

> **验收文件, 读记号.** 任务: 封存的 `src/OCF/BTBO` 的序数 (层号走 `ordᴰ`, 把每个 `lim` 换成累加) 与 probes 的 `BTBOᴵ` (带字面标签 $\psi_0(\Omega_\Omega)$) 是否同值. 本组文件前缀 `BTBOVal`. src 只导入, 未改动.

## 判决

**PARTIAL.** 整棵 BTBO 的同值没有证出, 也没有反例. 证出的是: 两个树族的折叠差异全部不改值, 问题归结为层号上的一件事; 对角线的前四步已交错; 字面的 $\sqsubseteq^0$ 这一档是假的 (否定定理).

## 定理

全部编译通过, 无前提, 除非另外写明.

| 名字 | 陈述 | 文件 |
|---|---|---|
| `FGH-tr₀` | 第 0 层翻译不改 FGH: `S.FGH a n ≡ FGH (tr₀ a) n` | `BTBOValBase` |
| `ordᴰ-≥` | `tr₀ x ≼ fd (ordᴰ x)`, 对一切树 | `BTBOValBase` |
| `Ψ⁰≼<`, `Ψ⁰≽<` | 对一切 $p:0<a$: Level 的 $\psi^0(\Omega_{\tau a})$ 与 src 的 $\psi_p(\Omega_a)$ 互相 `≼` | `BTBOValDn`, `BTBOValUp` |
| `ψ₀≈` | 对一切 `Ordᴰ` 层号 $a$: `tr₀ (S.ψ₀ (S.Ω a)) ≈ᵛ ψ⁰ (Ω (τ a))` | `BTBOValMain` |
| `x-step` | `tr₀ (ψⁿ (k+1)) ≈ᵛ ψ⁰ (Ω (τ (ordᴰ (ψⁿ k))))` | `BTBOValMain` |
| `x₂≈BO` | `tr₀ (ψⁿ 2) ≈ᵛ ψ⁰ (Ω ωᴵ)`: 层号 $0,2,5,9,\dots$ 对 $0,1,2,\dots$ | `BTBOValMain` |
| `row₀`...`row₃` | $\gamma_0\preccurlyeq x_1\preccurlyeq\gamma_1\preccurlyeq x_2\preccurlyeq\gamma_2$ | `BTBOValMain` |
| `absorb`, `absorb-lim` | 前提 `St (tr₀ x)`: `fd (ordᴰ x) ≼ ψ⁰ (suc (tr₀ x))`; 极限时 `≼ ψ⁰ (tr₀ x)` | `BTBOValAbsorb` |
| `ordᴰ-not-cong` | $\omega$ 与 $\lim(\omega,\omega,\dots)$ 值相等, 都 `HS`, 而累加后不再 `≼` | `BTBOValAbsorb` |
| `no-⊑⁰`, `no-⊑⁰-lab` | `¬ (tr₀ BTBO ⊑⁰ BTBOᴵ)`, 对一切带字面标签 $\psi_0(\Omega_\Omega)$ 的树同样 | `BTBOValNeg` |
| `LeE.WithLaws.Ψ⁰-emb` | 前提 `Laws`: 层号前驱间的保序嵌入给 $\psi^0(\Omega_a)\preccurlyeq\psi^0(\Omega_{a'})$ | `BTBOValLe` |
| `ω+1≈`, `x-ω+1` | 层号 $\omega_D+1$ 与 $\omega+1$ 折叠值相等, src 的 $\psi_0(\Omega_{\omega_D+1})$ 同 | `BTBOValLeInst` |
| `¬⊑₁`, `¬⊑₂` | 上面两个层号不 $\sqsubseteq^\mathsf{I}$ 相关, `Ψ⁰-mono` 不适用 | `BTBOValLeInst` |

**条件定理.** `cond-main` (`BTBOValMain`): 若每个 $\psi^0(\Omega_{\tau(\mathsf{ord}^\mathsf{D}x_k)})$ 被某个 $\gamma_m$ 控制, 每个 $\gamma_{m+1}$ 被某个 $\psi^0(\Omega_{\tau(\mathsf{ord}^\mathsf{D}x_k)})$ 控制, 则 `tr₀ BTBO ≈ᵛ BTBOᴵ`. 前提就是未证的内容.

## 吸收成立不成立

分开说:

1. **层号的值上, 严格的树: 成立, 定理.** $x\preccurlyeq\mathrm{ord}^\mathrm{D}x\preccurlyeq\psi^0(x+1)$.
2. **层号的值上, 不严格的树: 不成立, 定理.** `ordᴰ-not-cong`. 所以 `HS` 不够.
3. **src 的 $x_k$ 严格吗:** 未证. 有限比较器在预算内没有结论 ([BTBOValTest](BTBOValTest.lagda.md) §4), 只有纸面判断.
4. **放大之后折叠不变吗:** 在 $\omega$ 与 $\omega+1$ 处是定理 (`x₂≈BO`, `x-ω+1`). 一般情形**未决**: 没有证明, 也没有反例. 判断: 成立, 依据是经典的单调性和上面第 1 条. 这只是判断.

## 字面的值验收

`no-⊑⁰` 否定的是这个字面关系, 不是序数值相等. $\sqsubseteq^0$ 的叶子是 $\cong$, 而 src 的 $\Omega_0=\omega$ 让 $\omega^\omega$ 的基本列是 $\omega,\omega^2,\dots$, 对面是 $1,\omega,\omega^2,\dots$. 所以 src 的 BTBO **过不了** AGENTS 里 "互相 $\sqsubseteq^0$" 这一档, 即使同值也一样. 要验收它只能用 `≼`, 这是比 $\sqsubseteq^0$ 弱的关系 (`⊑→≼` 的逆不成立).

## 第一个障碍

$\gamma_2\preccurlyeq x_3$, 即 $\psi^0(\Omega_{L_1})\preccurlyeq\psi^0(\Omega_{\tau(\mathsf{ord}^\mathsf{D}x_2)})$. 这是第一个真要比较 `toLevel` 层号与累加层号的地方. 不是报错, 没有卡住的编译: 缺的是一个对象.

- 有判据: `Ψ⁰-emb` 要一个保序嵌入 $E$ (`Laws`).
- 缺的是造 $E$ 的办法. 从值 `≼` 造不出来: 见证 $a\preccurlyeq b$ 对同一个前驱经两条路径可能给两个不同的像, 派发就错开; 想要像精确等值, 要在 $b$ 里判定极限点, 那是 `no-lim-cmp`, `no-cut` 的形状 (判断, 没有针对这一条编译否定).
- 下界一半有更窄的路: 累加的目标字面上含 `Σ + d`, 所以嵌入可以按 "最小的 $n$" 分块加偏移. 这要求左边的树严格 (判定 "$c\prec f_m$"), 目前没有严格性定理. 上界一半的目标 `toLevel γ` 没有这种字面结构, 只在 $\psi^0(s)$ 的基本列 $A\cdot n+R$ 处有. 这两条都是纸面分析, 未编译.

这是 "未走通", 不是路线否定.

## 证明方法的记录

`Dn`, `Mh`, `Le` 都是**归纳**关系, 不是 `Uniform` 的观测前序, 按右边或左边的层号分层才严格正 (同 Level 的 `Eq₊`). `limᵢ` 只有两条规则: 同层逐分支, 和只看链起点. 所以 $\mathrm{up}\,y$ 不会因为值小就在 $\Omega_1$ 之下, 这正是 `ψ⁰-not-cong`, `ψᴱ-not-mono` 的 $y$. 这样的关系对折叠封闭, 不要 `Good`, 也不要 PER. 每个方向约 300 行, 编译各约 10 秒.

$\Omega_0=\omega$ 对 $1$ 的吸收只靠一条: `Mh` 的叶子要求右边非零.

## 文件

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOVal where

open import OCF.Align.BTBOValBase public using (tr₀; fd; FGH-tr₀; ordᴰ-≥)
open import OCF.Align.BTBOValDn public using (τ; Ψ⁰≼<)
open import OCF.Align.BTBOValUp public using (Ψ⁰≽<)
open import OCF.Align.BTBOValMain public using (ψ₀≈; x-step; cond-main; x₂≈BO; row₀; row₁; row₂; row₃)
open import OCF.Align.BTBOValAbsorb public using (St; absorb; absorb-lim; ordᴰ-not-cong)
open import OCF.Align.BTBOValNeg public using (no-⊑⁰; no-⊑⁰-lab)
open import OCF.Align.BTBOValLe public using (module LeE)
open import OCF.Align.BTBOValLeInst public using (ω+1≈; x-ω+1; ¬⊑₁; ¬⊑₂)
open import OCF.Align.BTBOValTest
```
