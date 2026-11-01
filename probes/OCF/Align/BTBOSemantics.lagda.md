# BTBO 的语义: 树上的 ψ 到底算出哪个序数

> 本文回答一个问题: [BTBO](../../../src/OCF/BTBO.lagda.md) 的标签 "$\mathsf{BTBO}=\psi(\Omega_\Omega)$, $\psi^2(0)=\psi(\Omega_\omega)$" 能不能信.
> 方法: 给树一个集合论语义 $[\![\cdot]\!]$, 按 Agda 定义逐条算 `ψ<` 与 `ψ₀` 的值, 再与 Buchholz 的 $\psi_\nu$ (Buchholz 1986; 本仓库 [Notation/EBO](../../../archive/probes/OCF/Notation/EBO.lagda.md) 的基本列) 和 Madore 的 $\psi$ 比较.
> 前置: [Finite](Finite.lagda.md) §2 列出的五条差异; 本文给出它们各自是否改变数值.
>
> **结论 (详见 §9)**:
> - 树的一步折叠 `ψ< zero : Ord (ℓ+1) → Ord ℓ` 就是 Buchholz 基本列规则 (底数 $\Omega_0=\omega$, 链从 0 起, 两者都不改变 $\ge\varepsilon_0$ 处的值), 但**没有 $C$-集的停滞**.
> - 树的直接折叠 `ψ< p : Ord ℓ → Ord i` 把所有高于 $i+1$ 的层**压平**成 $i+1$ (§4, 对目标层 0 用 Agda 证明到任意层). 跨层的 `ψ₀` 是 "一步折叠的复合 + 极限层上的对角", 即 Kovács 改写自 Madore 的**迭代折叠**, 只是逐层闭包从 $\exp$ 换成了 $+$.
> - $[\![\psi^1(0)]\!]=\omega$ (Agda), $[\![\psi^2(0)]\!]=\psi_0(\Omega_\omega)=\mathsf{BO}$ (高置信度). 偏差 (d) 在这里恰好不改变数值.
> - 从 $\Omega_{\omega+1}$ 起压平吞掉了一切: 在任何 $\ge\omega$ 的层上, 树的 `ψ₀ (Ω ℓ)` 都等于 $\mathsf{BO}$. 于是 $[\![\psi^k(0)]\!]=\mathsf{BO}$ 对一切 $k\ge2$ 成立, **$[\![\mathsf{BTBO}]\!]=\psi_0(\Omega_\omega)=\mathsf{BO}$, 不是 $\psi(\Omega_\Omega)$** (估计, 置信度约 80%; 依赖的假设见 §9).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOSemantics where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open BoundedTrich hiding (_+_)
open Ord-Ord
open import OCF.Align.Finite using (_≈_; z≈; s≈; l≈; +-≈; iter-≈; chain₁; chain₂; ψᴱ; Ωᴱ)
```

本文的每条结论标注来源:

- **[Agda]**: 本文件中以 `refl` 或短证明机器检验;
- **[标准]**: 序数论的已知事实 (Buchholz 1986; Wikipedia "Ordinal collapsing function" 与 "Buchholz psi functions" 的数值表; 本仓库 EBO 的基本列规则);
- **[估计]**: 本文的论证, 给出假设与置信度, 未形式化.

## §1 语义与约定

**模型.** 在 ZFC 中把 `Ord ℓ` 解释为它的全体良基树 (W-类型的标准集合论模型). 对 `ℓ : Ordᴰ` 记 $|\ell|$ 为其秩 (可数序数). 对树 $a$:

$$
[\![0]\!]=0,\quad [\![a^+]\!]=[\![a]\!]+1,\quad [\![\mathsf{lim}\,f]\!]=\sup_n[\![f\,n]\!],\quad [\![\mathsf{lim}_i(p,f)]\!]=\sup_{x:\mathsf{Ord}_i}[\![f\,x]\!],\quad [\![\uparrow_p a]\!]=[\![a]\!].
$$

**层级是链.** `_<_` 的三个构造子说明 $x<\ell$ 当且仅当 $x$ 是 $\ell$ 的某个结点. 由有界三歧性 (`<-dec`), $\ell$ 的全部前驱两两可比; 且 $x<y\Rightarrow|x|<|y|$. 所以前驱集合在 $|\cdot|$ 下与序数 $|\ell|$ 序同构. 这有两个后果: `ψ<` 里 `<-dec q p` 的三个分支恰好对应层号的序数比较; 不同的证明 $p:i<\ell$ 给出语义相同的 `ψ< p`.

**Ω 的约定.** 由归纳, $\mathsf{Ord}_\ell$ 的上确界是 $\omega_{|\ell|+1}$, 且 $[\![\Omega_\ell]\!]=\omega_{|\ell|}$, 其中 $\omega_0=\omega$. 这里 $\Omega_0=\omega$ 是树的约定 (Kovács 与 Madore 同); Buchholz 取 $\Omega_0=1$. 下文写 $\Omega_\nu$ 均指 $\omega_\nu$ 并令 $\Omega_0=\omega$, 与 Buchholz 比较时另行说明.

```agda
_ : Ω zero ≡ ω
_ = refl
```

**"字面上确界" 还是 "约定上确界".** 在 ZFC 的标准模型里 `Ord i` 含全部可数分支树, 所以 $\sup_{x:\mathsf{Ord}_i}$ 字面上就是 $\Omega_{i+1}$, 两种读法一致. 如果换成可数模型 (例如只取可计算树), 这个上确界会变小. 但这不影响任何最终结论: `ψ<` 遇到 `limᵢ` 时只做两件事, 要么沿一条 $\omega$-链把**具体的**点喂给 $f$, 要么把 `limᵢ` 原样降到更低的层 (穿透). 落到 `Ord₀` 的树里没有 `limᵢ`, 它的值就是这棵良基树的秩, 不随模型改变. 上确界的读法只影响我们怎样**命名**中间的不可数树.

**非外延性.** `ψ<` 是树上的函数, 不是序数上的函数. 两棵值相同的树可以有不同的折叠值 (§5 的停滞例子). 所以 "$[\![\psi_\nu(a)]\!]$" 只对具体的树有意义. 下文计算的都是对角线上实际出现的那些规范树.

**`ordᴰ` 的累积和.** `ordᴰ (lim f) = lim (cumsum (ordᴰ ∘ f))`. 由归纳, $[\![x]\!]\le|\mathsf{ord}^\mathsf{D}x|\le\omega^{[\![x]\!]+1}$. 若 $x=\mathsf{lim}\,f$ 且 $[\![x]\!]$ 是不被任何 $f\,n$ 达到的 $\varepsilon$-数, 则累积和的每一项都 $<[\![x]\!]$, 于是 $|\mathsf{ord}^\mathsf{D}x|=[\![x]\!]$. 对角线 $\psi^n$ 上出现的 $x$ 都是这种情形, 所以**累积和不改变层号的值**, 只改变层号的基本列. BTBO 原文对此的判断是对的. 层 $\mathsf{ord}^\mathsf{D}\,\omega$ 的基本列是 $0,2,5,9,\ldots$:

```agda
n₁ n₂ n₃ : Ordᴰ
n₁ = suc zero
n₂ = suc n₁
n₃ = suc n₂

fs : Ordᴰ → ℕ → Ordᴰ
fs (lim f _) = f
fs _         = λ _ → zero

ℓω : Ordᴰ
ℓω = ordᴰ ω

g : ℕ → Ordᴰ
g = fs ℓω

fl : (n : ℕ) → g n < ℓω
fl n = f<l n

_ : (g 0 ≡ zero) × (g 1 ≡ n₂) × (g 2 ≡ suc (suc n₃))
_ = refl , refl , refl
```

## §2 一层之内: 树的 ψ 的语义方程

记 $\psi_\nu$ 为目标层 $\nu$ 的 `ψ< p` ($p:\nu<\ell$). 按定义逐条读出:

$$
\begin{aligned}
[\![\psi_\nu(0)]\!] &= \Omega_\nu \\
[\![\psi_\nu(a^+)]\!] &= [\![\psi_\nu(a)]\!]\cdot\omega \\
[\![\psi_\nu(\mathsf{lim}\,f)]\!] &= \sup_n [\![\psi_\nu(f\,n)]\!] \\
[\![\psi_\nu(\mathsf{lim}_\mu f)]\!] &= \sup_{x:\mathsf{Ord}_\mu}[\![\psi_\nu(f\,x)]\!] \quad (\mu<\nu,\ \text{穿透}) \\
[\![\psi_\nu(\mathsf{lim}_\mu f)]\!] &= \sup_k x_k,\ \ x_0=0,\ x_{k+1}=[\![\psi_\nu(f(\uparrow x_k))]\!],\ x_k:\mathsf{Ord}_\nu \quad (\mu\ge\nu)
\end{aligned}
$$

最后一行要注意: $\mu$ 只出现在提升 $\uparrow$ 里, 链的每一步都只经过目标层的 $\psi_\nu$.

```agda
_ : ∀ {i ℓ} (p : i < ℓ) → ψ< p zero ≡ Ω i
_ = λ p → refl

_ : ∀ {i ℓ} (p : i < ℓ) (a : Ord ℓ) → ψ< p (suc a) ≡ lim (iter (ψ< p a +_) zero)
_ = λ p a → refl

-- 穿透: ψ₁(Ω₁ 的提升) 仍是一个以 Ord₀ 为分支的 limᵢ
_ : ψ< {ℓ = n₂} zero (↑ zero (Ω n₁)) ≡ limᵢ zero (λ y → ψ< zero (↑ zero (↑ zero y)))
_ = refl
```

**引理 P (幂律)** [Agda 结构 + 语义归纳]. 设 $x$ 是层 $\le\nu$ 的树, 提升到层 $\ell>\nu$. 则 $[\![\psi_\nu(\uparrow x)]\!]=\Omega_\nu\cdot\omega^{[\![x]\!]}$. 当 $\nu\ge1$ 时这等于 $\omega^{\Omega_\nu+[\![x]\!]}$; 当 $\nu=0$ 时等于 $\omega^{1+[\![x]\!]}$.
*证明.* 对 $x$ 归纳. $x$ 的 `limᵢ` 层号都 $<\nu$, 所以只走穿透分支. 四个构造子分别对应 $\Omega_\nu\cdot\omega^0$, 乘 $\omega$, 以及 $\beta\mapsto\Omega_\nu\omega^\beta$ 的连续性 (两种极限). 对一切树都成立, 不需要树 "规范". ∎

**引理 C** [语义]. 一步折叠 $\psi_\nu(\Omega_{\nu+1})$ 的链是 $x_{k+1}=\Omega_\nu\omega^{x_k}$, 从 0 出发. 由引理 P, 其值为 $\varepsilon_{\Omega_\nu+1}$, 即 $\Omega_\nu$ 之后的第一个 $\varepsilon$-数 (当 $\nu=0$ 时是 $\varepsilon_0$). 这与 Buchholz 的 $\psi_\nu(\Omega_{\nu+1})$ 相同.

```agda
_ : ψ< zero (Ω n₂) ≡ lim (iter (λ x → ψ< zero (↑ zero x)) zero)   -- ψ₁(Ω₂) = ε_{Ω+1} 的链
_ = refl
```

## §3 一步折叠从不走 `injᵇ`, 它就是 Buchholz 的基本列

一步折叠 `ψ< zero : Ord (suc ℓ) → Ord ℓ` 里, 任何 `limᵢ` 的层号 $j$ 都满足 $j<\ell+1$, 即 $j\le\ell$. 所以 `<-dec q zero` 只可能是 `injᵃ` ($j<\ell$, 穿透) 或 `injᶜ` ($j=\ell$, 链). [Agda]:

```agda
data NotB {A B C : Set} : A ⊎ B ⊎ C → Set where
  isA : ∀ {x} → NotB (injᵃ x)
  isC : ∀ {x} → NotB (injᶜ x)

one-step : ∀ {j ℓ} (q : j < suc ℓ) → NotB (<-dec q zero)
one-step zero    = isC
one-step (suc q) = isA
```

把一步折叠与 Buchholz 的基本列 (EBO §5, 目标层 $u=\nu$, 参数 $<\Omega_{\nu+2}$) 对照. 参数的共尾度要么是 $1$ 或 $\omega$, 要么是 $\Omega_{\mu+1}$ 且 $\mu\le\nu$:

| 情形 | 树 | Buchholz | 是否改变值 |
|---|---|---|---|
| $\psi(0)$ | $\Omega_\nu$, 其中 $\Omega_0=\omega$ | $\Omega_\nu$, 其中 $\Omega_0=1$ | 只在底部. $\nu=0$ 时树给 $\omega^{1+x}$, Buchholz 给 $\omega^x$ ($x<\varepsilon_0$), 两者只在有限的 $x$ 上不同, $\ge\omega^\omega$ 处一致 |
| 规则 4 $\psi(a+1)$ | $\psi(a)\cdot\omega$ | $\psi(a)\cdot n$ 之极限 | 相同 |
| 规则 5 ($\omega$) | 逐项 | 逐项 | 相同 |
| 规则 5 ($\Omega$), $\mu<\nu$ | 穿透 | 穿透 | 相同 |
| 规则 6, $\mu=\nu$ | $x_0=0$, $x_{k+1}=\psi_\nu(f\,x_k)$ | $\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(f\,\gamma_k)$ | 不改变. $x_1\ge\Omega_\nu=\gamma_0$ (树的 $\psi_\nu$ 恒 $\ge\Omega_\nu$), 两条链交错, 上确界相同 (要求 $\psi_\nu\circ f$ 在链上单调, 规范树满足) |

所以 [估计, 高置信度]: **在 Buchholz 标准形对应的树上, 树的一步折叠与 Buchholz 的 $\psi_\nu$ 同值** (数值上只差 $\Omega_0$ 带来的有限偏移). 需要的 [标准] 事实是 Buchholz 基本列在标准形上收敛到正确的值.

**例外是非标准形.** Buchholz 的 $\psi_\nu(\alpha)$ 由 $C_\nu(\alpha)$ 定义. 参数不在 $C_\nu(\alpha)$ 里时函数会**停滞**, 树没有这一机制. 例: [标准] Buchholz 的 $\psi_0(\Omega+\alpha)=\varepsilon_1$ 对一切 $\varepsilon_1\le\alpha\le\Omega$ 成立, 因为 $\varepsilon_1=\psi_0(\Omega\cdot2)$ 不在 $C_0(\Omega+\alpha)$ 里. 树按规则算: $\psi_0(\Omega+\varepsilon_1+1)=\varepsilon_1\cdot\omega$ (由引理 P 的同型归纳得 $\psi_0(\Omega+y)=\varepsilon_0\cdot\omega^{y}$). **树的 ψ 是 Buchholz 基本列规则在一切树上的无停滞延拓.** 这一点在 §5 起决定性作用.

## §4 直接折叠的压平定理 (差异 (d))

**定理 F (压平)**. 设 $p:\nu<\ell$. 定义 $a{\downarrow}\nu:\mathsf{Ord}_{\nu+1}$: `zero`/`suc`/`lim` 同态; 对 $\mathsf{lim}_j f$, 若 $j\le\nu$ 则保持 (逐点压平); 若 $j>\nu$ 则换成 $\mathsf{lim}_\nu(x\mapsto (f(\uparrow x)){\downarrow}\nu)$. 那么 `ψ< p a` 与一步折叠 `ψ< zero (a↓ν)` 是外延相同的树.
*证明.* 对 $a$ 归纳. 唯一非平凡的是 $j>\nu$: 左边走 `injᵇ`, 得 `lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)`; 右边层号恰为 $\nu$, 走 `injᶜ`, 得 `lfp (ψ< zero ∘ (f ∘ ↑)↓)`. 由归纳假设两者逐项相同. ∎

**语义**: $\psi_\nu(a)=\psi_\nu(a[\Omega_\mu\mapsto\Omega_{\nu+1}\ (\mu>\nu)])$. 直接折叠看不见 $\nu+1$ 以上的任何层. 特别地 $[\![\psi_\nu(\Omega_\mu)]\!]=\varepsilon_{\Omega_\nu+1}$ 对**一切** $\mu>\nu$ 成立. 与之对比, [标准] Buchholz 的 $\psi_\nu(\Omega_\mu)$ 在 $\mu>\nu+1$ 时经由 $\psi_{\mu-1}$ 的 $\gamma$-链: 例如 $\psi_0(\Omega_2)=\psi_0(\varepsilon_{\Omega+1})=\mathsf{BHO}$, $\psi_0(\Omega_\omega)=\mathsf{BO}$.

目标层为 0 时, 外延相等 `_≈_` ([Finite](Finite.lagda.md) §5) 足以陈述. 关系 `Lift a x` 表示 "$a$ 是可数树 $x$ 经若干次提升所得". 下面证明: 目标层 0 的折叠作用在任何提升上, 结果与来源层和证明都无关.

```agda
≈₀-refl : (a : Ord₀) → a ≈ a
≈₀-refl zero        = z≈
≈₀-refl (suc a)     = s≈ (≈₀-refl a)
≈₀-refl (lim f)     = l≈ (λ n → ≈₀-refl (f n))
≈₀-refl (limᵢ () f)

data Lift {ℓ} : Ord ℓ → Ord₀ → Set where
  zL : Lift zero zero
  sL : ∀ {a x} → Lift a x → Lift (suc a) (suc x)
  lL : ∀ {f : ℕ → Ord ℓ} {h : ℕ → Ord₀} → (∀ n → Lift (f n) (h n)) → Lift (lim f) (lim h)

Lift-refl : (x : Ord₀) → Lift x x
Lift-refl zero        = zL
Lift-refl (suc x)     = sL (Lift-refl x)
Lift-refl (lim f)     = lL (λ n → Lift-refl (f n))
Lift-refl (limᵢ () f)

Lift-↑ : ∀ {ℓ₁ ℓ₂} (q : ℓ₁ < ℓ₂) {a : Ord ℓ₁} {x : Ord₀} → Lift a x → Lift (↑ q a) x
Lift-↑ q zL     = zL
Lift-↑ q (sL h) = sL (Lift-↑ q h)
Lift-↑ q (lL h) = lL (λ n → Lift-↑ q (h n))

ψ-Lift : ∀ {ℓ ℓ′} (p : zero < ℓ) (p′ : zero < ℓ′) {a : Ord ℓ} {b : Ord ℓ′} {x y : Ord₀} →
         Lift a x → Lift b y → x ≈ y → ψ< p a ≈ ψ< p′ b
ψ-Lift p p′ zL      zL      z≈     = ≈₀-refl ω
ψ-Lift p p′ (sL ha) (sL hb) (s≈ e) = l≈ (iter-≈ (λ e′ → +-≈ (ψ-Lift p p′ ha hb e) e′) z≈)
ψ-Lift p p′ (lL ha) (lL hb) (l≈ e) = l≈ (λ n → ψ-Lift p p′ (ha n) (hb n) (e n))
```

$\psi^\mathsf{b}(x):=\psi_0(\uparrow x)$ 是可数参数上的标准 $\psi_0$, 其值为 $\omega^{1+x}$ (引理 P).

```agda
ψᵇ : Ord₀ → Ord₀
ψᵇ x = ψ< zero (↑ zero x)
```

提升后再取回需要一条传输引理 (对证明归纳, 不用 K):

```agda
coe∘coe₀ : ∀ {μ ℓ} (r : μ < ℓ) (x : Ord μ) → coe {p = r} {q = zero} (coe₀ {p = r} x) ≡ x
coe∘coe₀ zero      x = refl
coe∘coe₀ (suc r)   x = coe∘coe₀ r x
coe∘coe₀ (lim n r) x = coe∘coe₀ r x
```

**定理 F₀** [Agda]. 对任意后继层 $\mu+1$, 任意外层 $\ell$, 任意证明, 都有 $\psi_0(\Omega_{\mu+1})\approx\psi_0(\Omega_1)$, 提升前后皆然. 即直接折叠到第 0 层时, 一切 $\Omega_{\mu+1}$ 都只值 $\varepsilon_0$.

```agda
ψΩ-flat : ∀ {μ} (p : zero < suc μ) → ψ< p (Ω (suc μ)) ≈ ψ< zero (Ω n₁)
ψΩ-flat p with <-dec zero p
... | injᵃ ()
... | injᵇ r    = l≈ (iter-≈ (λ {x} {y} e →
                    ψ-Lift _ _ (Lift-↑ zero (Lift-↑ r (Lift-refl x))) (Lift-↑ zero (Lift-refl y)) e) z≈)
... | injᶜ refl = l≈ (iter-≈ (λ {x} {y} e →
                    ψ-Lift _ _ (Lift-↑ zero (Lift-refl x)) (Lift-↑ zero (Lift-refl y)) e) z≈)

ψΩ-flat↑ : ∀ {μ ℓ} (p : zero < ℓ) (q : suc μ < ℓ) → ψ< p (↑ q (Ω (suc μ))) ≈ ψ< zero (Ω n₁)
ψΩ-flat↑ p q with <-dec (<-trans zero q) p
... | injᵃ ()
... | injᵇ r    = l≈ (iter-≈ (λ {x} {y} e → ψ-Lift _ _
                    (subst (λ z → Lift (↑ q (↑ zero z)) x) (sym (coe∘coe₀ (<-trans zero q) (↑ r x)))
                      (Lift-↑ q (Lift-↑ zero (Lift-↑ r (Lift-refl x)))))
                    (Lift-↑ zero (Lift-refl y)) e) z≈)
... | injᶜ refl = l≈ (iter-≈ (λ {x} {y} e → ψ-Lift _ _
                    (subst (λ z → Lift (↑ q (↑ zero z)) x) (sym (coe∘coe₀ (<-trans zero q) x))
                      (Lift-↑ q (Lift-↑ zero (Lift-refl x))))
                    (Lift-↑ zero (Lift-refl y)) e) z≈)
```

特例: [Finite](Finite.lagda.md) §2 的 `chain₂` 与 `chain₁`. 树的 $\psi_0(\Omega_2)$ 与 $\psi_0(\Omega_3)$ 都外延等于 $\psi_0(\Omega_1)$, 值为 $\varepsilon_0$:

```agda
_ : ψ< (suc zero) (Ω n₂) ≡ lim chain₂
_ = refl

ψΩ₂≈ψΩ₁ : ψ< (suc zero) (Ω n₂) ≈ ψ< zero (Ω n₁)
ψΩ₂≈ψΩ₁ = ψΩ-flat (suc zero)

ψΩ₃≈ψΩ₁ : ψ< (suc (suc zero)) (Ω n₃) ≈ ψ< zero (Ω n₁)
ψΩ₃≈ψΩ₁ = ψΩ-flat (suc (suc zero))
```

作为对照, [Finite](Finite.lagda.md) §3 的忠实折叠 `ψᴱ` 在同一位置用 $\gamma$-链经过 $\psi_1$ (即 `ψᴱ zero : Ord 2 → Ord 1`), 起点是 $\Omega_1$:

```agda
_ : ψᴱ (suc zero) (Ωᴱ n₂)
  ≡ lim (λ n → ψᴱ (suc zero) (↑ zero (iter (λ y → ψᴱ zero (↑ zero y)) (Ωᴱ n₁) n)))
_ = refl
```

## §5 跨层: `ψ₀` 是复合与对角, 不是 Buchholz 的直接折叠

```agda
_ : ∀ {ℓ} (a : Ord (suc ℓ)) → ψ₀ a ≡ ψ₀ (ψ< zero a)
_ = λ a → refl

_ : ψ₀ {n₂} (Ω n₂) ≡ ψ< zero (ψ< zero (Ω n₂))
_ = refl
```

语义方程. 第三行用了定理 F, 并注意 $b:\mathsf{Ord}_{\lambda[n]+1}$ 时 $\psi_0^{(\lambda[n]+1)}(b)=\psi_0^{(\lambda[n])}(\psi_{\lambda[n]}(b))$:

$$
\psi_0^{(0)}(a)=a,\qquad
\psi_0^{(\ell+1)}=\psi_0^{(\ell)}\circ\psi_\ell,\qquad
\psi_0^{(\lambda)}(a)=\sup_n\ \psi_0^{(\lambda[n]+1)}\big(a{\downarrow}\lambda[n]\big).
$$

**有限层: 复合正是靠 "无停滞" 才有用.** [标准] 在 Buchholz 体系里, $\psi_0$ 单调不减且 $\psi_1(\alpha)<\Omega_2$. 所以对一切 $\alpha$ 有 $\psi_0(\psi_1(\alpha))\le\psi_0(\Omega_2)=\mathsf{BHO}$, 等号对一切 $\alpha\ge\Omega_2$ 成立 (因为 $\varepsilon_{\Omega+1}\le\psi_1(\alpha)<\Omega_2$, 而 $\psi_0$ 在 $[\varepsilon_{\Omega+1},\Omega_2]$ 上恒为 $\mathsf{BHO}$). 因此 Buchholz 自己的复合 $\psi_0\circ\psi_1\circ\cdots$ 永远卡在 $\mathsf{BHO}$. 至于问题 "Buchholz 里 $\psi_0(\psi_1(\alpha))=\psi_0(\alpha)$ 吗": 在 $\alpha=\Omega_2$ 处成立, 在 $\alpha>\Omega_2$ 处不成立 (例如 $\psi_0(\Omega_2+1)=\mathsf{BHO}\cdot\omega$).

树的复合不卡, 因为树的 $\psi_0$ 不停滞. 例子 [语义]: $\psi_1(\Omega_2+1)$ 的树是 $E\cdot\omega$, 其中 $E=\varepsilon_{\Omega+1}$ 是链树. 再看 $\psi_0(E+\Omega)$: 它的链是 $z\mapsto\psi_0(E+z)$ 且 $\psi_0(E+y)=\mathsf{BHO}\cdot\omega^{y}$, 所以 $\psi_0(E+\Omega)=\varepsilon_{\mathsf{BHO}+1}$. 于是

$$
\text{树}\ \psi_0(\psi_1(\Omega_2+1))\ \ge\ \varepsilon_{\mathsf{BHO}+1}\ >\ \mathsf{BHO}\cdot\omega=\psi_0^{\mathrm{B}}(\Omega_2+1)\ >\ \mathsf{BHO}=\psi_0^{\mathrm{B}}(\psi_1^{\mathrm{B}}(\Omega_2+1)).
$$

在非标准参数上, 树的值**大于** Buchholz 的值. 这正是 Wikipedia 所述 Madore 的 "迭代 (非同时) 折叠": $\psi_0$ 把 $\psi_1$ 的输出 "重新注入" 为可用的积木 ("doubly impredicative", 例如 $\psi(\psi_1(1)+1)=\varepsilon_{\mathsf{BHO}+1}$). Kovács 的 gist 明说自己的折叠是 "based on Madore's ψ … the iterated (non-simultaneous) collapse". BTBO 的 `ψ<`/`ψ₀` 与 Kovács 的 `ψ<`/`ψ` 结构逐字相同, 只是把逐层的闭包从幂 (`lfp (Ω ^ᵁ_)`, `lfp (ψ< p a ^ᵁ_)`) 换成了加法 (`Ω _`, `lfp (ψ< p a +_)`).

## §6 数值: $\psi^1(0)$ 与 $\psi^2(0)$

记 $\Psi(\ell):=[\![\psi_0^{(\ell)}(\Omega_\ell)]\!]$, 于是 $[\![\psi^{k+1}(0)]\!]=\Psi(\mathsf{ord}^\mathsf{D}(\psi^k(0)))$. 由 §5 与引理 C:

$$
\Psi(0)=\omega,\qquad \Psi(\nu+1)=[\![\psi_0^{(\nu)}(\varepsilon_{\Omega_\nu+1})]\!],\qquad \Psi(\lambda)=\sup_n\Psi(\lambda[n]+1).
$$

最后一式: 由定理 F, $\psi_{\lambda[n]}(\Omega_\lambda)$ 的值是 $\varepsilon_{\Omega_{\lambda[n]}+1}$. $\Omega_\lambda$ 中层号 $\le\lambda[n]$ 的分量被穿透, 其余的全部压成同一条链.

- $\Psi(1)=\varepsilon_0$ [语义, 由引理 P/C 严格得到]. 这与 Buchholz 的 $\psi_0(\Omega_1)$ 相同.
- $\Psi(2)=[\![\psi_0(\varepsilon_{\Omega+1})]\!]=\sup_k\psi_0(\psi_1^k(0))=\mathsf{BHO}$ [§3 + 标准]. 链上的 $\psi_1^k(0)$ 都是 Buchholz 标准形, 一步折叠在其上与 Buchholz 同值. 这与 Buchholz 的 $\psi_0(\Omega_2)$ 相同. 注意: 树的直接折叠 $\psi_0(\Omega_2)$ 只有 $\varepsilon_0$ (§4); 这里是复合把它救了回来.
- $\Psi(m)$, $m<\omega$ [估计]: $\psi_0^{\mathrm{B}}(\Omega_m)\le\Psi(m)<\psi_0^{\mathrm{B}}(\Omega_{m+2})$. 下界的依据是无停滞复合在标准形上不小于直接折叠 (在 $\Omega_2,\ \Omega_2+1,\ \Omega_2+\Omega,\ \Omega_2\cdot2$ 处逐一验证过). 上界的依据是有限多个基数的迭代折叠体系与同样多基数的 Buchholz 体系强度相当 (Wikipedia: 迭代与同时两种写法 "both equal ψ(ζ_{Ω+1})", 加到 $\Omega_\omega$ 时 "essentially equivalent to Buchholz's"). 最终结论只用到较弱的形式: **$\Psi(m)<\mathsf{BO}$, 且 $\sup_m\Psi(m)=\mathsf{BO}$**.

**$\psi^2(0)$.** 层是 $\mathsf{ord}^\mathsf{D}\,\omega$, 基本列 $g=0,2,5,9,\ldots$. 展开定义 [Agda]:

```agda
_ : ψⁿ 1 ≡ ω
_ = refl

_ : ψⁿ 2 ≡ lim (λ n → ψ₀ (ψ< (fl n) (Ω ℓω)))
_ = refl

_ : Ω ℓω ≡ lim (λ k → ↑ (fl k) (Ω (g k)))
_ = refl
```

第 $n$ 个近似项是 $\psi_0^{(g n)}(\psi_{g n}(\Omega_{\ell_\omega}))$. 其中 $\psi_{g n}$ 是从极限层出发的直接折叠, 所以分量 $k>n$ 全部走 `injᵇ`/`injᶜ` 并被压平. $n=0$ 时目标层就是 0, 可以完整地机器检验: 近似项 $A_0$ 外延等于 $(\psi^\mathsf{b}(\omega),\varepsilon_0,\varepsilon_0,\ldots)$ 的极限, 值 $\varepsilon_0=\Psi(1)$ [Agda]:

```agda
A₀ : Ord₀
A₀ = ψ< (fl 0) (Ω ℓω)

A₀-shape : Ord₀
A₀-shape = lim λ { zero → ψᵇ ω ; (suc k) → ψ< zero (Ω n₁) }

A₀≈ : A₀ ≈ A₀-shape
A₀≈ = l≈ λ { zero    → ψ-Lift _ _ (Lift-↑ (fl 0) (Lift-refl ω)) (Lift-↑ zero (Lift-refl ω)) (≈₀-refl ω)
           ; (suc k) → ψΩ-flat↑ (fl 0) (fl (suc k)) }
```

一般的 $n$ [语义 + 定理 F]: 近似项 $=\psi_0^{(g n)}(\varepsilon_{\Omega_{g n}+1})=\Psi(g\,n+1)$. 所以

$$
[\![\psi^2(0)]\!]=\sup_n\Psi(g\,n+1)=\sup\{\Psi(1),\Psi(3),\Psi(6),\ldots\}=\psi_0(\Omega_\omega)=\mathsf{BO}.
$$

**偏差 (d) 在这里不改变数值.** 树的第 $n$ 项约为 $\psi_0(\Omega_{g n+1})$, Buchholz 的基本列第 $n$ 项是 $\psi_0(\Omega_{g n})$. 两者互相共尾. 被压平跳过的那些层 ($g\,n+1$ 到 $g(n+1)-1$) 在取上确界时无关紧要.

## §7 越过 $\Omega_\omega$: 压平吞掉一切

**$\Omega_{\omega+1}$.** 设 $\ell=\lambda+1$, $\lambda=\mathsf{ord}^\mathsf{D}\omega$. 则 $\psi_0^{(\lambda+1)}(\Omega_{\lambda+1})=\psi_0^{(\lambda)}(E)$, 其中 $E=\psi_\lambda(\Omega_{\lambda+1})=\varepsilon_{\Omega_\omega+1}$ 是链树, $x_{j+1}=\Omega_\omega\omega^{x_j}$. 由 §5 的第三式,

$$
\psi_0^{(\lambda)}(E)=\sup_n\psi_0^{(g n+1)}(E{\downarrow}g\,n),\qquad E{\downarrow}g\,n\ \text{的值}=\varepsilon_{\Omega_{g n+1}+1}.
$$

(逐项检查: $\Omega_\omega{\downarrow}g\,n=\Omega_{g n+1}$; $\Omega_\omega\omega^{\Omega_\omega}$ 压平为 $\Omega_{g n+1}\omega^{\Omega_{g n+1}}$; 依此类推.) 所以 $\Psi(\omega+1)=\sup_n\Psi(g\,n+2)=\mathsf{BO}$. 而 [标准] Buchholz 的 $\psi_0(\Omega_{\omega+1})=\psi_0(\varepsilon_{\Omega_\omega+1})$ 是 Takeuti–Feferman–Buchholz 序数, 远大于 $\mathsf{BO}$.

同理, 树的 $\psi_0^{(\omega)}(\Omega_\omega+1)=\sup_n\psi_0^{(g n+1)}(\Omega_{g n+1}+1)=\mathsf{BO}$; Buchholz 是 $\mathsf{BO}\cdot\omega$. 又如树的 $\psi_0^{(\omega)}(\Omega_\omega+\Omega)=\mathsf{BO}$; Buchholz 是 $\varepsilon_{\mathsf{BO}+1}$. 原因是 Buchholz 的 $\psi_0$ 把 $\Omega_\omega$ 当作参数里的常量保留, 而树的极限层 `ψ₀` 按定义是对 $\lambda[n]$ 的对角. 每一项都先把 $\Omega_\lambda$ 换成 $\Omega_{\lambda[n]+1}$ 再折叠, 从不把 $\Omega_\lambda$ 当常量.

**一般层** [估计]. 对任意 $\mu\ge\omega$, $\Psi(\mu)=\mathsf{BO}$. 论证: 沿 $\mu$ 的 `Ordᴰ` 树下降时只有两种步骤, 后继层做一步折叠, 极限层做压平, 每条路径在有限步内到达有限层 $m$. 到达时手里的树属于 $\mathsf{Ord}_m$. 它的值是一个只用有限多层的 Buchholz 式项的值, 被压平的高层只以链的形状 "虚拟地" 留在树里. 树里也不含大于结果本身的可数常量: 层号从不作为可数结构进入树, 可数值只由第 0 层的链产生. 所以每条路径的值都 $<\mathsf{BO}$ (§6 的有限层上界), 上确界 $\le\mathsf{BO}$. 反过来, 每条路径都穿过某个 $\ge\omega$ 的极限层, 在那里取上确界得到 $\ge\mathsf{BO}$.

于是 $\mathsf{ord}^\mathsf{D}(\psi^2(0))$ 的层号 $=\mathsf{BO}\ge\omega$, 得 $[\![\psi^3(0)]\!]=\Psi(\mathsf{BO})=\mathsf{BO}$. 归纳下去:

$$
[\![\psi^0(0)]\!]=0,\quad [\![\psi^1(0)]\!]=\omega,\quad [\![\psi^k(0)]\!]=\mathsf{BO}\ (k\ge2),\qquad [\![\mathsf{BTBO}]\!]=\mathsf{BO}=\psi_0(\Omega_\omega).
$$

**旁注 (Kovács 的标签).** gist 的 `ex13 = ψ ω₀ (Ω ω₀) -- ID<ω` 与上面的 $\Psi(\omega)=\mathsf{BO}=|\mathrm{ID}_{<\omega}|$ 相符. 但 `ex15 = ψ (ω₀ + 1) 0 -- TFB`, `ex16 -- ID<ω^ω`, `ex17 -- ID<ε₀` 处在同样的压平机制下 (gist 的 `ψ<` 的 `injᵇ` 分支与 `ψ (lim l lw)` 和 BTBO 逐字相同). 按本节论证它们都只有 $|\mathrm{ID}_{<\omega}|$ [估计]. BTBO 继承了这些标签的乐观.

## §8 Madore 与 Buchholz 是否 "已追平" (问题 C)

**单个 Ω.** [标准] Madore 的 $\psi$: $C(\alpha)$ 由 $0,1,\omega,\Omega$ 在 $+,\times,\exp$ 与 $\psi{\restriction}\alpha$ 下生成. 数值是 $\psi(0)=\varepsilon_0$, $\psi(\Omega)=\zeta_0$, $\psi(\Omega^\Omega)=\Gamma_0$, $\psi(\varepsilon_{\Omega+1})=\mathsf{BHO}$, 此后恒定. Buchholz 的 $\psi_0$ 只对 $+$ 封闭: $\psi_0(0)=1$, $\psi_0(\Omega)=\varepsilon_0$, $\psi_0(\Omega^\Omega)=\Gamma_0$, $\psi_0(\varepsilon_{\Omega+1})=\psi_0(\Omega_2)=\mathsf{BHO}$. 两者在底部差一层 $\varepsilon$/$\zeta$ 式的平移, 到 $\Gamma_0$ 一带已对齐, 并在同一个上限 $\mathsf{BHO}$ 处停住. 停住的原因相同: 参数 $\ge\varepsilon_{\Omega+1}$ 时生成不了新的 $<\Omega$ 的元素, 要再往上必须引入 $\Omega_2,\Omega_3,\ldots$ 和对应的 $\psi_1,\psi_2,\ldots$. 用户的猜想 "在这个量级 Madore 与 Buchholz 已追平" 在逐层闭包这一维度上**成立**: 闭包用 $+$ 还是 $\exp$ 只影响 $\mathsf{BHO}$ 以下的刻度, 不影响极限.

**真正起作用的是迭代结构.** 树的第 $\nu$ 层一步折叠是 Buchholz 式的 $\psi_\nu$ (§3; Kovács 的是 Madore 式的, 区别同上, 无关紧要). 跨层组织则是 Madore/Kovács 的迭代折叠: 有限层上 "复合 + 无停滞" 与 Buchholz 的同时定义强度相当; 极限层上则是对角加压平. Wikipedia 恰好指出: 要处理无穷多个折叠函数需要 "simultaneous rather than downward induction". 树在极限层用的是向下的对角, 于是 $\Omega_\lambda$ 作为常量的信息丢失 (§7). 所以对问题 C 的回答是: 在第 $\nu$ 层, 树的行为像 Buchholz 的 $\psi_\nu$ (只看一步折叠时). 但目标层低于来源层减一时, 它像 "只认识 $\Omega_{\nu+1}$ 的逐层 Madore/Buchholz", 即定理 F.

## §9 让 `ψ<` 忠实于 Buchholz 需要改什么 (问题 D)

按对数值的影响从大到小:

1. **规则 6 的链要经过共尾层的直接折叠** (修正压平, 必要). `injᵇ` 分支要像 `ψᴱ` 那样用 $\gamma_{k+1}=\psi_j(f\,\gamma_k)$, 其中 $\psi_j$ 是 `limᵢ` 节点自带证明 $q:j<\ell$ 给出的直接折叠 `ψᴱ q` (§4 末的 `refl` 对照).
2. **`ψ₀` 改为直接折叠** (必要). `ψ₀ {ℓ} = ψᴱ (0<ℓ)` ($\ell\ne0$ 时 `z<nz` 给出证明), 不再用复合与对角. 只改第 1 条而保留对角时, 极限层的 `ψ₀` 仍是 $\sup_n\psi_0^{(\lambda[n])}(\cdots)$ 加上有限层的无停滞复合, 其值无法从 Buchholz 体系直接读出. 只改第 2 条时 $\psi_0(\Omega_2)$ 就已退化成 $\varepsilon_0$.
3. $\Omega_0:=1$ (`Ωᴱ zero = suc zero`) 与链起点 $\Omega_j$: 只是外观修正, 不改变 $\ge\varepsilon_0$ 的值, 但能让树与 EBO 的基本列**逐项**相同, 而对齐证明 ([Finite](Finite.lagda.md) §7) 需要逐项相同.
4. 规则 4, 规则 5 (两种): 已经一致.

**用 `ψᴱ` 重建的对角线.** $x_{k+1}=\psi^\mathsf{E}_0(\Omega^\mathsf{E}_{\mathsf{ord}^\mathsf{D}x_k})$, 依次给出 $1,\ \varepsilon_0,\ \psi_0(\Omega_{\varepsilon_0}),\ldots$. 它的极限是 $\alpha\mapsto\psi_0(\Omega_\alpha)$ 的最小不动点, 即扩展 Buchholz 记号中的 $\psi_0(\Omega_\Omega)$ [标准 + §1 的累积和论证]. 这时标签可以干净地陈述, 但 "可证" 分两层:

- **可在 Agda 中证明的**: 对齐定理 ([Finite](Finite.lagda.md), [Omega1](Omega1.lagda.md) 的路线) 把 EBO 的项 $\psi_0(\Omega_{t})$ 嵌进树并保持基本列, 从而得到 FGH 等式. 但还有一处障碍: `ordᴰ` 的累积和让层号 $\mathsf{ord}^\mathsf{D}x$ 的基本列与 EBO 中 $\Omega_t$ 下标的基本列**不逐项相同**, 只互相共尾. 所以要么把 `ordᴰ` 换成保持基本列的嵌入 (需要单调性另行保证), 要么把对齐定理放宽为共尾/优超形式.
- **只能引用的**: EBO 基本列在标准形上收敛到正确的集合论值. 这是表记系统的元定理, 不在 Agda 里.

## §10 结论与边界

**已机器检验 [Agda]:**

- 一步折叠 `ψ< zero` 从不走 `injᵇ` (`one-step`).
- 目标层 0 的直接折叠对任意后继层 $\mu+1$ (含可数序数层), 无论是否提升, 都有 $\psi_0(\Omega_{\mu+1})\approx\psi_0(\Omega_1)$ (`ψΩ-flat`, `ψΩ-flat↑`). 特例 $\psi_0(\Omega_2)\approx\psi_0(\Omega_3)\approx\psi_0(\Omega_1)$.
- $\psi^1(0)\equiv\omega$; $\psi^2(0)$ 展开为对 $n$ 的直接折叠之极限; 其第 0 项外延等于 $(\psi^\mathsf{b}(\omega),\varepsilon_0,\varepsilon_0,\ldots)$ 的极限 (`A₀≈`).
- 复合: `ψ₀ {suc ℓ} a ≡ ψ₀ (ψ< zero a)`; $\psi_0^{(2)}(\Omega_2)\equiv\psi_0(\psi_1(\Omega_2))$; 以及 `ψᴱ` 的 $\gamma$-链经过 $\psi_1$ 的对照.

**由语义严格得到 [语义]:** 引理 P ($\psi_\nu(\uparrow x)=\Omega_\nu\omega^{x}$); 引理 C; 定理 F (压平, 对一般目标层; 其形式化需要带 `limᵢ` 的外延相等, 本文只做了目标层 0); $\Psi(0)=\omega$; $\Psi(1)=\varepsilon_0$; 累积和不改变对角线上的层号值.

**依赖标准事实 [标准]:** $\Psi(2)=\mathsf{BHO}$ (另需树的一步折叠在 Buchholz 标准形上与 Buchholz 同值, §3, 高置信度); Buchholz 复合 $\psi_0\circ\psi_1\le\mathsf{BHO}$; Madore 与 Buchholz 的单 Ω 数值.

**估计 [估计]:**

| 断言 | 置信度 | 依赖 |
|---|---|---|
| 树的一步折叠 = Buchholz 基本列的无停滞延拓, 在标准形上同值 | 高 (~90%) | §3 逐条对照; 差异 (a)(b) 的交错论证 |
| $[\![\psi^2(0)]\!]=\psi_0(\Omega_\omega)=\mathsf{BO}$ | 高 (~85%) | 有限层: $\Psi(m)<\mathsf{BO}$ 且 $\sup_m\Psi(m)=\mathsf{BO}$ |
| $[\![\psi^k(0)]\!]=\mathsf{BO}$ ($k\ge2$), $[\![\mathsf{BTBO}]\!]=\mathsf{BO}$ | 中高 (~80%) | 上一条 + 定理 F + §7 的路径论证 (每条下降路径终止于有限层, 无可数常量泄漏) |
| $\mathsf{BTBO}\ne\psi(\Omega_\Omega)$ (标签不可信) | 高 (~90%) | 只需 §7 的上界方向 |
| Kovács gist 的 ex15–ex17 标签同样偏高 | 中 (~70%) | 同一机制; 未逐一展开 |

**什么能把估计变成定理.**
(1) 把定理 F 形式化到一般目标层. 这需要一个带 `limᵢ` 分支的外延相等 (类似 [Omega1](Omega1.lagda.md) §2 的 `Eq R`, 但层号与证明可变), 加上 `<-dec` 的非自反性 (`a < a → ⊥`, 尚未在 `BoundedTrich` 中证明).
(2) 有限层的上界 $\Psi(m)<\mathsf{BO}$: 把树的有限层体系对齐到 EBO 项上, 在共尾/优超意义下证明 `ψ₀ {m}` 的每个值落在某个 $\psi_0(\Omega_{m+c})$ 项之下. 这是 Align 路线的自然延伸.
(3) 数值实验无效: 这些序数的 FGH 在 $n\le2$ 时退化 (例如 $f_\alpha(1)=2$ 对一切 $\alpha$), 而在 $n\ge3$ 时不可算.

**对仓库的含义.** 现有标签 "$\mathsf{BTBO}=\psi(\Omega_\Omega)$" 应降为 "$\psi_0(\Omega_\omega)$ (估计), 原标签不成立 (高置信度)". "布劳威尔树壁垒" 的叙事 (卡在 $\psi(\Omega_\Omega)$) 需要重新表述: 现有构造在 $\Omega_\omega$ 处就已经被极限层的对角压平卡住. 换成 `ψᴱ` (§9 的第 1、2 条) 后, 对角线的极限才是 $\psi_0(\Omega_\Omega)$.
