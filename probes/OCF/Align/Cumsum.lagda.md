# 消去 cumsum: 层号与表记基本列的逐项一致

> 对齐纲领 (见 [probes/README.md](../../README.md)) 要证"树序数的基本列恰是 [EBO](EBO.lagda.md) 的基本列". 在 $\Omega$ 的下标是极限时, EBO 的规则是 $\Omega_u[n]=\Omega_{u[n]}$; 树这边的层号却是 [BTBO](../../../src/OCF/BTBO.lagda.md) 的 `ordᴰ x`, 它把树 $x$ 的每一个 `lim` 都换成累积和 (`cumsum`), 于是两边只是共尾一致, 不是逐项一致. 本文研究能否消去 `cumsum`, 而不放弃 `--safe --without-K`、无公设、下标的有界可判定比较 (壁垒定理 [Barrier](../Barrier.lagda.md) 说下标必须仍是可数树) 和结构递归的 FGH.
>
> 结论先说:
>
> 1. **单调性的唯一用户是有界三歧性**. $\Omega$ 在极限层的定义和层间提升 `↑` 只需要"前驱集合的包含" $\sqsubseteq$, 不需要单调 (§1, 已编译). 反过来, 有界三歧性迫使一个极限层的各项前驱两两可比: 消去 `cumsum` 等价于让被嵌入的基本列项在结构序下两两可比. `cumsum` 是"不管原序列是否可比, 硬造一条嵌套的序列".
> 2. **候选 A (构造即单调) 在 $\psi_0$ 片段 ($\varepsilon_0$) 完全成立**: 折叠可以直接写进下标类型, 与自己的单调性互递归, 不用任何填充; 层号的 $\Omega$ 基本列逐项是 $\Omega_{u[n]}$ (§2.2–2.3, 已编译). **对一般的 $\psi^\mathsf{E}$ 不成立**: $\psi^\mathsf{E}$ 对结构序不单调, 有 `refl` 级的反例 (§2.4). 卡点精确在规则 6: $a\prec\lim_j f$ 经过分支 $x$, 而 $x$ 不在 $\gamma$-链之下.
> 3. **候选 B 的最弱可用证据是 $\sqsubseteq$-步进** (§3.1, 已编译; 有界三歧性、树族、$\Omega$、忠实折叠全部照搬). 它允许常值步与极限的重表示, 但不解决吸收问题: 优势序列 (cumsum 当上界) 被 `absorb-fails` 形式地否定 (§3.2); 把累积和写进 `lim` 的语义则让树族的归纳递归定义过不了停机检查 (§3.4, 记录了错误).
> 4. **候选 C (按需填充) 不可计算**: 判定结构序 (哪怕只判 $0\prec x$) 推出 LPO (§4, 已编译).
> 5. 现状比题设更糟: `ordᴰ` 对非加法主数的树改变**值**, 不只改基本列. `ordᴰ (ω + ω)` 的值是 $\omega^2$, 已编译出 $\omega\cdot 3$ 在它之下的结构见证 (§0). 所以表记那边不可能写出镜像 `ordᴰ` 的规则.
>
> 推荐 (§7): 下标类型换成 $\sqsubseteq$-步进的 `Ordʷ` (树侧小改, 表记侧不动, 无损); 层号不再由 `ordᴰ` 从树事后计算, 而由折叠**直接构造**为带单调证据的下标 (ψ⁰ᴰ 的模式). $\varepsilon_0$ 片段已完成; 一般情形欠一条引理 ("规则 6 的分支落在 $\gamma$-链之下"), 它是 Buchholz 标准形条件在树上的影子, 是本文留下的开放问题.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Cumsum where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Barrier using (nat; nat-mono; LPO)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc; s<s)
open BoundedTrich renaming (_+_ to _+ᴰ_; +-mono to +ᴰ-mono)
open Ord-Ord
open import OCF.Align.Finite
  using (Ωᴱ; ψᴱ; _≈_; z≈; s≈; l≈; NoLᵢ; nz; ns; nl; ≈-refl; ≈-trans; +-≈; ↑-≈; ψᴱ-≈;
         P₀; T₀; ψ⁰; emb₀; embP₀; cω; cof₀; fs₀; Shape; corr)
```

约定: `_<_` 是 `Ordᴰ` 的结构序 (BTBO), `_+ᴰ_` 是 `Ordᴰ` 上的加法, `_+_` 是树族 `Ord ℓ` 上的加法.

## §0 问题与现状

BTBO 的层号嵌入 $\mathsf{ord}^\mathsf{D}(\lim f)=\lim(\mathrm{cumsum}(\mathsf{ord}^\mathsf{D}\circ f))$, 其中 $\mathrm{cumsum}\,g\,0=g\,0$, $\mathrm{cumsum}\,g\,(n+1)=\mathrm{cumsum}\,g\,n+(g(n+1))^+$. 最简单的例子 $\omega=\lim(n\mapsto n)$: 层号的各项是 $0,2,5,9,\ldots$, 于是树的 $\Omega_\omega$ 的基本列是 $\Omega_0,\Omega_2,\Omega_5,\ldots$, 而 EBO 的是 $\Omega_\omega[n]=\Omega_n$.

```agda
natᴼ : ℕ → Ord₀
natᴼ zero    = zero
natᴼ (suc n) = suc (natᴼ n)

ω₀ : Ord₀
ω₀ = lim natᴼ

_ : cumsum (ordᴰ ∘ natᴼ) 1 ≡ nat 2
_ = refl

_ : cumsum (ordᴰ ∘ natᴼ) 2 ≡ nat 5
_ = refl

_ : Ω (ordᴰ ω₀) ≡ lim (λ n → ↑ (f<l n) (Ω (cumsum (ordᴰ ∘ natᴼ) n)))
_ = refl
```

**问题比"只差基本列"更严重.** BTBO 原文说累积和"可能会使某些基本列的极限值往上偏移". 对加法不可分解 (主数) 的极限这不发生, 对一般极限则发生: $\omega\cdot2=\lim(\omega+n)$ 的累积和第 $k$ 项含 $k+1$ 份 $\omega$, 极限是 $\omega^2$. 下面是 $\omega\cdot 3$ 位于 $\mathsf{ord}^\mathsf{D}(\omega\cdot 2)$ 之下的结构见证 (第 2 项 $=(\omega+(\omega+2))+(\omega+3)$, 右加数 $\omega<\omega+3$):

```agda
D₀ : Ordᴰ
D₀ = ordᴰ ω₀

overshoot : (D₀ +ᴰ suc (suc D₀)) +ᴰ D₀ < ordᴰ (ω₀ + ω₀)
overshoot = lim 2 (+ᴰ-mono (suc (suc zero)))
```

所以树那边的 "$\Omega_{\omega\cdot2}$" 实际是 $\Omega_{\omega^2}$. BTBO 的对角线 $\psi^n$ 只把 $\psi$ 值 (主数) 当层号, 值不受影响; 但 EBO 的下标是任意项 ($\Omega_{\omega\cdot2}$, $\Omega_{\Omega+\omega}$ 之类), 对齐它们时值也错. 同一个例子说明 $\mathsf{ord}^\mathsf{D}$ 与 $+$ 不交换 ($\mathsf{ord}^\mathsf{D}\omega+\mathsf{ord}^\mathsf{D}\omega$ 的值是 $\omega\cdot2$): 表记那边若想镜像 $\mathsf{ord}^\mathsf{D}$, 规则必须改变项的值, 这样的"镜像"不再是同一个表记. 修复只能在树侧.

## §1 单调性被谁消费

BTBO 的 `Ordᴰ` 要求 `lim` 的序列单调. 除了 `cumsum-mono` 自身的证明 (经 `z<nz`), 单调性只有两个用户: `f<l` (给 $\Omega$ 的极限分支提供 $f\,n<\lim f$, 以便提升 `↑`), 和有界三歧性 `<-dec` 的 `lim`/`lim` 情况. 本节说明前者其实不需要单调, 后者需要的恰好是"可比".

**前驱包含** $a\sqsubseteq b$: $a$ 的每个结构前驱都是 $b$ 的结构前驱. 语义版 `Sim` 有 `Ordᴰ` 的负出现, 不能放进构造子; 归纳版 $\sqsubseteq$ 是严格正的, 两者等价 (`⊑→Sim`, `Sim→⊑`). 所以 $\sqsubseteq$ 是"能沿它搬运 $c<a$ 的证明"的最弱的严格正关系.

```agda
infix 4 _⊑_
data _⊑_ : Ordᴰ → Ordᴰ → Set where
  z⊑ : ∀ {b} → zero ⊑ b
  s⊑ : ∀ {a b} → a < b → suc a ⊑ b
  l⊑ : ∀ {f : ℕ → Ordᴰ} {m : monotonic f} {b} → (∀ n → f n ⊑ b) → lim f m ⊑ b

Sim : Ordᴰ → Ordᴰ → Set
Sim a b = ∀ {c} → c < a → c < b

⊑→Sim : ∀ {a b} → a ⊑ b → Sim a b
⊑→Sim (s⊑ p) zero      = p
⊑→Sim (s⊑ p) (suc q)   = <-trans q p
⊑→Sim (l⊑ h) (lim n q) = ⊑→Sim (h n) q

Sim→⊑ : ∀ {a b} → Sim a b → a ⊑ b
Sim→⊑ {a = zero}    s = z⊑
Sim→⊑ {a = suc a}   s = s⊑ (s zero)
Sim→⊑ {a = lim f m} s = l⊑ (λ n → Sim→⊑ (λ q → s (lim n q)))
```

**$f\,n\sqsubseteq\lim f$ 对任意序列成立**, 证明只用 `_<_` 的 `lim` 构造子, 不碰单调性:

```agda
f⊑lim : ∀ {f : ℕ → Ordᴰ} {m : monotonic f} n → f n ⊑ lim f m
f⊑lim n = Sim→⊑ (lim n)
```

**层间提升只需要前驱包含.** BTBO 的 `↑ p` 只用 $p$ 去把 `limᵢ q` 的 $q:i<\ell_1$ 送成 $i<\ell_2$, 所以它对任意 `Sim` 都写得出来; 于是 $\Omega$ 在极限层可以直接用 `lim n` 当提升证据:

```agda
↑ˢ : ∀ {ℓ₁ ℓ₂} → Sim ℓ₁ ℓ₂ → Ord ℓ₁ → Ord ℓ₂
↑ˢ s zero       = zero
↑ˢ s (suc a)    = suc (↑ˢ s a)
↑ˢ s (lim f)    = lim (↑ˢ s ∘ f)
↑ˢ s (limᵢ q f) = limᵢ (s q) (↑ˢ s ∘ f ∘ coe)

Ωˢ : (ℓ : Ordᴰ) → Ord ℓ
Ωˢ zero      = ω
Ωˢ (suc ℓ)   = limᵢ zero (↑ zero)
Ωˢ (lim f _) = lim (λ n → ↑ˢ (lim n) (Ωˢ (f n)))
```

**必要条件.** 若一列层号都包含于同一个 $c$, 有界三歧性就迫使它们的前驱两两可比:

```agda
comparable : ∀ {f : ℕ → Ordᴰ} {c} → (∀ n → f n ⊑ c) →
             ∀ {a b n m} → a < f n → b < f m → a < b ⊎ b < a ⊎ a ≡ b
comparable h p q = <-dec (⊑→Sim (h _) p) (⊑→Sim (h _) q)
```

推论: 要让层号 $\lim F$ 的第 $n$ 项**就是** $u[n]$ 的树 (从而 $\Omega_{\lim F}[n]=\Omega_{u[n]}$), 必须有 $F\,n\sqsubseteq\lim F$ (由 `f⊑lim` 自动成立), 于是各 $u[n]$ 的树的前驱必须两两可比. 树的结构序是内涵的 (前驱就是字面出现的子树), 两个值相等而表示不同的树的前驱一般不可比, 所以这是关于**树怎样被造出来**的条件, 不是关于值的条件. `cumsum` 绕开它的办法是丢掉原序列, 造一条每项都把前一项当左加数的嵌套序列; 代价就是 §0 的偏移. 消去 `cumsum` 只有两条路: 证明被嵌入的序列本来就可比 (候选 A), 或者把证据放宽到最弱 (候选 B). 两条路都绕不开上面的必要条件.

## §2 候选 A: 构造即单调

### 2.1 树族上的结构序

把 `Ordᴰ` 的结构序推广到 `Ord ℓ`, 加上 `limᵢ` 的情况 ($a\prec f\,x\Rightarrow a\prec\lim_i f$). 它是良基的, 因此非自反 (`≺-irrefl`, 后面的反例要用).

```agda
infix 4 _≺_
data _≺_ {ℓ} : Ord ℓ → Ord ℓ → Set where
  ≺z : ∀ {a} → a ≺ suc a
  ≺s : ∀ {a b} → a ≺ b → a ≺ suc b
  ≺l : ∀ {a} {f : ℕ → Ord ℓ} n → a ≺ f n → a ≺ lim f
  ≺i : ∀ {a i} {p : i < ℓ} {f : Ord< i p → Ord ℓ} x → a ≺ f x → a ≺ limᵢ p f

≺-trans : ∀ {ℓ} {a b c : Ord ℓ} → a ≺ b → b ≺ c → a ≺ c
≺-trans p ≺z       = ≺s p
≺-trans p (≺s q)   = ≺s (≺-trans p q)
≺-trans p (≺l n q) = ≺l n (≺-trans p q)
≺-trans p (≺i x q) = ≺i x (≺-trans p q)

data Acc≺ {ℓ} (a : Ord ℓ) : Set where
  acc : (∀ {b} → b ≺ a → Acc≺ b) → Acc≺ a

acc≺ : ∀ {ℓ} (a : Ord ℓ) {b} → b ≺ a → Acc≺ b
acc≺ (suc a)    ≺z       = acc (acc≺ a)
acc≺ (suc a)    (≺s p)   = acc≺ a p
acc≺ (lim f)    (≺l n p) = acc≺ (f n) p
acc≺ (limᵢ q f) (≺i x p) = acc≺ (f x) p

≺-irrefl : ∀ {ℓ} {a : Ord ℓ} → ¬ (a ≺ a)
≺-irrefl {a = a} = go (acc (acc≺ a)) where
  go : ∀ {a} → Acc≺ a → ¬ (a ≺ a)
  go (acc h) p = go (h p) p
```

**右加数单调是结构的, 左加数吸收不是.** $b\prec c\Rightarrow a+b\prec a+c$ (`+-mono≺`) 逐构造子成立, 包括 `limᵢ`. 反方向的 $b\prec a+b$ 在值上对 (加上 1 后), 在结构上一般不对, §3.2 给出形式反例.

```agda
+-mono≺ : ∀ {ℓ} {a b c : Ord ℓ} → b ≺ c → a + b ≺ a + c
+-mono≺ ≺z       = ≺z
+-mono≺ (≺s q)   = ≺s (+-mono≺ q)
+-mono≺ (≺l n q) = ≺l n (+-mono≺ q)
+-mono≺ (≺i x q) = ≺i x (+-mono≺ q)
```

**规则 4 不是问题.** $\psi_u(b+1)[n]=\psi_u(b)\cdot n$ 在树上是 `lim (iter (c +_) zero)`, 即右嵌套 $c+(c+(\cdots))$; EBO 的 `rep₀`/`rep↓` 把 $\psi_u(b)\cdot(n+1)$ 写成列表 `ψ b ∷ rep b n`, 嵌入后也是右嵌套 (Finite 的 `rep-iter` 是定义性等式). 右嵌套的单调性用的是 $x_n\prec x_{n+1}\Rightarrow c+x_n\prec c+x_{n+1}$, 只需 `+-mono≺`, 用不到 $a\prec b+a$; 左嵌套 `iter (_+ c) c` 每步是 $x\prec x+c$, 也只需 `+-mono≺`. 两种嵌套都只要求 $0\prec c$, 对 $\psi$ 的输出 ($\ge\Omega_0=1$) 这是成立的. 所以不必换嵌套方向或种子.

```agda
rule4ʳ : ∀ {ℓ} {c : Ord ℓ} → zero ≺ c → ∀ n → iter (c +_) zero n ≺ iter (c +_) zero (suc n)
rule4ʳ h zero    = h
rule4ʳ h (suc n) = +-mono≺ (rule4ʳ h n)

rule4ˡ : ∀ {ℓ} {c : Ord ℓ} → zero ≺ c → ∀ n → iter (_+ c) c n ≺ iter (_+ c) c (suc n)
rule4ˡ h n = +-mono≺ h
```

### 2.2 $\varepsilon_0$ 片段: 折叠直接落在下标类型里

规则 5ω ($\psi(\lim f)=\lim(\psi\circ f)$) 的单调性要求 $\psi$ 本身保持结构序. 在只有 $\psi_0$ 的片段 (Cantor 范式, 极限 $\varepsilon_0$) 这是一条结构引理, 而且可以和折叠**互递归**: 折叠直接输出 `Ordᴰ`, 每个 `lim` 的单调性证据由同一个互递归块里的单调性引理现场提供, 不需要事后 `ordᴰ`.

```agda
step→mono : ∀ {f : ℕ → Ordᴰ} → (∀ n → f n < f (suc n)) → monotonic f
step→mono s zero    = s _
step→mono s (suc p) = <-trans (step→mono s p) (s _)

iterᴰ-mono : ∀ {c} → zero < c → monotonic (iter (c +ᴰ_) zero)
iterᴰ-mono {c} h = step→mono go where
  go : ∀ n → iter (c +ᴰ_) zero n < iter (c +ᴰ_) zero (suc n)
  go zero    = h
  go (suc n) = +ᴰ-mono (go n)

ψ⁰ᴰ   : Ordᴰ → Ordᴰ
z<ψ⁰ᴰ : ∀ a → zero < ψ⁰ᴰ a
ψ⁰ᴰ-mono : ∀ {a b} → a < b → ψ⁰ᴰ a < ψ⁰ᴰ b

ψ⁰ᴰ zero      = suc zero
ψ⁰ᴰ (suc a)   = lim (iter (ψ⁰ᴰ a +ᴰ_) zero) (iterᴰ-mono (z<ψ⁰ᴰ a))
ψ⁰ᴰ (lim f m) = lim (ψ⁰ᴰ ∘ f) (λ p → ψ⁰ᴰ-mono (m p))

z<ψ⁰ᴰ zero      = zero
z<ψ⁰ᴰ (suc a)   = lim 1 (z<ψ⁰ᴰ a)
z<ψ⁰ᴰ (lim f m) = lim 0 (z<ψ⁰ᴰ (f 0))

ψ⁰ᴰ-mono {a} zero = lim 2 (+ᴰ-mono (z<ψ⁰ᴰ a))
ψ⁰ᴰ-mono {a} {suc b} (suc p) = <-trans (ψ⁰ᴰ-mono p) (lim 2 (+ᴰ-mono (z<ψ⁰ᴰ b)))
ψ⁰ᴰ-mono {b = lim f m} (lim n p) = <-trans (ψ⁰ᴰ-mono p) (lim (suc n) (ψ⁰ᴰ-mono (m zero)))
```

停机: `ψ⁰ᴰ-mono` 对较大的那一端 $b$ 结构递归. `lim` 情况的第二个调用的证明参数 `m zero` 不是子项, 但目标 $f(n+1)$ 是 $\lim f$ 的子项, 所以与 BTBO 的 `<-dec` 一样靠隐式参数递降. 证明的关键一步是 `lim (suc n) (ψ⁰ᴰ-mono (m zero))`: $\psi(f\,n)\prec\psi(f(n+1))\prec\lim(\psi\circ f)$, 用的正是输入树自带的单调性. 这就是"构造即单调": 只要输入是带证据的下标, 输出就是带证据的下标.

**规则 6 的 $\gamma$-链 (目标层 = 共尾层 = 0).** $\psi_0(\Omega_1)=\varepsilon_0$: $\gamma_0=\Omega_0=1$, $\gamma_{k+1}=\psi_0(\gamma_k)$, 基本列是 $\gamma_{n+1}$. 链的单调性就是 `ψ⁰ᴰ-mono` 的迭代, 种子一步 $\gamma_0=\psi_0(0)\prec\psi_0(1)=\gamma_1$. 层号 $\varepsilon_0$ 的 $\Omega$ 基本列逐项是 $\Omega_{\gamma_{n+1}}$, 定义性成立:

```agda
γᴰ : ℕ → Ordᴰ
γᴰ = iter ψ⁰ᴰ (suc zero)

γᴰ-step : ∀ n → γᴰ n < γᴰ (suc n)
γᴰ-step zero    = ψ⁰ᴰ-mono {a = zero} zero
γᴰ-step (suc n) = ψ⁰ᴰ-mono (γᴰ-step n)

ε₀ᴰ : Ordᴰ
ε₀ᴰ = lim (γᴰ ∘ suc) (λ p → step→mono γᴰ-step (s<s p))

_ : Ω ε₀ᴰ ≡ lim (λ n → ↑ (f<l n) (Ω (γᴰ (suc n))))
_ = refl
```

### 2.3 与 Finite 的忠实折叠对应

`ψ⁰ᴰ` 不是另起炉灶: 遗忘单调证据后, 它就是 [Finite](Finite.lagda.md) §3 的 $\psi^\mathsf{E}$ 在 $\varepsilon_0$ 片段上的样子 (`forget-ψ`, 在 Finite 的外延相等 $\approx$ 下). 由此 Finite §6–7 的 $\varepsilon_0$ 片段 (项 `T₀`, 嵌入 `emb₀`, 对应定理 `corr`) 可以直接把层号造在下标类型里 (`embᴰ`), 无填充.

```agda
forget : Ordᴰ → Ord₀
forget zero      = zero
forget (suc a)   = suc (forget a)
forget (lim f _) = lim (forget ∘ f)

forget-noLᵢ : ∀ a → NoLᵢ (forget a)
forget-noLᵢ zero      = nz
forget-noLᵢ (suc a)   = ns (forget-noLᵢ a)
forget-noLᵢ (lim f _) = nl (λ n → forget-noLᵢ (f n))

forget-+ : ∀ a b → forget (a +ᴰ b) ≈ forget a + forget b
forget-+ a zero      = ≈-refl (forget-noLᵢ a)
forget-+ a (suc b)   = s≈ (forget-+ a b)
forget-+ a (lim f _) = l≈ (λ n → forget-+ a (f n))

ψ₀ᴱ : Ord₀ → Ord₀
ψ₀ᴱ x = ψᴱ {i = zero} {ℓ = suc zero} zero (↑ zero x)

forget-ψ : ∀ a → forget (ψ⁰ᴰ a) ≈ ψ₀ᴱ (forget a)
forget-ψ zero      = s≈ z≈
forget-ψ (suc a)   = l≈ go where
  go : ∀ n → forget (iter (ψ⁰ᴰ a +ᴰ_) zero n) ≈ iter (ψ₀ᴱ (forget a) +_) zero n
  go zero    = z≈
  go (suc n) = ≈-trans (forget-+ (ψ⁰ᴰ a) _) (+-≈ (forget-ψ a) (go n))
forget-ψ (lim f _) = l≈ (λ n → forget-ψ (f n))

embᴰ  : T₀ → Ordᴰ
embPᴰ : P₀ → Ordᴰ
embᴰ []       = zero
embᴰ (x ∷ xs) = embPᴰ x +ᴰ embᴰ xs
embPᴰ (ψ⁰ a)  = ψ⁰ᴰ (embᴰ a)

forget-emb  : ∀ t → forget (embᴰ t) ≈ emb₀ t
forget-embP : ∀ x → forget (embPᴰ x) ≈ embP₀ x
forget-emb []       = z≈
forget-emb (x ∷ xs) = ≈-trans (forget-+ (embPᴰ x) (embᴰ xs)) (+-≈ (forget-embP x) (forget-emb xs))
forget-embP (ψ⁰ a)  = ≈-trans (forget-ψ (embᴰ a)) (ψᴱ-≈ (↑-≈ (forget-emb a)))
```

**定理 (精确层号, $\varepsilon_0$ 片段).** 对共尾度为 $\omega$ 的项 $t$, 层号 `embᴰ t` 是一个 `lim f m`, 且它的第 $n$ 项 (遗忘证据后) 外延等于 $t[n]$ 的树. 由 $\Omega$ 的定义, $\Omega_{\mathsf{emb}^\mathsf{D} t}$ 的第 $n$ 项就是 $\Omega$ 在这一项上的值: 这就是 EBO 的 $\Omega_u[n]=\Omega_{u[n]}$, 没有任何累积和.

```agda
inv-lim : ∀ x {g : ℕ → Ord₀} → forget x ≈ lim g →
          Σ[ f ∈ (ℕ → Ordᴰ) ] Σ[ m ∈ monotonic f ] (x ≡ lim f m) × (∀ n → forget (f n) ≈ g n)
inv-lim (lim f m) (l≈ h) = f , m , refl , h

exact : ∀ t → cof₀ t ≡ cω →
        Σ[ f ∈ (ℕ → Ordᴰ) ] Σ[ m ∈ monotonic f ]
          (embᴰ t ≡ lim f m) × (∀ n → forget (f n) ≈ emb₀ (fs₀ t n))
exact t e = inv-lim (embᴰ t) (≈-trans (forget-emb t) (subst (Shape t) e (corr t)))
```

与 §0 对照, 同一个 $\omega$ 现在给出 $\Omega_\omega[2]=\Omega_2$ (原来是 $\Omega_5$):

```agda
ω̂ : T₀
ω̂ = ψ⁰ (ψ⁰ [] ∷ []) ∷ []

_ : Ω (embᴰ ω̂) ≡ lim (λ n → ↑ (f<l n) (Ω (iter (suc zero +ᴰ_) zero n)))
_ = refl

_ : iter (suc zero +ᴰ_) zero 2 ≡ nat 2
_ = refl
```

"精确"在这里是 $\approx$ 意义下的: 第 $n$ 项与 `embᴰ (fs₀ t n)` 的遗忘像外延相等, 不是定义性相等 (`Ordᴰ` 的 `lim` 带单调证明, 证明不唯一). 这与对齐纲领其余部分的标准一致 (Finite、FiniteAll 都在 $\approx$ 下陈述).

### 2.4 边界: $\psi^\mathsf{E}$ 对结构序不单调

把 2.2 的互递归推到有 `limᵢ` 的层 (Bachmann–Howard 及以上) 时, 需要 $\psi_i$ 对 `Ord ℓ` 的结构序单调. 这不成立. 反例在第 1 层: $\Omega_1=\lim_0(\uparrow)$, $\psi_0(\Omega_1)$ 是 $\gamma$-链 $G$ (从 $G\,0=1$ 起, $G(k+1)=\psi_0(G\,k)$) 的极限 `lim (G ∘ suc)`. 取 $a_1:=\uparrow(\lim G)$, 也就是 $\varepsilon_0$ 的另一个表示 (从 $G\,0$ 而不是 $G\,1$ 起) 提升到第 1 层. 那么 $a_1\prec\Omega_1$ (经分支 $x=(\lim G)+1$), 而 $\psi_0(a_1)$ 与 $\psi_0(\Omega_1)$ **定义性相等**:

```agda
Ω₁ : Ord (suc zero)
Ω₁ = Ωᴱ (suc zero)

G : ℕ → Ord₀
G = iter ψ₀ᴱ (suc zero)

_ : ψᴱ zero Ω₁ ≡ lim (G ∘ suc)
_ = refl

a₁ : Ord (suc zero)
a₁ = ↑ zero (lim G)

_ : ψᴱ zero a₁ ≡ lim (G ∘ suc)
_ = refl

a₁≺Ω₁ : a₁ ≺ Ω₁
a₁≺Ω₁ = ≺i (suc (lim G)) ≺z

ψᴱ-not-mono : ¬ (∀ {a b : Ord (suc zero)} → a ≺ b → ψᴱ zero a ≺ ψᴱ zero b)
ψᴱ-not-mono h = ≺-irrefl {a = lim (G ∘ suc)} (h {a = a₁} {b = Ω₁} a₁≺Ω₁)
```

同一条 $\gamma$-链在 2.2 里是带证据的 `γᴰ`, 两者对应:

```agda
G≈γᴰ : ∀ n → forget (γᴰ n) ≈ G n
G≈γᴰ zero    = s≈ z≈
G≈γᴰ (suc n) = ≈-trans (forget-ψ (γᴰ n)) (ψᴱ-≈ (↑-≈ (G≈γᴰ n)))
```

**失败的确切位置.** 照 2.2 的模式对较大一端归纳证 $a\prec b\Rightarrow\psi_i(a)\prec\psi_i(b)$, `zero`/`suc`/`lim` 三种情况与 $\varepsilon_0$ 片段相同; `limᵢ` 情况 $b=\lim_j g$, $a\prec g\,x$:

- $j<i$ (规则 5Ω, 穿透): $\psi_i(b)=\lim_j(\psi_i\circ g)$, 结构跟着走, 只需 $g$ 单调 (外加 `coe` 的簿记).
- $j\ge i$ (规则 6): $\psi_i(b)=\lim_n\psi_i(g\,\gamma_n)$, 要证 $\psi_i(g\,x)\prec\psi_i(g\,\gamma_n)$ 对某个 $n$, 必须 $x\prec\gamma_n$. 而 $x$ 是任意的第 $j$ 层树, 可以落在整条 $\gamma$-链之上. 上面的反例就是 $x=(\sup\gamma)+1$.

这正是 Buchholz 的 $\psi$ 需要标准形条件的地方: 集合论定义的 $\psi_\nu$ 是弱单调的, 因为非标准参数会被自动折叠 (Buchholz 的 $\psi_0(\varepsilon_0)=\psi_0(\varepsilon_0+2)=\varepsilon_0$); 树的 $\psi^\mathsf{E}$ 沿基本列计算, 对非标准参数"假装它标准", 于是 $\psi^\mathsf{E}_0(\uparrow(\varepsilon_0+2))=\omega^{\varepsilon_0+2}>\psi^\mathsf{E}_0(\Omega_1)$ (这一句是纸面计算, 未编译; 编译的是上面严格版的反例). 要树侧在所有输入上单调, 折叠就得按"参数是否在 $\gamma$-链之下"分情况, 而结构序的判定推出 LPO (§4).

**题设子问题的答案.**

- 规则 4 的 `lim (iter (ψ a +_) zero)` 结构单调, 左右嵌套都行 (2.1). 不需要改.
- 规则 5ω 的 `lim (ψ ∘ f)`: 当 $f$ 单调且相邻项之间的结构路径对 $\psi_i$ **安全** (只在 $j<i$ 的 `limᵢ` 节点分叉, 或在 $j\ge i$ 的节点上分叉于某个 $\gamma_k$ 之下) 时单调. 无 `limᵢ` 的片段一律安全 (2.2). 一般不单调 (2.4).
- 规则 6 的链 $\gamma_k\prec\gamma_{k+1}=\psi_j(f\,\gamma_k)$: 归结为 $\psi_j$ 在 $f\,\gamma_{k-1}\prec f\,\gamma_k$ 上单调; 种子一步要 $\psi_j(0)\prec\psi_j(f\,\Omega_j)$. $j=0$, $f=\uparrow$ 时成立 (`γᴰ-step`). 一般情形与上一条是同一个条件.
- 能否在保持基本列不变的前提下改定义使其单调? 不能靠改 $\psi$ 的某一条规则: 单调性的反例出在非标准输入上, 而对标准输入 $\psi^\mathsf{E}$ 的基本列与 EBO 逐条相同 (Finite, Omega1). 能改的只是**谁来提供证据**: 证据必须来自项的来历 (标准项的嵌入), 不能来自树本身.

## §3 候选 B: 弱化 `lim` 的证据

### 3.1 前驱包含步进: `Ordʷ`

把 `Ordᴰ` 的 `lim` 证据从"严格单调"换成"相邻两项前驱包含" `f n ⊑ f (suc n)`. 三个类型互归纳, 都严格正. 有界三歧性的 `lim`/`lim` 情况用 `sim` 把 $a<f\,n$ 搬到 $a<f\,m$, 仍对隐式上界 $c$ 结构递归; 树族 `Ord₊ʷ`/`Ord<ʷ` 与 BTBO 逐字相同 (下标序仍是子项序, 归纳递归照常通过); $\Omega$ 的极限分支用 `lim n` 当提升证据, **不读步进证据**; Finite 的忠实折叠 $\psi^\mathsf{E}$ 原样搬过来 (`ψʷ`). 由 §1, $\sqsubseteq$ 是能沿之搬运证明的最弱严格正关系, 所以这是候选 B 能走到的最远处. 有向版本 ($\forall n\,m.\,\exists k.\,f\,n\sqsubseteq f\,k\wedge f\,m\sqsubseteq f\,k$) 也能让 `<-dec` 通过, 证明相同, 此处不另写.

```agda
module W where
  infix 4 _<ʷ_ _⊑ʷ_
  data Ordʷ : Set
  data _<ʷ_ : Ordʷ → Ordʷ → Set
  data _⊑ʷ_ : Ordʷ → Ordʷ → Set

  data Ordʷ where
    zero : Ordʷ
    suc  : Ordʷ → Ordʷ
    lim  : (f : ℕ → Ordʷ) (step : ∀ n → f n ⊑ʷ f (suc n)) → Ordʷ

  data _<ʷ_ where
    zero : ∀ {a} → a <ʷ suc a
    suc  : ∀ {a b} → a <ʷ b → a <ʷ suc b
    lim  : ∀ {a} {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} n → a <ʷ f n → a <ʷ lim f s

  data _⊑ʷ_ where
    z⊑ : ∀ {b} → zero ⊑ʷ b
    s⊑ : ∀ {a b} → a <ʷ b → suc a ⊑ʷ b
    l⊑ : ∀ {f : ℕ → Ordʷ} {s : ∀ n → f n ⊑ʷ f (suc n)} {b} → (∀ n → f n ⊑ʷ b) → lim f s ⊑ʷ b

  <ʷ-trans : ∀ {a b c} → a <ʷ b → b <ʷ c → a <ʷ c
  <ʷ-trans p zero      = suc p
  <ʷ-trans p (suc q)   = suc (<ʷ-trans p q)
  <ʷ-trans p (lim n q) = lim n (<ʷ-trans p q)

  sim : ∀ {a b c} → a ⊑ʷ b → c <ʷ a → c <ʷ b
  sim (s⊑ p) zero      = p
  sim (s⊑ p) (suc q)   = <ʷ-trans q p
  sim (l⊑ h) (lim n q) = sim (h n) q

  ⊑ʷ-trans : ∀ {a b c} → a ⊑ʷ b → b ⊑ʷ c → a ⊑ʷ c
  ⊑ʷ-trans z⊑     q = z⊑
  ⊑ʷ-trans (s⊑ p) q = s⊑ (sim q p)
  ⊑ʷ-trans (l⊑ h) q = l⊑ (λ n → ⊑ʷ-trans (h n) q)

  Simʷ : Ordʷ → Ordʷ → Set
  Simʷ a b = ∀ {c} → c <ʷ a → c <ʷ b

  Sim→⊑ʷ : ∀ {a b} → Simʷ a b → a ⊑ʷ b
  Sim→⊑ʷ {a = zero}    s = z⊑
  Sim→⊑ʷ {a = suc a}   s = s⊑ (s zero)
  Sim→⊑ʷ {a = lim f t} s = l⊑ (λ n → Sim→⊑ʷ (λ q → s (lim n q)))

  ⊑ʷ-refl : ∀ {a} → a ⊑ʷ a
  ⊑ʷ-refl = Sim→⊑ʷ (λ q → q)

  steps : ∀ {f : ℕ → Ordʷ} → (∀ n → f n ⊑ʷ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ʷ f m
  steps s zero    = s _
  steps s (suc p) = ⊑ʷ-trans (steps s p) (s _)

  <ʷ-dec : ∀ {a b c} → a <ʷ c → b <ʷ c → a <ʷ b ⊎ b <ʷ a ⊎ a ≡ b
  <ʷ-dec zero zero       = injᶜ refl
  <ʷ-dec zero (suc q)    = injᵇ q
  <ʷ-dec (suc p) zero    = injᵃ p
  <ʷ-dec (suc p) (suc q) = <ʷ-dec p q
  <ʷ-dec (lim {s = s} n p) (lim m q) with <ᴺ-dec n m
  ... | injᵃ n<m  = <ʷ-dec (sim (steps s n<m) p) q
  ... | injᵇ m<n  = <ʷ-dec p (sim (steps s m<n) q)
  ... | injᶜ refl = <ʷ-dec p q

  -- 常值列也是合法的极限 (Ordᴰ 不允许)
  const-lim : Ordʷ → Ordʷ
  const-lim a = lim (λ _ → a) (λ _ → ⊑ʷ-refl)

  -- Ordᴰ 保守地嵌入 Ordʷ: 旧的层号全部仍是层号
  ι     : Ordᴰ → Ordʷ
  ι-mono : ∀ {a b} → a < b → ι a <ʷ ι b
  ι zero      = zero
  ι (suc a)   = suc (ι a)
  ι (lim f m) = lim (ι ∘ f) (λ n → Sim→⊑ʷ (λ q → <ʷ-trans q (ι-mono (m zero))))
  ι-mono zero      = zero
  ι-mono (suc p)   = suc (ι-mono p)
  ι-mono (lim n p) = lim n (ι-mono p)

  -- 树族: 与 BTBO 的 Ord-Ord 逐字相同, 只换下标类型
  module _ (ℓ : Ordʷ) (Ord< : (i : Ordʷ) → i <ʷ ℓ → Set) where
    data Ord₊ʷ : Set where
      zero : Ord₊ʷ
      suc  : Ord₊ʷ → Ord₊ʷ
      lim  : (f : ℕ → Ord₊ʷ) → Ord₊ʷ
      limᵢ : ∀ {i} (p : i <ʷ ℓ) (f : Ord< i p → Ord₊ʷ) → Ord₊ʷ

  Ord<ʷ : ∀ {ℓ} (i : Ordʷ) → i <ʷ ℓ → Set
  Ord<ʷ i zero      = Ord₊ʷ i Ord<ʷ
  Ord<ʷ i (suc p)   = Ord<ʷ i p
  Ord<ʷ i (lim n p) = Ord<ʷ i p

  Ordᵂ : Ordʷ → Set
  Ordᵂ ℓ = Ord<ʷ ℓ zero

  Ord<ʷ-≡ : ∀ {i ℓ₁ ℓ₂} (p : i <ʷ ℓ₁) (q : i <ʷ ℓ₂) → Ord<ʷ i p ≡ Ord<ʷ i q
  Ord<ʷ-≡ zero zero      = refl
  Ord<ʷ-≡ (suc p) zero   = Ord<ʷ-≡ p zero
  Ord<ʷ-≡ (lim n p) zero = Ord<ʷ-≡ p zero
  Ord<ʷ-≡ p (suc q)      = Ord<ʷ-≡ p q
  Ord<ʷ-≡ p (lim n q)    = Ord<ʷ-≡ p q

  coeʷ : ∀ {i ℓ₁ ℓ₂} {p : i <ʷ ℓ₁} {q : i <ʷ ℓ₂} → Ord<ʷ i p → Ord<ʷ i q
  coeʷ {p = p} {q = q} = subst (λ X → X) (Ord<ʷ-≡ p q)

  coe₀ʷ : ∀ {i ℓ} {p : i <ʷ ℓ} → Ordᵂ i → Ord<ʷ i p
  coe₀ʷ = coeʷ {p = zero}

  ↑ʷ : ∀ {ℓ₁ ℓ₂} → Simʷ ℓ₁ ℓ₂ → Ordᵂ ℓ₁ → Ordᵂ ℓ₂
  ↑ʷ s zero       = zero
  ↑ʷ s (suc a)    = suc (↑ʷ s a)
  ↑ʷ s (lim f)    = lim (↑ʷ s ∘ f)
  ↑ʷ s (limᵢ q f) = limᵢ (s q) (↑ʷ s ∘ f ∘ coeʷ)

  -- Ω 的极限分支: 第 n 项就是 Ω_{f n}, 提升证据是 `lim n`, 不读步进证据
  Ωʷ : (ℓ : Ordʷ) → Ordᵂ ℓ
  Ωʷ zero      = suc zero
  Ωʷ (suc ℓ)   = limᵢ zero (↑ʷ suc)
  Ωʷ (lim f _) = lim (λ n → ↑ʷ (lim n) (Ωʷ (f n)))

  _+ʷ_ : ∀ {ℓ} → Ordᵂ ℓ → Ordᵂ ℓ → Ordᵂ ℓ
  a +ʷ zero     = a
  a +ʷ suc b    = suc (a +ʷ b)
  a +ʷ lim f    = lim (λ n → a +ʷ f n)
  a +ʷ limᵢ p f = limᵢ p (λ x → a +ʷ f x)

  -- Buchholz 忠实折叠 (Finite §3 的 ψᴱ), 原样搬到新下标类型
  ψʷ : ∀ {i ℓ} → i <ʷ ℓ → Ordᵂ ℓ → Ordᵂ i
  ψʷ p zero    = Ωʷ _
  ψʷ p (suc a) = lim (iter (ψʷ p a +ʷ_) zero)
  ψʷ p (lim f) = lim (ψʷ p ∘ f)
  ψʷ {i} {ℓ} p (limᵢ {i = j} q f) with <ʷ-dec q p
  ... | injᵃ j<i = limᵢ j<i (ψʷ p ∘ f ∘ coeʷ)
  ... | injᵇ _   = lim (λ n → ψʷ p (f (coe₀ʷ (iter (ψʷ q ∘ f ∘ coe₀ʷ) (Ωʷ j) n))))
  ... | injᶜ _   = lim (λ n → ψʷ p (f (coe₀ʷ (iter (ψʷ q ∘ f ∘ coe₀ʷ) (Ωʷ j) n))))
```

在 `Ordʷ` 上, 任何合法的极限层 $\lim f$ 的 $\Omega$ 基本列都是 $\Omega_{f\,n}$ 本身; 问题只剩"被嵌入的序列是否 $\sqsubseteq$-步进". 规则 4、5ω、6 的形状都不变, 与 EBO 的规则 $\Omega_u[n]=\Omega_{u[n]}$ 字面一致.

### 3.2 优势序列: 用 cumsum 当上界, 原序列当基本列

自然的混合方案: `lim` 同时存原序列 $f$ (给 $\Omega$ 读) 和单调的上界 $g=\mathrm{cumsum}\,f$ (给 `<-dec` 读), 要求 $f\,n\sqsubseteq g\,n$. 这要求 $b\sqsubseteq a+(b+1)$, 即左加数吸收, 结构上不成立. 反例: $f\,0=1$, $f\,1=\omega+1$, 则 $\mathrm{cumsum}\,f\,1=1+(\omega+2)$, 其前驱里没有 $\omega$ 本身 (只有 $1+\omega$, 它是 $\omega$ 的另一个表示, 结构上既不等于也不大于 $\omega$):

```agda
ωᴰ : Ordᴰ
ωᴰ = lim nat nat-mono

1+nat : ∀ k → suc zero +ᴰ nat k ≡ nat (suc k)
1+nat zero    = refl
1+nat (suc k) = cong suc (1+nat k)

¬ω<nat : ∀ k → ¬ (ωᴰ < nat k)
¬ω<nat zero ()
¬ω<nat (suc zero) (suc ())
¬ω<nat (suc (suc k)) (suc p) = ¬ω<nat (suc k) p

¬ω<1+ω : ¬ (ωᴰ < suc zero +ᴰ ωᴰ)
¬ω<1+ω (lim k p) = ¬ω<nat (suc k) (subst (ωᴰ <_) (1+nat k) p)

head₀ : Ordᴰ → Ordᴰ
head₀ (lim f _) = f 0
head₀ a         = a

¬ω≡1+ω : ¬ (ωᴰ ≡ suc zero +ᴰ ωᴰ)
¬ω≡1+ω e with cong head₀ e
... | ()

<suc : ∀ {a b} → a < suc b → a ≡ b ⊎ a < b
<suc zero    = inj₁ refl
<suc (suc p) = inj₂ p

absorb-fails : ¬ (suc ωᴰ ⊑ suc zero +ᴰ suc (suc ωᴰ))
absorb-fails (s⊑ p) with <suc p
... | inj₁ ()
... | inj₂ q with <suc q
...   | inj₁ e = ¬ω≡1+ω e
...   | inj₂ r = ¬ω<1+ω r

-- 也就是 cumsum 的第 1 项不包含原序列第 1 项的前驱
dom-fails : let f = λ { zero → suc zero ; (suc _) → suc ωᴰ } in ¬ (f 1 ⊑ cumsum f 1)
dom-fails = absorb-fails
```

换别的上界也无济于事: $g(n+1)$ 必须同时包含 $g\,n$ 与 $f(n+1)$ 的前驱, 由 `comparable` 这要求两者的前驱可比, 而 $f(n+1)$ 与此前诸项的可比性正是要回避的条件. 结构序没有"并": 两个不可比的树没有公共的结构上界. 把 $f$ 当右加数则单调性那一侧需要吸收, 对称地失败.

### 3.3 $\sqsubseteq$ 证据的实际增益

`Ordʷ` 比 `Ordᴰ` 多接纳的是**极限节点的重表示**: $\omega$ 与 $1+\omega$ 在 `Ordᴰ` 里结构上互不小于 (`¬ω<1+ω`), 在 `Ordʷ` 里互相前驱包含, 于是二者可以在同一个极限层号里相邻. **后继节点仍须字面一致**: $(\omega+1)\sqsubseteq x$ 要求 $\omega$ 本身是 $x$ 的前驱, 3.2 的反例经 `ι` 搬到 `Ordʷ` 里同样成立 (`absorbʷ-fails`). 所以 B 降低了 A 要证的东西 (从 $\prec$ 到 $\sqsubseteq$), 但不改变 A 的困难所在: 2.4 的严格版反例在 $\sqsubseteq$ 下不再是反例 (两边相等), 值层面的版本 ($\uparrow(\varepsilon_0+2)$) 仍然是, 因为 $\sqsubseteq$ 蕴含值的 $\le$.

```agda
open W using (Ordʷ; _<ʷ_; _⊑ʷ_; Simʷ; Sim→⊑ʷ; ι)

ω-shift : ι ωᴰ ⊑ʷ ι (suc zero +ᴰ ωᴰ)
ω-shift = Sim→⊑ʷ go where
  go : Simʷ (ι ωᴰ) (ι (suc zero +ᴰ ωᴰ))
  go {c} (W.lim k p) = W.lim k (subst (λ x → c <ʷ ι x) (sym (1+nat k)) (W.suc p))

¬ιω<ιnat : ∀ k → ¬ (ι ωᴰ <ʷ ι (nat k))
¬ιω<ιnat zero ()
¬ιω<ιnat (suc zero) (W.suc ())
¬ιω<ιnat (suc (suc k)) (W.suc p) = ¬ιω<ιnat (suc k) p

¬ιω<ι1+ω : ¬ (ι ωᴰ <ʷ ι (suc zero +ᴰ ωᴰ))
¬ιω<ι1+ω (W.lim k p) = ¬ιω<ιnat (suc k) (subst (λ x → ι ωᴰ <ʷ ι x) (1+nat k) p)

headʷ : Ordʷ → Ordʷ
headʷ (W.lim f _) = f 0
headʷ a           = a

¬ιω≡ι1+ω : ¬ (ι ωᴰ ≡ ι (suc zero +ᴰ ωᴰ))
¬ιω≡ι1+ω e with cong headʷ e
... | ()

<sucʷ : ∀ {a b} → a <ʷ W.suc b → a ≡ b ⊎ a <ʷ b
<sucʷ W.zero    = inj₁ refl
<sucʷ (W.suc p) = inj₂ p

absorbʷ-fails : ¬ (ι (suc ωᴰ) ⊑ʷ ι (suc zero +ᴰ suc (suc ωᴰ)))
absorbʷ-fails (W.s⊑ p) with <sucʷ p
... | inj₁ ()
... | inj₂ q with <sucʷ q
...   | inj₁ e = ¬ιω≡ι1+ω e
...   | inj₂ r = ¬ιω<ι1+ω r
```

### 3.4 把累积和写进 `lim` 的语义

另一种 B: `lim d` 的语义直接定为 $d_0+(1+d_1)+(1+d_2)+\cdots$, 下标序的 `lim` 构造子指向部分和 `psum d n`. 这样单调性免费, 表记一侧的规则变成"$\Omega_u[n]=\Omega_{d_0+\cdots+d_n}$". 下标类型本身 (互归纳-递归, `psum` 用 `_⊕_` 定义) 能通过; **树族不能**:

```text
module B3 where   -- 实验文件 (scratchpad), --safe --without-K
  data Ordˢ : Set;  data _<_ : Ordˢ → Ordˢ → Set
  _⊕_ : Ordˢ → Ordˢ → Ordˢ;  psum : (ℕ → Ordˢ) → ℕ → Ordˢ
  data Ordˢ where zero; suc; lim : (d : ℕ → Ordˢ) → Ordˢ
  data _<_ where zero : a < suc a; suc : a < b → a < suc b
                 lim  : ∀ n → a < psum d n → a < lim d
  psum d zero = d zero;  psum d (suc n) = psum d n ⊕ suc (d (suc n))
  ... (树族 Ord₊ / Ord< 与 BTBO 逐字相同)
  Ord< i zero      = Ord₊ i Ord<
  Ord< i (suc p)   = Ord< i p
  Ord< i (lim n p) = Ord< i p

B3.agda:37.1-40.28: error: [TerminationIssue]
Termination checking failed for the following functions:
  Ord<
Problematic calls:
  Ord<            (at B3.agda:38.27-31)
  Ord< i p        (at B3.agda:40.20-24)
```

原因: `lim n p` 情况把上界从 `lim d` 换成 `psum d n`, 后者是计算出来的, 不是 `lim d` 的子项, 与 `zero` 情况里未应用的递归出现组合后没有一致递降的参数. 这是 README 记录的设计事实 ("下标序必须是子项序") 的又一个实例. 即使绕过, $\Omega$ 读到的也是部分和, 表记一侧要写 $\Omega_{\omega+\omega^\omega+\cdots}$ 这样的非范式项, 与"整个基本列更规整"背道而驰. 否决.

## §4 候选 C: 换一个层号嵌入

### 4.1 按需填充不可计算

"只在序列不单调时填充"要判定 $f\,n\prec f(n+1)$. 哪怕只判定 $0\prec x$ 也推出 LPO: 对 $\alpha:\mathbb{N}\to\mathbf 2$ 令 $t_\alpha=\lim(n\mapsto[\alpha\,n])$, $[\mathsf{true}]=1$, $[\mathsf{false}]=0$, 则 $0\prec t_\alpha\iff\exists n.\,\alpha\,n$.

```agda
b2o : Bool → Ord₀
b2o true  = suc zero
b2o false = zero

tα : (ℕ → Bool) → Ord₀
tα α = lim (λ n → b2o (α n))

dec≺→LPO : (∀ (a b : Ord₀) → Dec (a ≺ b)) → LPO
dec≺→LPO d α with d zero (tα α)
... | yes (≺l n p) = inj₁ (n , is-true (α n) p) where
  is-true : ∀ b → zero ≺ b2o b → b ≡ true
  is-true true  _ = refl
  is-true false ()
... | no ¬p = inj₂ (λ k → not-true (α k) (λ p → ¬p (≺l k p))) where
  not-true : ∀ b → ¬ (zero ≺ b2o b) → b ≡ false
  not-true true  h = ⊥-elim (h ≺z)
  not-true false h = refl
```

所以"按需"只能是**按来历**: 证据由造树的过程携带 (候选 A 的 `ψ⁰ᴰ`), 而不是事后检测.

### 4.2 其他填充方式

- **按 $+1$ 填充** ($g\,n=f\,n+n$ 之类): 有限的平移只能把已有的 $\sqsubseteq$-步进变成严格步进 (而 `Ordʷ` 已经不需要严格), 造不出可比性. 由 `comparable`, 任何不丢弃原序列的填充都要求原序列先可比.
- **丢弃原序列的填充** (cumsum 及其变体): 都会遇到 §0 的偏移, 而且与 $+$ 不交换, 表记无法镜像.

结论: 不存在只看树、对所有树都可用、又与表记逐项一致的层号嵌入. 这一条与 4.1 合起来就是题目要求的"能否被表记镜像"的否定回答.

## §5 候选 D: 其他想法

**D1 (§1 的观察).** $\Omega$ 与 `↑` 只用前驱包含, 单调性只服务于 `<-dec`. 这把问题从"消去 cumsum"重述为"为每个极限层号提供可比性证据", 并给出证据的下界 ($\sqsubseteq$-步进, §3.1). "两条序列各管一事"(3.2) 被 `absorb-fails` 否定.

**D2 (层号由表记生成).** 不从树算层号, 而对标准项 $u$ 按 `cof` 递归: 后继取 `suc`, 极限取 $\lim(n\mapsto\mathsf{lvl}(u[n]))$, 单调证据来自 Bachmann 性质 ("$v<u$ 且 $u$ 为极限 $\Rightarrow v\le u[n]$ 对可计算的 $n$", 于是每个更小的标准项都沿基本列路径**字面地**出现, 结构序与项序一致). 这给出值正确、逐项精确的层号. 但它需要 (a) 沿 $<^\mathsf{T}$ 的 `Acc` 证书, 恰是对齐纲领想由树免费得到的东西, 循环; (b) EBO 标准形的理论 (EBO §9 说明尚未做). 未编译; 记为 A 的开放引理在表记一侧的对偶.

**D3 (混合: 按来历认证).** 对由标准项嵌入而来的树, 用带证据的折叠 (`ψ⁰ᴰ` 模式) 直接造下标; 对来历不明的树, 保留 `ordᴰ` 作后备, 其强度标签照 README 的认证规则记为"估计". 这是 §7 的推荐.

## §6 对比

| 候选 | 定义要点 | 决定性实验 | 极限下标 $u$ 的 $\Omega_u[n]$ | 表记能否逐项镜像 | 判定 |
|---|---|---|---|---|---|
| 现状 (BTBO) | `ordᴰ`: 每个 `lim` 换成 cumsum | §0 `refl`; `overshoot` | $\Omega_{u[0]+(u[1]+1)+\cdots+(u[n]+1)}$; 非主数的 $u$ 值也错 ($\omega\cdot2\mapsto\omega^2$) | 否 (要改值) | 待替换 |
| A, $\psi_0$ 片段 | `ψ⁰ᴰ` 与单调性互递归, 直接输出 `Ordᴰ` | `exact` (编译), `Ω ε₀ᴰ` `refl` | $\Omega_{u[n]}$ ($\approx$ 意义) | 是, 规则不变 | 成立, 到 $\varepsilon_0$ |
| A, 一般 $\psi^\mathsf{E}$ | 同上推到有 `limᵢ` 的层 | `ψᴱ-not-mono` (编译) | (若能认证) $\Omega_{u[n]}$ | 是 | 需开放引理 |
| B1 `Ordʷ` | `lim` 证据改为 $\sqsubseteq$-步进 | `<ʷ-dec`, `ψʷ`, `ι` (编译) | 对任意合法层号恰为 $\Omega_{f\,n}$ | 是, 当嵌入序列 $\sqsubseteq$-步进 | 采纳 (无损的最弱证据) |
| B2 优势序列 | 存 $f$ 与上界 $g=\mathrm{cumsum}\,f$ | `absorb-fails` (编译) | — | — | 否决 |
| B3 和式语义 | `lim d` 表示 $\sum d_n$ | 树族 `TerminationIssue` | $\Omega_{d_0+\cdots+d_n}$ (非范式) | 否 | 否决 |
| C1 按需填充 | 不单调才填 | `dec≺→LPO` (编译) | — | — | 不可计算 |
| C2 $+1$ 填充 | 有限平移 | 由 `comparable` (纸面) | — | — | 无效 |
| D2 表记生成 | 按 `cof` 递归建层号 | 未编译 | $\Omega_{u[n]}$ | 是 | 循环 (要 `Acc`) |

## §7 推荐与代价

**推荐**: B1 + A 的认证模式 (即 D3).

1. **下标类型换成 `Ordʷ`.** 树侧改动: `Ordᴰ` 的 `lim` 字段从 `monotonic f` 换成 `∀ n → f n ⊑ f (suc n)`, 增加一个互归纳关系 `_⊑_` 与三条引理 (`sim`, `⊑-trans`, `Sim→⊑`); `<-dec` 改三行; `↑` 接受 `Sim`; $\Omega$ 的极限分支用 `lim n` 代替 `f<l n`. 树族、折叠逐字不动 (§3.1 全部编译). 表记侧不动. 损失: 无 (`ι` 把旧层号保守地嵌入; `<-dec` 的强度不变; 壁垒定理的前提不变, 因为 `Ordʷ` 仍是可数树, 没有 $\Omega$-共尾元).
2. **层号由折叠直接构造, 不再事后 `ordᴰ`.** 对每个片段, 写一个输出下标类型的折叠, 与它的单调性引理互递归 (`ψ⁰ᴰ`/`ψ⁰ᴰ-mono` 的模式), 再证它遗忘证据后与 $\psi^\mathsf{E}$ 外延相等 (`forget-ψ`). 树侧代价: 每个片段一套认证折叠与对应引理. 表记侧: 不动, $\Omega_u[n]=\Omega_{u[n]}$ 保持原样. 已完成: $\psi_0$ 片段 ($\varepsilon_0$).
3. **一般情形的代价 (开放).** 有 `limᵢ` 的层需要一条**安全路径引理**: 对标准项的嵌入, 相邻基本列项之间的结构路径在每个 $j\ge i$ 的 `limᵢ` 节点上都分叉于该节点对应的 $\gamma$-链之下 (或更一般地, 在 $\sqsubseteq$ 意义下被 $\gamma$-链覆盖). 它是 Buchholz 标准形条件 ($a\in C_\nu(a)$, 参数小于所折叠的值) 在树上的影子; 对非标准树它是假的 (§2.4), 所以只能对"由标准项嵌入而来"的树证明, 证明要对项结构归纳并跟踪 $\gamma$-链. 在它证出之前, 对角线 $\psi^n$ (层号是 $\psi_0(\Omega_x)$ 的输出, 涉及所有层的规则 6) 仍须用 `ordᴰ` 后备, 其层号的基本列只是共尾一致, 强度标签仍为估计.

**不推荐**改表记一侧去镜像累积和: §0 说明那会改变项的值, §3.4 说明连树族都定义不出来.

## §8 结论与边界

已形式化 (全部 `--safe --without-K`, 无公设、无洞、无停机编译指示):

1. $\Omega$ 的极限分支与层间提升只需前驱包含, 对任意序列成立 (`f⊑lim`, `↑ˢ`, `Ωˢ`); 有界三歧性迫使同一极限层的各项前驱两两可比 (`comparable`). 消去 cumsum 等价于给出这种可比性的证据.
2. 现状的偏移是值层面的: $\omega\cdot3$ 在 $\mathsf{ord}^\mathsf{D}(\omega\cdot2)$ 之下 (`overshoot`).
3. 规则 4 的迭代在两种嵌套下都结构单调 (`rule4ʳ`, `rule4ˡ`).
4. $\psi_0$ 片段的认证折叠 `ψ⁰ᴰ` 直接输出下标, 其单调性互递归可证; 与 $\psi^\mathsf{E}$ 外延相等 (`forget-ψ`); 片段的层号逐项是表记的基本列 (`exact`); $\varepsilon_0$ 的层号 $\Omega$-基本列为 $\Omega_{\gamma_{n+1}}$ (`refl`).
5. $\psi^\mathsf{E}$ 对结构序不单调 (`ψᴱ-not-mono`, 反例 $\uparrow(\lim G)\prec\Omega_1$ 且两者的 $\psi_0$ 定义性相等).
6. 下标类型 `Ordʷ` ($\sqsubseteq$-步进) 有有界三歧性, 承载 BTBO 的树族与 Finite 的忠实折叠, 保守扩张 `Ordᴰ`.
7. 以 cumsum 为上界的混合方案不成立 (`absorb-fails`, 在 `Ordʷ` 中亦然: `absorbʷ-fails`); `Ordʷ` 接纳 $\omega$ 与 $1+\omega$ 的相邻 (`ω-shift`), `Ordᴰ` 不接纳 (`¬ω<1+ω`, `¬ω≡1+ω`); 结构序的判定推出 LPO (`dec≺→LPO`).
8. 实验记录: 累积和写进 `lim` 语义的下标类型, 其树族不过停机检查 (§3.4 错误原文).

边界与未做:

- "逐项精确"在外延相等 $\approx$ 下成立, 不是定义性相等; 层号之间的比较仍是结构 (内涵) 的.
- 认证只覆盖 $\psi_0$ 片段. 推到 Bachmann–Howard (Omega1 的片段) 需要 §7 第 3 条的安全路径引理, 本文只给出它的精确陈述和必要性 (反例), 没有证明.
- $\psi^\mathsf{E}_0(\uparrow(\varepsilon_0+2))>\psi^\mathsf{E}_0(\Omega_1)$ (值层面的非单调) 是纸面计算; 编译的是严格版的反例.
- D2 (表记生成层号) 未编译, 理由见 §5.
- 本文不改 `src/` 与已有的 Align 文件; `Ordʷ` 是否替换 `Ordᴰ` 由后续任务决定.
