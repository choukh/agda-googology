# RR4 实验 (一): "分支对值单调" 的片段上, 折叠仍不是值的函数; 逐点前序下折叠单调

> 第四次路线审查 (`probes/Survey/RR4-Fable52.md`) 的实验文件, 第 4 层, 不进成品. 只导入 [Level](Level.lagda.md) 与 [Value](Value.lagda.md), 不改任何已有文件.
>
> 要检验的主张 (待核): [Value](Value.lagda.md) §3 的读法与 RouteReview3 §5.9.3 第一行说, $\psi$ 尊重值可以在 "分支对值单调" 的片段上成立. 本文只看第 1 层的结点 (分支取第 0 层的树), 给出两条编译过的定理:
>
> 1. **否定 `mono-fragment-not-cong`.** 取 $X=\psi^0(\Omega_1)$, 结点 $\Omega_1^X$ 的分支是 $x\mapsto X+x$. 这个分支对值单调 (`hX-mono`), 且 $x\preccurlyeq X+x$ (`≼-+ˡ`). $\Omega_1\approx^{\mathsf v}\Omega_1^X$ (`Ω₁≈Ω₁ˣ`), 但 $\mathrm{suc}\,X\preccurlyeq\psi^0(\Omega_1^X)$ (`sucX≼`), 所以 $\psi^0(\Omega_1^X)\not\preccurlyeq\psi^0(\Omega_1)$. **两个结点的分支都对值单调, 值相同, 折叠值不同.** 所以 "分支对值单调" 不足以让 $\psi^0$ 成为值的函数, 也不足以让它对值前序单调.
> 2. **正面 `pointwise-mono₁`.** 若两个分支逐点相关 ($x\preccurlyeq y\Rightarrow h\,x\preccurlyeq h'\,y$), 则 $\psi^0(\mathrm{node}\,h)\preccurlyeq\psi^0(\mathrm{node}\,h')$. 无其它前提. 证明沿规则 6 的两条链同步归纳.
>
> **读法 (判断).** 两个结点的值相同是因为值只看上确界 ($X+\Omega_1$ 的上确界就是 $\Omega_1$). 折叠沿基本列计算, 它算的是 "$\psi_0(X+\Omega_1)$ 这个写法的基本列极限", 第 0 项就是 $\psi^0(X+1)$. 这与记号里非标准形的项是同一件事 (纸面: 按 Buchholz 的语义 $\psi_0(\varepsilon_0+\Omega_1)=\psi_0(\Omega_1)$, 按基本列展开则得到更大的序数). 第 2 条说明: 把输入的比较从 "值 (上确界)" 换成 "逐点" 之后, 第 1 层没有反例. 更高层是否成立, 本文没有检验.
>
> **范围.** 两条定理都只对第 1 层的结点 `limᵢ zero (λ x → up zero (h x))`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR4MonoFragment where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Value
  using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≅→≼;
         s≼s⁻; s≼0; ≼lim⁻; +-mono; ψ⁰-mono⁰; 1≼ψ⁰; 𝟏; Ω₁)
```

## §1 第 1 层的结点与规则 6 的链

`node h` 是分支为 $x\mapsto h\,x$ 的第 1 层结点. `Ω₁` 就是 `node (λ x → x)`. `ψ⁰-node` 是 `refl`: $\psi^0$ 在这类结点上的值就是链上各点的折叠的极限.

```agda
Br : Set
Br = Ordᶜ zero → Ordᶜ zero

node : Br → Ordᶜ (suc zero)
node h = limᵢ zero (λ x → up zero (h x))

STEPʰ : Br → Ordᶜ zero → Ordᶜ zero
STEPʰ h x = ψ {i = zero} {k = suc zero} {ℓ = suc zero} zero (λ r → r) (up zero (h x))

chain : Br → ℕ → Ordᶜ zero
chain h = iter (STEPʰ h) 𝟏

ψ⁰-node : ∀ h → ψ⁰ (node h) ≡ lim (λ n → ψ⁰ (h (chain h n)))
ψ⁰-node h = refl

Ω₁-node : Ω₁ ≡ node (λ x → x)
Ω₁-node = refl
```

链的一步 `STEPʰ h x` 是带证明的折叠 `ψ zero`, 它与 `ψ⁰ (h x)` 结构互模拟 (`Level.ψ⁰≅ψ`), 于是值相同.

```agda
step≼ : ∀ h x → STEPʰ h x ≼ ψ⁰ (h x)
step≼ h x = ≅→≼ (≅-sym (ψ⁰≅ψ {p = zero} {σ = λ q → suc q} (≅-refl⁰ (h x))))

step≽ : ∀ h x → ψ⁰ (h x) ≼ STEPʰ h x
step≽ h x = ≅→≼ (ψ⁰≅ψ {p = zero} {σ = λ q → suc q} (≅-refl⁰ (h x)))
```

## §2 正面: 逐点前序下折叠单调

前提 `R` 把两个分支逐点联系起来. 它不要求 $h$ 或 $h'$ 各自单调, 也不比较两个结点的上确界.

```agda
module Pointwise (h h′ : Br) (R : ∀ {x y} → x ≼ y → h x ≼ h′ y) where

  chain≼ : ∀ n → chain h n ≼ chain h′ n
  chain≼ zero    = ≼-refl 𝟏
  chain≼ (suc n) =
    ≼-trans (step≼ h (chain h n))
    (≼-trans (ψ⁰-mono⁰ (R (chain≼ n))) (step≽ h′ (chain h′ n)))

  pointwise-mono₁ : ψ⁰ (node h) ≼ ψ⁰ (node h′)
  pointwise-mono₁ = l≼ (λ n → ≼l n (ψ⁰-mono⁰ (R (chain≼ n))))
```

前提可满足: 取 $h=h'$ 为恒等, `R` 就是恒等.

```agda
pointwise-instance : ψ⁰ Ω₁ ≼ ψ⁰ Ω₁
pointwise-instance = Pointwise.pointwise-mono₁ (λ x → x) (λ x → x) (λ e → e)
```

## §3 否定: 分支对值单调, 值相同, 折叠值不同

三条第 0 层的引理: 右加不减 (`≼-+ˡ`), $a\preccurlyeq\psi^0a$ (`x≼ψ⁰`), 值前序无自反的后继 (`irr`, 与 `BTBOValNeg.≼-irr` 同一证明, 这里重写是为了不导入记号模块).

```agda
≼-+ˡ : ∀ (a b : Ordᶜ zero) → b ≼ a + b
≼-+ˡ a zero        = z≼
≼-+ˡ a (suc b)     = s≼s (≼-+ˡ a b)
≼-+ˡ a (lim f)     = l≼ (λ n → ≼l n (≼-+ˡ a (f n)))
≼-+ˡ a (limᵢ () f)
≼-+ˡ a (up () x)

x≼ψ⁰ : ∀ (a : Ordᶜ zero) → a ≼ ψ⁰ a
x≼ψ⁰ zero        = z≼
x≼ψ⁰ (suc a)     = ≼l 2 (+-mono (x≼ψ⁰ a) (1≼ψ⁰ a))
x≼ψ⁰ (lim f)     = l≼ (λ n → ≼l n (x≼ψ⁰ (f n)))
x≼ψ⁰ (limᵢ () f)
x≼ψ⁰ (up () x)

irr : ∀ (a : Ordᶜ zero) → ¬ (suc a ≼ a)
irr zero        p = s≼0 p
irr (suc a)     p = irr a (s≼s⁻ p)
irr (lim f)     p with ≼lim⁻ p
... | n , q = irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) q)
irr (limᵢ () f) p
irr (up () x)   p
```

对任意第 0 层的 $a$, 分支 $x\mapsto a+x$ 的结点与 $\Omega_1$ 同值, 分支对值单调, 而它的折叠严格高于 $a$.

```agda
module Prefix (a : Ordᶜ zero) where
  hA : Br
  hA x = a + x

  hA-mono : ∀ {x y} → x ≼ y → hA x ≼ hA y
  hA-mono e = +-mono (≼-refl a) e

  hA-infl : ∀ x → x ≼ hA x
  hA-infl x = ≼-+ˡ a x

  same-value : Ω₁ ≈ᵛ node hA
  same-value =
      i≼ (λ x ex → ≼i x ex (u≼ (≼u (≼-+ˡ a x))))
    , i≼ (λ x ex → ≼i (hA x) (≅-refl⁰ (hA x)) (≼-refl (up zero (hA x))))

  fold-above : suc a ≼ ψ⁰ (node hA)
  fold-above = ≼l 0 (≼l 2 (+-mono (x≼ψ⁰ a) (1≼ψ⁰ a)))

  fold-below : ψ⁰ Ω₁ ≼ ψ⁰ (node hA)
  fold-below = Pointwise.pointwise-mono₁ (λ x → x) hA (λ {x} {y} e → ≼-trans e (≼-+ˡ a y))
```

取 $a=X=\psi^0(\Omega_1)$.

```agda
X : Ordᶜ zero
X = ψ⁰ Ω₁

module PX = Prefix X

Ω₁ˣ : Ordᶜ (suc zero)
Ω₁ˣ = node PX.hA

hX-mono : ∀ {x y} → x ≼ y → PX.hA x ≼ PX.hA y
hX-mono = PX.hA-mono

Ω₁≈Ω₁ˣ : Ω₁ ≈ᵛ Ω₁ˣ
Ω₁≈Ω₁ˣ = PX.same-value

sucX≼ : suc (ψ⁰ Ω₁) ≼ ψ⁰ Ω₁ˣ
sucX≼ = PX.fold-above

mono-fragment-not-cong : (Ω₁ ≈ᵛ Ω₁ˣ) × ¬ (ψ⁰ Ω₁ˣ ≼ ψ⁰ Ω₁)
mono-fragment-not-cong = Ω₁≈Ω₁ˣ , λ e → irr X (≼-trans sucX≼ e)

-- 另一个方向成立: 折叠值只会变大
Ω₁≼Ω₁ˣ-fold : ψ⁰ Ω₁ ≼ ψ⁰ Ω₁ˣ
Ω₁≼Ω₁ˣ-fold = PX.fold-below
```

## §4 结论与边界

**已编译.**

- `Pointwise.pointwise-mono₁`: 第 1 层, 分支逐点相关则折叠单调. 前提实例 `pointwise-instance`.
- `mono-fragment-not-cong`: $\Omega_1\approx^{\mathsf v}\Omega_1^X$, $\psi^0(\Omega_1^X)\not\preccurlyeq\psi^0(\Omega_1)$. 两个分支 (恒等与 $x\mapsto X+x$) 都对值单调 (`hX-mono`), 都满足 $x\preccurlyeq h\,x$ (`Prefix.hA-infl`).
- 与 `Value.ψ⁰-not-cong` 的差别: 那里的 $\Omega_1'$ 的分支 $g$ 不尊重值 ($g(1)=0$ 而 $g(\lim\,\mathrm{const}\,1)=\lim\,\mathrm{const}\,1$), 折叠值偏小 (链停滞). 这里的分支尊重值且单调, 折叠值偏大 (前缀被上确界吸收, 折叠却看得见).

**没有证的.** 第 2 层及以上的逐点前序 (分支吃第 1 层的树, 输入之间要用同一个逐点关系比较, 这是按层递归的定义, 本文没有写). "逐点前序对 $\Omega$、加法、回灌封闭" 也没有证. 所以本文不说 V 墙已被绕开, 只说: 值 (上确界) 前序在单调片段上仍有反例, 逐点前序在第 1 层没有反例.
