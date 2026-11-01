# 证据模 ≅ 的下标类型: 层号证书与无填充的折叠

> 接 [Cumulative](Cumulative.lagda.md) §13 "代价" 一段. 那里的累积树族 `Ordᶜ` (定义性提升 `up`, 跨层结构互模拟 $\cong$) 让对角线上的步进成立, 但只是**模 $\cong$** 成立; 而下标类型仍是 [Cumsum](Cumsum.lagda.md) 的 `Ordʷ`, 它的 `lim` 要求相邻两项**字面**前驱包含. 于是 [Certified](Certified.lagda.md) 的证书 `toLevel` 吃不下模 $\cong$ 的步进, 对角线的层号仍要靠 [BTBO](../../../src/OCF/BTBO.lagda.md) 的 `ordᴰ` (`cumsum`) 填充. 本文做那一步 "本文没有尝试" 的事: 一个 `lim` 证据模 $\cong$ 的下标类型, 树族搬到它上面, 证书 `toLevel`, 以及组装无填充的对角线所需的全部接口. 对角线本身在 [Diagonal](Diagonal.lagda.md).
>
> 结论先说:
>
> 1. **采用内部表示 R1 (§1).** `Ordᴵ` 与它上面的字面子项序 $<^\mathsf{I}$、结构互模拟 $\cong^\mathsf{I}$、前驱包含 $\sqsubseteq^\mathsf{I}$ 四者归纳-归纳地同时定义, `lim f s` 的证据 `s n : f n ⊑ᴵ f (suc n)` 是 "$f\,n$ 的每个前驱都 $\cong^\mathsf{I}$ 于 $f(n+1)$ 的某个字面前驱". 外部表示 R2 ($\Sigma$ 型) 不能字面地作树族的下标: 用序对作下标时归纳-递归的 `U` 要么留下无解元变量, 要么过不了停机检查 (§3, 记录了确切报错); 只能退到 "树族以裸树为下标, 证据另传", 那样每个派发函数都要多一个证据参数, `toLevel` 也不再平凡.
> 2. **有界三歧性模 $\cong$ 成立 (`<ᴵ-dec`), 但三种情况都只模 $\cong$, 不只是第三种.** 结果是 $a\prec^\mathsf{I}b$, $b\prec^\mathsf{I}a$ 或 $a\cong^\mathsf{I}b$, 其中 $a\prec^\mathsf{I}b$ 意为 "$a\cong^\mathsf{I}a'$ 且 $a'<^\mathsf{I}b$". 第一种情况不能加强成字面的 $a<^\mathsf{I}b$: 任何给出字面结果的三歧判定都推出一个函数外延性的特例 `natᴵ ≡ (λ n → natᴵ (n +ᴺ 0))` (`lit→ext`, §2, 已编译), 而这在 `--without-K` 下不可证.
> 3. **因此 $\psi$ 需要层间搬运, 恰好一处.** 任务预期 "第三种情况的唯一消费者是 $\psi$ 的派发, 链在节点自己的层 $j$ 上, 不需要搬运". 第三种 (以及第二种) 确实如此: 链 $\gamma$ 在第 $j$ 层, 输出直接折到目标层. 但第一种 (穿透, $j\prec i$) 的输出节点必须挂在目标层 $i$ 的某个**字面**前驱 $j'$ 上, 而输入的分支函数吃第 $j$ 层的树, $j\cong^\mathsf{I}j'$ 却 $j\ne j'$. 所以穿透分支要一个结构搬运 `tr⁻ : j ≅ᴵ j′ → Ordᶜ j′ → Ordᶜ j` (§4). 它对 $\cong^\mathsf{I}$ 的证明与树同时递归, 只碰 `limᵢ` 的下标与 `up` 的嵌入, 在 $\cong$ 下不可见 (`tr-≅`). $\Omega$、`lift`、`add`、`Sim`、`ψ⁰` 都不需要搬运.
> 4. **树族与定理的移植 (§4–§8).** `Ordᶜ`, `U`/`into`/`out`/`lift`, $\Omega$, `add`, `ψ⁰`, FGH 逐字; `ψ` 只改穿透分支; $\cong$ 的 `lᵢ≅` 改为允许两边节点在 $\cong^\mathsf{I}$-相关的层 (这是穿透输出代表元的直接后果); `ψ-≅` 推广到 $\cong^\mathsf{I}$-相关的目标层; `≅-sym`, `≅-trans`, `≺-respʳ`, `Ω-mono`, `Ψ-mono` 的证明各改一两处 (用 `tr`), 陈述不变. 清单在 §10.
> 5. **证书 `toLevel` 忠实 (§9).** `toLevel : (x : Ordᶜ zero) → HS x → Ordᴵ` 对树 $x$ 递归 (不是对证书), `lim` 的证据由 `toLevel-⊑` 现场给出, 二者互递归且通过停机检查. 对**任意**证书 $h$ (包括抽象的假设), `toLevel (lim f) h` 的第 $n$ 项定义性地就是 `toLevel (f n) _`, $\Omega$ 的第 $n$ 项定义性地是 $\Omega_{\mathtt{toLevel}(f\,n)}$ (`toLevel-lim`, `Ω-exact`, 都是 `refl`); $\omega$ 的层号第 2 项是 2, 而 `ordᴰ` 给 5. 遗忘回树只在 $\cong$ 下还原 (`forget-toLevel`); 字面的 `≡` 要函数外延性.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 下标类型是新的, 不用 `W`; 只从 Cumsum 取 `natᴼ` 作 `cumsum` 的对照.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Level where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂; trans)

open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open Ord-Ord using (iter; ordᴰ)
open BoundedTrich using (cumsum)
open import OCF.Barrier using (nat)
open import OCF.Align.Cumsum using (natᴼ)
```

## §0 问题的精确形式

Cumulative 证明的步进是 $\cong$-版的: 叶子 `≺z` 要求 $c\cong b$. 而 Certified 的证书

    data Step where
      l : (h : ∀ n → Step (f n)) → (∀ n → toLevel (f n) (h n) ⊑ʷ toLevel (f (suc n)) (h (suc n))) → Step (lim f)

要的是 `Ordʷ` 上的**字面** $\sqsubseteq^\mathsf{w}$ (`s⊑ : a <ʷ b → suc a ⊑ʷ b`, 前驱必须字面地是子项). 两个相邻层号的前驱只模 $\cong$ 对应时, `toLevel` 造不出 `lim`. 需要的是一个下标类型, 它的 `lim` 证据本身就模 $\cong$, 同时保留有界三歧性 (折叠的派发) 与归纳-递归树族的停机论证 (定义域由对子项证明的递归算出).

接口 (与并行的安全路径引理约定):

    HS : Ordᶜ zero → Set          -- 第 0 层的遗传步进, ⊑⁰ 是 ⊑ 的第 0 层实例
    toLevel : (x : Ordᶜ zero) → HS x → Ordᴵ
    Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))   -- 由另一方给出, 本文只作模块参数

## §1 下标类型 `Ordᴵ`

四个类型同时定义: `Ordᴵ`; 字面子项序 $<^\mathsf{I}$ (与 `W` 的 $<^\mathsf{w}$ 同形, 树族的 `limᵢ` 用它); 结构互模拟 $\cong^\mathsf{I}$ (对 `lim` 逐点, 不看步进证据); 前驱包含 $\sqsubseteq^\mathsf{I}$, 它的后继子句是 `s⊑ : a ≅ᴵ a′ → a′ <ᴵ b → suc a ⊑ᴵ b`, 即 "$a$ 本身 $\cong^\mathsf{I}$ 于 $b$ 的某个字面前驱". 这就是 "叶子为 $\cong$ 的前驱包含" 的归纳写法: 记 $a\prec^\mathsf{I}b$ 为 "$a\cong^\mathsf{I}a'<^\mathsf{I}b$", 则 $\mathrm{suc}\,a\sqsubseteq^\mathsf{I}b\iff a\prec^\mathsf{I}b$, 与树侧 `≺z` 的形状一致.

```agda
infix 4 _<ᴵ_ _≅ᴵ_ _⊑ᴵ_ _≺ᴵ_
data Ordᴵ : Set
data _<ᴵ_ : Ordᴵ → Ordᴵ → Set
data _≅ᴵ_ : Ordᴵ → Ordᴵ → Set
data _⊑ᴵ_ : Ordᴵ → Ordᴵ → Set

data Ordᴵ where
  zero : Ordᴵ
  suc  : Ordᴵ → Ordᴵ
  lim  : (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) → Ordᴵ

data _<ᴵ_ where
  zero : ∀ {a} → a <ᴵ suc a
  suc  : ∀ {a b} → a <ᴵ b → a <ᴵ suc b
  lim  : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a <ᴵ f n → a <ᴵ lim f s

data _≅ᴵ_ where
  z≅ : zero ≅ᴵ zero
  s≅ : ∀ {a b} → a ≅ᴵ b → suc a ≅ᴵ suc b
  l≅ : ∀ {f g : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {t : ∀ n → g n ⊑ᴵ g (suc n)} →
       (∀ n → f n ≅ᴵ g n) → lim f s ≅ᴵ lim g t

data _⊑ᴵ_ where
  z⊑ : ∀ {b} → zero ⊑ᴵ b
  s⊑ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → suc a ⊑ᴵ b
  l⊑ : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {b} → (∀ n → f n ⊑ᴵ b) → lim f s ⊑ᴵ b

data _≺ᴵ_ (a b : Ordᴵ) : Set where
  via : ∀ {a′} → a ≅ᴵ a′ → a′ <ᴵ b → a ≺ᴵ b
```

$\sqsubseteq^\mathsf{I}$ 必须是归纳的. 函数式的写法 (`lim` 的证据为 `∀ n {c} → c ≺ f n → c ≺ f (suc n)`) 让正在定义的类型出现在箭头左边: `[NotStrictlyPositive] Ordᶠ is not strictly positive, because it occurs to the left of an arrow in the type of the constructor lim in the definition of Ordᶠ` (临时文件 `F1`). 树侧的 $\sqsubseteq$ 可以是函数式的, 因为它从不进入某个数据类型的构造子.

**$\cong^\mathsf{I}$ 是等价关系, 对一切层号.** 与树侧不同, 层号没有 `limᵢ`, 所以 $\cong^\mathsf{I}$ 自反 (不只是 PER).

```agda
≅ᴵ-refl : ∀ a → a ≅ᴵ a
≅ᴵ-refl zero      = z≅
≅ᴵ-refl (suc a)   = s≅ (≅ᴵ-refl a)
≅ᴵ-refl (lim f s) = l≅ (λ n → ≅ᴵ-refl (f n))

≅ᴵ-sym : ∀ {a b} → a ≅ᴵ b → b ≅ᴵ a
≅ᴵ-sym z≅     = z≅
≅ᴵ-sym (s≅ e) = s≅ (≅ᴵ-sym e)
≅ᴵ-sym (l≅ h) = l≅ (λ n → ≅ᴵ-sym (h n))

≅ᴵ-trans : ∀ {a b c} → a ≅ᴵ b → b ≅ᴵ c → a ≅ᴵ c
≅ᴵ-trans z≅     z≅      = z≅
≅ᴵ-trans (s≅ e) (s≅ e′) = s≅ (≅ᴵ-trans e e′)
≅ᴵ-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅ᴵ-trans (h n) (h′ n))

<ᴵ-trans : ∀ {a b c} → a <ᴵ b → b <ᴵ c → a <ᴵ c
<ᴵ-trans p zero      = suc p
<ᴵ-trans p (suc q)   = suc (<ᴵ-trans p q)
<ᴵ-trans p (lim n q) = lim n (<ᴵ-trans p q)
```

**沿 $\cong^\mathsf{I}$ 搬子项.** `<-≅` 是整个下标层的关键引理: $a$ 的字面子项 $c$, 搬到 $a'\cong^\mathsf{I}a$ 里, 得到一个 $\cong^\mathsf{I}c$ 的字面子项. 由它得到 $\prec^\mathsf{I}$ 两侧尊重 $\cong^\mathsf{I}$、传递, 以及 $\sqsubseteq^\mathsf{I}$ 作为 "搬运函数" 的 `sim` (`W` 里的 `sim` 是字面的, 这里输出 $\prec^\mathsf{I}$).

```agda
<-≅ : ∀ {c a a′} → c <ᴵ a → a ≅ᴵ a′ → c ≺ᴵ a′
<-≅ zero      (s≅ e) = via e zero
<-≅ (suc p)   (s≅ e) with <-≅ p e
... | via e′ q = via e′ (suc q)
<-≅ (lim n p) (l≅ h) with <-≅ p (h n)
... | via e′ q = via e′ (lim n q)

≺ᴵ-respˡ : ∀ {a a′ b} → a′ ≅ᴵ a → a ≺ᴵ b → a′ ≺ᴵ b
≺ᴵ-respˡ e (via e′ q) = via (≅ᴵ-trans e e′) q

≺ᴵ-respʳ : ∀ {a b b′} → a ≺ᴵ b → b ≅ᴵ b′ → a ≺ᴵ b′
≺ᴵ-respʳ (via e q) e′ = ≺ᴵ-respˡ e (<-≅ q e′)

≺ᴵ-trans : ∀ {a b c} → a ≺ᴵ b → b ≺ᴵ c → a ≺ᴵ c
≺ᴵ-trans (via e q) (via e′ r) with <-≅ q e′
... | via e″ q′ = via (≅ᴵ-trans e e″) (<ᴵ-trans q′ r)

sim : ∀ {a b c} → a ⊑ᴵ b → c <ᴵ a → c ≺ᴵ b
sim (s⊑ e q) zero      = via e q
sim (s⊑ e q) (suc p)   = ≺ᴵ-trans (<-≅ p e) (via (≅ᴵ-refl _) q)
sim (l⊑ h)   (lim n p) = sim (h n) p

⊑ᴵ-trans : ∀ {a b c} → a ⊑ᴵ b → b ⊑ᴵ c → a ⊑ᴵ c
⊑ᴵ-trans z⊑       r = z⊑
⊑ᴵ-trans (s⊑ e q) r with sim r q
... | via e′ q′ = s⊑ (≅ᴵ-trans e e′) q′
⊑ᴵ-trans (l⊑ h)   r = l⊑ (λ n → ⊑ᴵ-trans (h n) r)

steps : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ⊑ᴵ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ᴵ f m
steps s zero    = s _
steps s (suc p) = ⊑ᴵ-trans (steps s p) (s _)

Sim→⊑ᴵ : ∀ {a b} → (∀ {c} → c <ᴵ a → c <ᴵ b) → a ⊑ᴵ b
Sim→⊑ᴵ {a = zero}    σ = z⊑
Sim→⊑ᴵ {a = suc a}   σ = s⊑ (≅ᴵ-refl a) (σ zero)
Sim→⊑ᴵ {a = lim f s} σ = l⊑ (λ n → Sim→⊑ᴵ (λ q → σ (lim n q)))

⊑ᴵ-refl : ∀ {a} → a ⊑ᴵ a
⊑ᴵ-refl = Sim→⊑ᴵ (λ q → q)
```

**有界三歧性, 模 $\cong^\mathsf{I}$.** `W` 的 `<ʷ-dec` 照搬, 改动只在 `lim`/`lim` 且 $n\ne m$ 的情况: `sim` 把 $a<f\,n$ 搬成 $a\cong a'<f\,m$, 对 $a'$ 递归, 再用 `shift` 把结果里的 $a'$ 换回 $a$. 递归仍是对隐式上界 $c$ 的结构递归 ($\lim f\to f\,m$). 无自反性靠 $<^\mathsf{I}$ 良基: $a\cong a'<a$ 经 `<-≅` 给出 $a'\prec a'$, 下降一步.

```agda
<ᴵ-dec : ∀ {a b c} → a <ᴵ c → b <ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
<ᴵ-dec zero    zero    = injᶜ (≅ᴵ-refl _)
<ᴵ-dec zero    (suc q) = injᵇ (via (≅ᴵ-refl _) q)
<ᴵ-dec (suc p) zero    = injᵃ (via (≅ᴵ-refl _) p)
<ᴵ-dec (suc p) (suc q) = <ᴵ-dec p q
<ᴵ-dec (lim {s = s} n p) (lim m q) with <ᴺ-dec n m
... | injᵃ n<m with sim (steps s n<m) p
...   | via e p′ = shift e (<ᴵ-dec p′ q) where
  shift : ∀ {a a′ b} → a ≅ᴵ a′ → a′ ≺ᴵ b ⊎ b ≺ᴵ a′ ⊎ a′ ≅ᴵ b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
  shift e (injᵃ r) = injᵃ (≺ᴵ-respˡ e r)
  shift e (injᵇ r) = injᵇ (≺ᴵ-respʳ r (≅ᴵ-sym e))
  shift e (injᶜ r) = injᶜ (≅ᴵ-trans e r)
<ᴵ-dec (lim {s = s} n p) (lim m q) | injᵇ m<n with sim (steps s m<n) q
...   | via e q′ = shift e (<ᴵ-dec p q′) where
  shift : ∀ {a b b′} → b ≅ᴵ b′ → a ≺ᴵ b′ ⊎ b′ ≺ᴵ a ⊎ a ≅ᴵ b′ → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
  shift e (injᵃ r) = injᵃ (≺ᴵ-respʳ r (≅ᴵ-sym e))
  shift e (injᵇ r) = injᵇ (≺ᴵ-respˡ e r)
  shift e (injᶜ r) = injᶜ (≅ᴵ-trans r (≅ᴵ-sym e))
<ᴵ-dec (lim n p) (lim m q) | injᶜ refl = <ᴵ-dec p q

data Accᴵ (a : Ordᴵ) : Set where
  acc : (∀ {b} → b <ᴵ a → Accᴵ b) → Accᴵ a

accᴵ : ∀ a {b} → b <ᴵ a → Accᴵ b
accᴵ (suc a)   zero      = acc (accᴵ a)
accᴵ (suc a)   (suc p)   = accᴵ a p
accᴵ (lim f s) (lim n p) = accᴵ (f n) p

≺ᴵ-irrefl : ∀ {a} → ¬ (a ≺ᴵ a)
≺ᴵ-irrefl {a} = go (acc (accᴵ a)) where
  go : ∀ {a} → Accᴵ a → ¬ (a ≺ᴵ a)
  go (acc h) (via e q) = go (h q) (<-≅ q e)
```

于是下标层的三条性质都在: 有界三歧 (模 $\cong^\mathsf{I}$), $\prec^\mathsf{I}$ 无自反且传递, 子项序良基. 壁垒定理 ([Barrier](../Barrier.lagda.md)) 不受影响: $\cong^\mathsf{I}$ 是结构的 (逐点、不看证据), 不是值的外延相等, 判定它从不需要无界搜索.

## §2 第一种情况不能是字面的

能不能让三歧性在前两种情况给出字面的 $a<^\mathsf{I}b$, 只在第三种退到 $\cong^\mathsf{I}$? 不能. 取 $\omega$ 的两个表示 `ωᴵ` 与 `ω′`, 后者的基本列是 $n\mapsto n+0$ (对变量 $n$ 不定义性地归约到 $n$), 二者 $\cong^\mathsf{I}$. 极限层 $c=\lim F$ 的第 0 项是 $\omega+1$, 其余项是 $\omega'+2$, 步进证据是 `s⊑ ω≅ω′ _`. 在 $c$ 之下比较 $\omega$ (经第 0 项) 与 $\omega'+1$ (经第 1 项): 字面三歧若在第一种情况给出 $\omega<^\mathsf{I}\omega'+1$, 则 $\omega=\omega'$ 或 $\omega<^\mathsf{I}\omega'$, 后者与 $\cong$ 矛盾; 第二种情况同样矛盾; 第三种 ($\omega\cong\omega'+1$) 没有构造子. 剩下的只有 $\omega\equiv\omega'$, 取基本列即得 `natᴵ ≡ (λ n → natᴵ (n +ᴺ 0))`.

```agda
natᴵ : ℕ → Ordᴵ
natᴵ zero    = zero
natᴵ (suc n) = suc (natᴵ n)

natᴵ-step : ∀ m → natᴵ m ⊑ᴵ natᴵ (suc m)
natᴵ-step m = Sim→⊑ᴵ suc

ωᴵ ω′ : Ordᴵ
ωᴵ = lim natᴵ natᴵ-step
ω′ = lim (λ n → natᴵ (n +ᴺ 0)) (λ n → natᴵ-step (n +ᴺ 0))

ω≅ω′ : ωᴵ ≅ᴵ ω′
ω≅ω′ = l≅ (λ n → subst (λ k → natᴵ n ≅ᴵ natᴵ k) (sym (+-identityʳ n)) (≅ᴵ-refl _))

F : ℕ → Ordᴵ
F zero    = suc ωᴵ
F (suc _) = suc (suc ω′)

F-step : ∀ n → F n ⊑ᴵ F (suc n)
F-step zero    = s⊑ ω≅ω′ (suc zero)
F-step (suc n) = ⊑ᴵ-refl

LitTrich : Set
LitTrich = ∀ {a b c} → a <ᴵ c → b <ᴵ c → a <ᴵ b ⊎ b <ᴵ a ⊎ a ≅ᴵ b

<suc : ∀ {a b} → a <ᴵ suc b → a ≡ b ⊎ a <ᴵ b
<suc zero    = inj₁ refl
<suc (suc p) = inj₂ p

lit→ω≡ω′ : LitTrich → ωᴵ ≡ ω′
lit→ω≡ω′ t with t {c = lim F F-step} (lim 0 zero) (lim 1 zero)
... | injᵃ r with <suc r
...   | inj₁ e = e
...   | inj₂ q = ⊥-elim (≺ᴵ-irrefl (<-≅ q (≅ᴵ-sym ω≅ω′)))
lit→ω≡ω′ t | injᵇ r = ⊥-elim (≺ᴵ-irrefl (<-≅ (<ᴵ-trans zero r) ω≅ω′))
lit→ω≡ω′ t | injᶜ ()

seq : Ordᴵ → ℕ → Ordᴵ
seq (lim f _) = f
seq _         = λ _ → zero

lit→ext : LitTrich → natᴵ ≡ (λ n → natᴵ (n +ᴺ 0))
lit→ext t = cong seq (lit→ω≡ω′ t)
```

`natᴵ ≡ (λ n → natᴵ (n +ᴺ 0))` 是函数外延性的一个实例: 两边逐点命题相等, 定义性不等, `--without-K` 的 Agda 证不出它 (函数外延性独立于 MLTT; 这一句是元理论事实, 未编译). 所以有界三歧性的第一种情况只能是 $j\prec^\mathsf{I}i$ ("$j\cong^\mathsf{I}j'<^\mathsf{I}i$"), 而 $\psi$ 的穿透分支要把第 $j$ 层的分支挂到 $j'$ 上: **层间搬运是必需的**, 见 §4.

## §3 外部表示 R2 为什么不用

R2 把证据放在树外: `Ordᴵ = Σ (x : Ordᶜ zero) (HS x)`, 序取第一分量. 字面地这样写是循环的: `Ordᶜ` 以 `Ordᴵ` 为下标, 而 `Ordᴵ` 由 `Ordᶜ zero` 定义. 可行的版本是先有一个裸树类型 `B` (`zero`/`suc`/`lim`), 证据谓词 `HSᴮ : B → Set`, 下标取序对 `Lv = Σ B HSᴮ`, 序取第一分量. 临时文件里测了树族的归纳-递归部分:

    U : ∀ {ℓ : Lv} (i : Lv) → proj₁ i <ᴮ proj₁ ℓ → Set
    U i zero      = Ord₊ i U
    U i (suc p)   = U i p
    U i (lim n p) = U i p

- `HSᴮ` 取 `⊤` 时通过 (η 让第二分量平凡), 不说明问题.
- `HSᴮ` 取真正的数据类型 (遗传谓词) 时: `[UnsolvedMetaVariables] Unsolved metas at the following locations: …` (三处, 递归调用里隐式的 $\ell$: 由 `proj₁ ℓ′ = b` 定不出第二分量; 而 `suc p` 情况下根本没有现成的 `HSᴮ b`).
- 把限制写出来 (`U {_ , h} i (suc p) = U {_ , hs⁻ h} i p`, `hs⁻`、`hl⁻` 是证据的反演): `[TerminationIssue] Termination checking failed for the following functions: U. Problematic calls: U …, U i p`. 停机检查器不把 `(b , hs⁻ h)` 看成比 `(suc b , h)` 小.
- 以裸的第一分量 `B` 为下标 (临时文件 `R2b`) 通过.

所以 R2 的可用形式是 "树族以裸树 `B` 为下标, 证据在外". 代价: (i) 树族的元素不再带三歧性所需的证据, `ψ` 的派发要额外的 `HSᴮ ℓ` 参数, 并沿 `σ`、`◃`、`<` 限制到较低层; `ψ⁰`、`ψ-≅`、`Ψ-mono` 同样, Cumulative 的所有签名都要改. (ii) 接口里的 `HS` 是 `Ordᶜ zero` 上的 (第 0 层的树), 而层号是 `B` 的元素, 两者是不同的类型, `toLevel` 要把 `Ordᶜ zero` 遗忘到 `B` 并把 `⊑⁰` 的证据翻译成 `B` 上的证据: R2 承诺的 "`toLevel` 平凡" 不成立. (iii) R1 也只需要 `toLevel-⊑` 这一个互递归 (§9), 已通过停机检查. **选 R1.** 对比表在 §11.

## §4 树族、层间搬运与折叠

树族照搬 Cumulative §3, 只换下标类型: $\triangleleft$ (结构子项, 多一个 `self n`)、直接前驱 $\triangleleft_1$、`U` 对证明递归、`into`/`out` 每步恒等、`lift` 只对证明递归.

```agda
infix 4 _◃_ _◃₁_

data _◃_ : Ordᴵ → Ordᴵ → Set where
  zero : ∀ {a} → a ◃ suc a
  suc  : ∀ {a b} → a ◃ b → a ◃ suc b
  self : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ◃ lim f s
  lim  : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a ◃ f n → a ◃ lim f s

data _◃₁_ : Ordᴵ → Ordᴵ → Set where
  zero : ∀ {a} → a ◃₁ suc a
  self : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ◃₁ lim f s

<→◃ : ∀ {a b} → a <ᴵ b → a ◃ b
<→◃ zero      = zero
<→◃ (suc p)   = suc (<→◃ p)
<→◃ (lim n p) = lim n (<→◃ p)

◃₁→◃ : ∀ {a b} → a ◃₁ b → a ◃ b
◃₁→◃ zero     = zero
◃₁→◃ (self n) = self n

Simᴵ : Ordᴵ → Ordᴵ → Set
Simᴵ a b = ∀ {c} → c <ᴵ a → c <ᴵ b

module _ (ℓ : Ordᴵ) (U : (i : Ordᴵ) → i ◃ ℓ → Set) where
  data Ord₊ : Set where
    zero : Ord₊
    suc  : Ord₊ → Ord₊
    lim  : (f : ℕ → Ord₊) → Ord₊
    limᵢ : ∀ {i} (p : i <ᴵ ℓ) (f : U i (<→◃ p) → Ord₊) → Ord₊
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : U k (◃₁→◃ r)) → Ord₊

U : ∀ {ℓ} (i : Ordᴵ) → i ◃ ℓ → Set
U i zero         = Ord₊ i U
U i (suc r)      = U i r
U _ (self {f} n) = Ord₊ (f n) U
U i (lim n r)    = U i r

Ordᶜ : Ordᴵ → Set
Ordᶜ ℓ = Ord₊ ℓ U

out : ∀ {i ℓ} (r : i ◃ ℓ) → U i r → Ordᶜ i
out zero      x = x
out (suc r)   x = out r x
out (self n)  x = x
out (lim n r) x = out r x

into : ∀ {i ℓ} (r : i ◃ ℓ) → Ordᶜ i → U i r
into zero      x = x
into (suc r)   x = into r x
into (self n)  x = x
into (lim n r) x = into r x

out-into : ∀ {i ℓ} (r : i ◃ ℓ) (x : Ordᶜ i) → out r (into r x) ≡ x
out-into zero      x = refl
out-into (suc r)   x = out-into r x
out-into (self n)  x = refl
out-into (lim n r) x = out-into r x

coe : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) → U i r → U i r′
coe r r′ x = into r′ (out r x)

lift : ∀ {k ℓ} → k ◃ ℓ → Ordᶜ k → Ordᶜ ℓ
lift zero      x = up zero x
lift (suc r)   x = up zero (lift r x)
lift (self n)  x = up (self n) x
lift (lim n r) x = up (self n) (lift r x)
```

**结构搬运.** `tr e : Ordᶜ a → Ordᶜ b` 沿 $e:a\cong^\mathsf{I}b$ 搬运一棵树, 反向的 `tr⁻` 与它互递归 (不用 $\cong^\mathsf{I}$ 的对称, 否则停机检查器看不出下降). `zero`/`suc`/`lim` 原样; `up` 按 $e$ 的构造子下降一层 (`s≅` 对 `up zero`, `l≅ h` 对 `up (self n)` 用 `h n`); `limᵢ q f` 的下标 $j<^\mathsf{I}a$ 要换成 $b$ 的字面子项: `res q e` 沿 $q$ 与 $e$ 同时递归, 给出代表元 `rep` ($j\cong^\mathsf{I}$ `rep` $<^\mathsf{I}b$) 和反向搬运 `back : Ordᶜ rep → Ordᶜ j`, 后者在底部就是 `tr⁻` (或 `tr`) 作用于 $e$ 的**子证明**. 停机度量是 ($e$, 树) 的字典序: 经过 `res` 的调用让 $e$ 结构下降, 直接的递归让树下降.

```agda
record Restr (j b : Ordᴵ) : Set where
  constructor restr
  field
    {rep} : Ordᴵ
    eq    : j ≅ᴵ rep
    lt    : rep <ᴵ b
    back  : Ordᶜ rep → Ordᶜ j
open Restr

tr   : ∀ {a b} → a ≅ᴵ b → Ordᶜ a → Ordᶜ b
tr⁻  : ∀ {a b} → a ≅ᴵ b → Ordᶜ b → Ordᶜ a
res  : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → Restr j b
res⁻ : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → Restr j a

tr e zero    = zero
tr e (suc x) = suc (tr e x)
tr e (lim f) = lim (λ n → tr e (f n))
tr e (limᵢ q f) = limᵢ (lt (res q e)) (λ y → tr e (f (into (<→◃ q) (back (res q e) (out (<→◃ (lt (res q e))) y)))))
tr (s≅ e) (up zero x)     = up zero (tr e x)
tr (l≅ h) (up (self n) x) = up (self n) (tr (h n) x)

tr⁻ e zero    = zero
tr⁻ e (suc x) = suc (tr⁻ e x)
tr⁻ e (lim f) = lim (λ n → tr⁻ e (f n))
tr⁻ e (limᵢ q f) = limᵢ (lt (res⁻ q e)) (λ y → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) (out (<→◃ (lt (res⁻ q e))) y)))))
tr⁻ (s≅ e) (up zero x)     = up zero (tr⁻ e x)
tr⁻ (l≅ h) (up (self n) x) = up (self n) (tr⁻ (h n) x)

res zero      (s≅ e) = restr e zero (tr⁻ e)
res (suc q)   (s≅ e) = restr (eq (res q e)) (suc (lt (res q e))) (back (res q e))
res (lim n q) (l≅ h) = restr (eq (res q (h n))) (lim n (lt (res q (h n)))) (back (res q (h n)))

res⁻ zero      (s≅ e) = restr (≅ᴵ-sym e) zero (tr e)
res⁻ (suc q)   (s≅ e) = restr (eq (res⁻ q e)) (suc (lt (res⁻ q e))) (back (res⁻ q e))
res⁻ (lim n q) (l≅ h) = restr (eq (res⁻ q (h n))) (lim n (lt (res⁻ q (h n)))) (back (res⁻ q (h n)))
```

`limᵢ` 情况用投影而不用 `with`: 后面的引理要直接谈论 `back (res q e)`, `with` 会把它抽象掉.

**$\Omega$、加法、折叠.** $\Omega$, `add`, `ψ⁰`, FGH 与 Cumulative 逐字相同. `ψ` 的规则 4、5ω、6 与提升情况逐字相同; 只有穿透 (规则 5Ω) 改了: `<ᴵ-dec` 给出 `via e r` ($e:j\cong^\mathsf{I}j'$, $r:j'<^\mathsf{I}i$), 输出节点挂在 $j'$ 上, 分支先用 `tr⁻ e` 把第 $j'$ 层的输入搬回第 $j$ 层. 规则 6 的两种情况 ($i\prec j$ 与 $i\cong j$) 都不搬运: 链 $\gamma$ 在节点自己的层 $j$ 上 (起点 $\Omega_j$, 每步 `ψ q`), 输出直接折到 $i$.

```agda
Ω : (ℓ : Ordᴵ) → Ordᶜ ℓ
Ω zero      = suc zero
Ω (suc ℓ)   = limᵢ zero (up zero)
Ω (lim f s) = lim (λ n → up (self n) (Ω (f n)))

add : ∀ {k ℓ} → Ordᶜ ℓ → Simᴵ k ℓ → Ordᶜ k → Ordᶜ ℓ
add a σ zero              = a
add a σ (suc b)           = suc (add a σ b)
add a σ (lim f)           = lim (λ n → add a σ (f n))
add a σ (limᵢ q f)        = limᵢ (σ q) (λ y → add a σ (f (coe (<→◃ (σ q)) (<→◃ q) y)))
add a σ (up zero x)       = add a (λ q → σ (suc q)) x
add a σ (up (self n) x)   = add a (λ q → σ (lim n q)) x

infixl 6 _+_
_+_ : ∀ {ℓ} → Ordᶜ ℓ → Ordᶜ ℓ → Ordᶜ ℓ
a + b = add a (λ q → q) b

ψ : ∀ {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → Ordᶜ k → Ordᶜ i
ψ p σ zero    = Ω _
ψ p σ (suc a) = lim (iter (ψ p σ a +_) zero)
ψ p σ (lim f) = lim (λ n → ψ p σ (f n))
ψ p σ (limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = limᵢ r (λ y → ψ p σ (f (into (<→◃ q) (tr⁻ e (out (<→◃ r) y)))))
... | injᵇ _ = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
... | injᶜ _ = lim (λ n → ψ p σ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ p σ (up zero x)     = ψ p (λ q → σ (suc q)) x
ψ p σ (up (self n) x) = ψ p (λ q → σ (lim n q)) x

ψ⁰ : ∀ {k} → Ordᶜ k → Ordᶜ zero
ψ⁰ zero    = suc zero
ψ⁰ (suc a) = lim (iter (ψ⁰ a +_) zero)
ψ⁰ (lim f) = lim (λ n → ψ⁰ (f n))
ψ⁰ (limᵢ {i = j} q f) = lim (λ n → ψ⁰ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n))))
ψ⁰ (up zero x)     = ψ⁰ x
ψ⁰ (up (self n) x) = ψ⁰ x

FGH : Ordᶜ zero → ℕ → ℕ
FGH zero        n = suc n
FGH (suc a)     n = iter (FGH a) n n
FGH (lim f)     n = FGH (f n) n
FGH (limᵢ () f) n
FGH (up () x)   n
```

搬运的使用者清单: `ψ` 的穿透分支一处. $\Omega$ (`lim` 分支只放 `up (self n)`, 不比较)、`lift` (对 $\triangleleft$ 的证明)、`add` 与 `Sim` (`σ` 把字面证明映到字面证明)、`ψ⁰` (目标层 0 没有穿透) 都不用. 停机: `ψ` 的递归参数仍是树 (`f` 的像), `tr⁻` 是先定义好的函数.

## §5 跨层结构互模拟 $\cong$

Cumulative §4 的 $\cong$, 一处改动: `lᵢ≅` 允许两边的节点挂在 $\cong^\mathsf{I}$-相关的层 $j,j'$ 上 (多一个前提 $j\cong^\mathsf{I}j'$). 这是 §4 的直接后果: 两次穿透可能选到目标层里两个不同的代表元. 前提 $j\cong^\mathsf{I}j'$ 用在 `ψ-≅` 里排除派发不一致的组合.

```agda
module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
  data Eq₊ : ∀ {ℓ′} → Ordᶜ ℓ → Ordᶜ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ {ℓ′} zero zero
    s≅  : ∀ {ℓ′} {a : Ordᶜ ℓ} {b : Ordᶜ ℓ′} → Eq₊ a b → Eq₊ (suc a) (suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordᶜ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → Eq₊ (f n) (g n)) → Eq₊ (lim f) (lim g)
    lᵢ≅ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : U j (<→◃ p) → Ordᶜ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordᶜ j) (y : Ordᶜ j′) → R j (<→◃ p) (into (<→◃ p) x) y → Eq₊ (f (into (<→◃ p) x)) (g (into (<→◃ q) y))) →
          Eq₊ (limᵢ p f) (limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ (up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordᶜ ℓ} → Eq₊ a (out (◃₁→◃ r) y) → Eq₊ a (up r y)

R : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
R i zero         x b = Eq₊ i R x b
R i (suc r)      x b = R i r x b
R _ (self {f} n) x b = Eq₊ (f n) R x b
R i (lim n r)    x b = R i r x b

infix 4 _≅_
_≅_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
_≅_ {ℓ₁} = Eq₊ ℓ₁ R

R→≅ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → R i r (into r x) b → x ≅ b
R→≅ zero      e = e
R→≅ (suc r)   e = R→≅ r e
R→≅ (self n)  e = e
R→≅ (lim n r) e = R→≅ r e

≅→R : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → x ≅ b → R i r (into r x) b
≅→R zero      e = e
≅→R (suc r)   e = ≅→R r e
≅→R (self n)  e = e
≅→R (lim n r) e = ≅→R r e

R-conv : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordᶜ j} {b : Ordᶜ ℓ′} → R j r (into r x) b → R j r′ (into r′ x) b
R-conv r r′ e = ≅→R r′ (R→≅ r e)
```

**对称.** Cumulative 的 `R-flip` 只对第一个证明递归, 第二个用 `≅→R` 转换. 那里两边是同一个 $j$, 停机检查器从第一个证明看到 $j$ 低于一侧的层就够了. 这里两边是 $j,j'$, 原样照搬报 `[TerminationIssue] Termination checking failed for the following functions: ≅-sym, R-flip. Problematic calls: R-flip (<→◃ q) (<→◃ p) d, ≅-sym e`: 内层 `≅-sym` 的第二个层 $j$ 没被看到下降. 修复是两段递归: `R-flip` 对第一个证明递归到底, 再交给 `flipR` 对第二个证明递归到底, 然后才调用 `≅-sym`. 仍然不同时对两个证明分情况, 避开 Cumulative 记录的 `UnificationStuck`.

```agda
≅-sym   : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ a
R-flip  : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordᶜ j} {y : Ordᶜ j′} → R j r (into r x) y → R j′ r′ (into r′ y) x
flipR   : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordᶜ j} {y : Ordᶜ j′} → x ≅ y → R j′ r′ (into r′ y) x
≅-sym z≅      = z≅
≅-sym (s≅ e)  = s≅ (≅-sym e)
≅-sym (l≅ h)  = l≅ (λ n → ≅-sym (h n))
≅-sym (lᵢ≅ {p = p} {q = q} e h) = lᵢ≅ (≅ᴵ-sym e) (λ y x d → ≅-sym (h x y (R-flip (<→◃ q) (<→◃ p) d)))
≅-sym (upˡ {r = zero} e)    = upʳ (≅-sym e)
≅-sym (upˡ {r = self n} e)  = upʳ (≅-sym e)
≅-sym (upʳ {r = zero} e)    = upˡ (≅-sym e)
≅-sym (upʳ {r = self n} e)  = upˡ (≅-sym e)
R-flip zero      r′ e = flipR r′ e
R-flip (suc r)   r′ e = R-flip r r′ e
R-flip (self n)  r′ e = flipR r′ e
R-flip (lim n r) r′ e = R-flip r r′ e
flipR zero       e = ≅-sym e
flipR (suc r′)   e = flipR r′ e
flipR (self n)   e = ≅-sym e
flipR (lim n r′) e = flipR r′ e
```

**搬运在 $\cong$ 下不可见.** `tr-≅`: $x\cong y\Rightarrow$ `tr e x` $\cong y$, 对 $x\cong y$ 的推导递归, 在 `limᵢ` 处经 `back-≅` 递归到 `tr⁻-≅` ($e$ 的子证明). 四个引理的递归结构与 `tr`/`tr⁻`/`res`/`res⁻` 一一对应, 停机理由相同. 它们不用对称与传递, 所以排在传递之前, 传递反过来用它们.

```agda
tr-≅    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ a} {y : Ordᶜ ℓ′} → x ≅ y → tr e x ≅ y
tr⁻-≅   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ b} {y : Ordᶜ ℓ′} → x ≅ y → tr⁻ e x ≅ y
back-≅  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {v : Ordᶜ ℓ′} → u ≅ v → back (res q e) u ≅ v
back⁻-≅ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {v : Ordᶜ ℓ′} → u ≅ v → back (res⁻ q e) u ≅ v

tr-≅ e z≅      = z≅
tr-≅ e (s≅ d)  = s≅ (tr-≅ e d)
tr-≅ e (l≅ h)  = l≅ (λ n → tr-≅ e (h n))
tr-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eq (res q e))) ej) λ u v d →
    subst (λ w → tr e (f (into (<→◃ q) (back (res q e) w))) ≅ g (into (<→◃ q₂) v))
          (sym (out-into (<→◃ (lt (res q e))) u))
          (tr-≅ e (h _ v (≅→R (<→◃ q) (back-≅ q e (R→≅ (<→◃ (lt (res q e))) d)))))
tr-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr-≅ e d)
tr-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr-≅ (h n) d)
tr-≅ e (upʳ d) = upʳ (tr-≅ e d)

tr⁻-≅ e z≅      = z≅
tr⁻-≅ e (s≅ d)  = s≅ (tr⁻-≅ e d)
tr⁻-≅ e (l≅ h)  = l≅ (λ n → tr⁻-≅ e (h n))
tr⁻-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eq (res⁻ q e))) ej) λ u v d →
    subst (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ≅ g (into (<→◃ q₂) v))
          (sym (out-into (<→◃ (lt (res⁻ q e))) u))
          (tr⁻-≅ e (h _ v (≅→R (<→◃ q) (back⁻-≅ q e (R→≅ (<→◃ (lt (res⁻ q e))) d)))))
tr⁻-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻-≅ e d)
tr⁻-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻-≅ (h n) d)
tr⁻-≅ e (upʳ d) = upʳ (tr⁻-≅ e d)

back-≅ zero      (s≅ e) d = tr⁻-≅ e d
back-≅ (suc q)   (s≅ e) d = back-≅ q e d
back-≅ (lim n q) (l≅ h) d = back-≅ q (h n) d

back⁻-≅ zero      (s≅ e) d = tr-≅ e d
back⁻-≅ (suc q)   (s≅ e) d = back⁻-≅ q e d
back⁻-≅ (lim n q) (l≅ h) d = back⁻-≅ q (h n) d
```

**传递.** 两个 `lᵢ≅` 串起来时, 三个节点在 $j\cong j'\cong j''$ 三个层上; 中间元取 `tr e x` (第 $j'$ 层). 需要 $x\cong x$ (PER 的定义域), 由 `R-reflˡ` 在较低层用传递得到, 停机理由与 Cumulative 的 `R-reflʳ` 相同 (隐式层号沿 $\triangleleft$ 证明下降).

```agda
≅-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≅ b → b ≅ c → a ≅ c
R-reflˡ  : ∀ {j ℓ ℓ′} (r : j ◃ ℓ) {x : Ordᶜ j} {z : Ordᶜ ℓ′} → R j r (into r x) z → x ≅ x
≅-trans (upˡ {r = zero} e)   d = upˡ (≅-trans e d)
≅-trans (upˡ {r = self n} e) d = upˡ (≅-trans e d)
≅-trans d (upʳ {r = zero} e)   = upʳ (≅-trans d e)
≅-trans d (upʳ {r = self n} e) = upʳ (≅-trans d e)
≅-trans (upʳ {r = zero} e)   (upˡ e′) = ≅-trans e e′
≅-trans (upʳ {r = self n} e) (upˡ e′) = ≅-trans e e′
≅-trans z≅     z≅      = z≅
≅-trans (s≅ e) (s≅ e′) = s≅ (≅-trans e e′)
≅-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅-trans (h n) (h′ n))
≅-trans (lᵢ≅ {p = p} {q = q} e h) (lᵢ≅ e′ h′) =
  lᵢ≅ (≅ᴵ-trans e e′) λ x z d →
    ≅-trans (h x (tr e x) (≅→R (<→◃ p) (≅-sym (tr-≅ e (R-reflˡ (<→◃ p) d)))))
            (h′ (tr e x) z (≅→R (<→◃ q) (tr-≅ e (R→≅ (<→◃ p) d))))
R-reflˡ zero      e = ≅-trans e (≅-sym e)
R-reflˡ (suc r)   e = R-reflˡ r e
R-reflˡ (self n)  e = ≅-trans e (≅-sym e)
R-reflˡ (lim n r) e = R-reflˡ r e

≅-tr : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ a} → y ≅ x → y ≅ tr e x
≅-tr e d = ≅-sym (tr-≅ e (≅-sym d))

≅-tr⁻ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ b} → y ≅ x → y ≅ tr⁻ e x
≅-tr⁻ e d = ≅-sym (tr⁻-≅ e (≅-sym d))
```

**$\Omega$ 与提升.** `Ω-refl` 推广为 `Ω-≅` ($a\cong^\mathsf{I}b\Rightarrow\Omega_a\cong\Omega_b$), 证明形状不变. 提升的一致性 (`lift-≅`, `lift-coh`, `lift-comp`) 逐字搬来.

```agda
Ω-≅ : ∀ {a b} → a ≅ᴵ b → Ω a ≅ Ω b
Ω-≅ z≅     = s≅ z≅
Ω-≅ (s≅ e) = lᵢ≅ e (λ x y d → upˡ (upʳ d))
Ω-≅ (l≅ h) = l≅ (λ n → upˡ (upʳ (Ω-≅ (h n))))

Ω-refl : ∀ ℓ → Ω ℓ ≅ Ω ℓ
Ω-refl ℓ = Ω-≅ (≅ᴵ-refl ℓ)

lift-≅ : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {x : Ordᶜ k} {b : Ordᶜ ℓ′} → x ≅ b → lift r x ≅ b
lift-≅ zero      e = upˡ e
lift-≅ (suc r)   e = upˡ (lift-≅ r e)
lift-≅ (self n)  e = upˡ e
lift-≅ (lim n r) e = upˡ (lift-≅ r e)

lift-coh : ∀ {k ℓ₁ ℓ₂} (r : k ◃ ℓ₁) (r′ : k ◃ ℓ₂) {x : Ordᶜ k} → x ≅ x → lift r x ≅ lift r′ x
lift-coh r r′ e = lift-≅ r (≅-sym (lift-≅ r′ e))

lift-comp : ∀ {k m ℓ ℓ′} (r : k ◃ m) (r′ : m ◃ ℓ) (r″ : k ◃ ℓ′) {x : Ordᶜ k} → x ≅ x →
            lift r′ (lift r x) ≅ lift r″ x
lift-comp r r′ r″ e = lift-≅ r′ (lift-≅ r (≅-sym (lift-≅ r″ e)))
```

## §6 折叠尊重 $\cong$

`ψ-≅` 推广到 $\cong^\mathsf{I}$-相关的目标层: $i\cong^\mathsf{I}i'$, $a\cong b\Rightarrow\psi_p\,\sigma\,a\cong\psi_{p'}\,\sigma'\,b$. 推广是被迫的: 两边都走规则 6 时, 两条 $\gamma$-链分别在节点的层 $j$ 与 $j'$ 上, 链的每一步就是一次目标层为 $j$ (对 $j'$) 的折叠. 照搬 Cumulative 的同目标层陈述报 `[UnequalTerms] j != j′ of type Ordᴵ when checking that the expression ψ-≅ (h _ _ (≅→R (<→◃ q) d)) has type _G_504 x ≅ _G′_505 y`. 派发不一致的四种组合由 `clash₁`/`clash₂` 排除 (都归结为 $\prec^\mathsf{I}$ 无自反); 两边都穿透时, 输出的两个代表元 $j'_1,j'_2$ 经 $j'_1\cong j\cong j'\cong j'_2$ 相关, 分支经 `tr⁻-≅` 对上.

```agda
iter-R : ∀ {A B : Set} (Rel : A → B → Set) {G : A → A} {G′ : B → B} →
         (∀ {x y} → Rel x y → Rel (G x) (G′ y)) → ∀ {x y} → Rel x y → ∀ n → Rel (iter G x n) (iter G′ y n)
iter-R Rel h e zero    = e
iter-R Rel h e (suc n) = h (iter-R Rel h e n)

add-≅ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordᶜ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordᶜ k₁} {b′ : Ordᶜ k₂} →
        a ≅ a′ → b ≅ b′ → add a σ b ≅ add a′ σ′ b′
add-≅ ea z≅     = ea
add-≅ ea (s≅ e) = s≅ (add-≅ ea e)
add-≅ ea (l≅ h) = l≅ (λ n → add-≅ ea (h n))
add-≅ ea (upˡ {r = zero} e)   = add-≅ ea e
add-≅ ea (upˡ {r = self n} e) = add-≅ ea e
add-≅ ea (upʳ {r = zero} e)   = add-≅ ea e
add-≅ ea (upʳ {r = self n} e) = add-≅ ea e
add-≅ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ≅ e λ x y d →
  subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ≅ add a′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-into (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
         (add-≅ ea (h x y (R-conv (<→◃ (σ q)) (<→◃ q) d)))

clash₁ : ∀ {j j′ i i′} → j ≅ᴵ j′ → i ≅ᴵ i′ → j ≺ᴵ i → i′ ≺ᴵ j′ → ⊥
clash₁ e ei r s = ≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans (≺ᴵ-respʳ r ei) s) (≅ᴵ-sym e))

clash₂ : ∀ {j j′ i i′} → j ≅ᴵ j′ → i ≅ᴵ i′ → j ≺ᴵ i → j′ ≅ᴵ i′ → ⊥
clash₂ e ei r c = ≺ᴵ-irrefl (≺ᴵ-respʳ r (≅ᴵ-trans ei (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym e))))

ψ-≅ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
      {a : Ordᶜ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ≅ b → ψ p σ a ≅ ψ p′ σ′ b
ψ-≅ ei z≅ = Ω-≅ ei
ψ-≅ ei (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ-≅ ei e) e′) z≅)
ψ-≅ ei (l≅ h) = l≅ (λ n → ψ-≅ ei (h n))
ψ-≅ ei (upˡ {r = zero} e)   = ψ-≅ ei e
ψ-≅ ei (upˡ {r = self n} e) = ψ-≅ ei e
ψ-≅ ei (upʳ {r = zero} e)   = ψ-≅ ei e
ψ-≅ ei (upʳ {r = self n} e) = ψ-≅ ei e
ψ-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u))) ≅ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
         (sym (out-into (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
         (ψ-≅ ei (h _ _ (≅→R (<→◃ q) (tr⁻-≅ e₁ (≅-tr⁻ e₂ (R→≅ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ n → ψ-≅ ei (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
```

目标层 0: `ψ⁰` 尊重 $\cong$ (`ψ⁰-≅`, 两边都是 `ψ⁰`, 这是对角线要用的形式), 且与带证明的折叠一致 (`ψ⁰≅ψ`, 即 Cumulative 的 `ψ⁰-≅`; 穿透分支 `injᵃ (via _ ())` 荒谬). FGH 在 $\cong$ 下不变.

```agda
ψ⁰-≅ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ⁰ b
ψ⁰-≅ z≅     = s≅ z≅
ψ⁰-≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰-≅ e) e′) z≅)
ψ⁰-≅ (l≅ h) = l≅ (λ n → ψ⁰-≅ (h n))
ψ⁰-≅ (upˡ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upˡ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = zero} e)   = ψ⁰-≅ e
ψ⁰-≅ (upʳ {r = self n} e) = ψ⁰-≅ e
ψ⁰-≅ (lᵢ≅ {p = q} e h) = l≅ (λ n → ψ⁰-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)

ψ⁰≅ψ : ∀ {k₁ k₂ ℓ} {p : zero <ᴵ ℓ} {σ : Simᴵ k₂ ℓ} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ⁰ a ≅ ψ p σ b
ψ⁰≅ψ z≅     = s≅ z≅
ψ⁰≅ψ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ⁰≅ψ e) e′) z≅)
ψ⁰≅ψ (l≅ h) = l≅ (λ n → ψ⁰≅ψ (h n))
ψ⁰≅ψ (upˡ {r = zero} e)   = ψ⁰≅ψ e
ψ⁰≅ψ (upˡ {r = self n} e) = ψ⁰≅ψ e
ψ⁰≅ψ (upʳ {r = zero} e)   = ψ⁰≅ψ e
ψ⁰≅ψ (upʳ {r = self n} e) = ψ⁰≅ψ e
ψ⁰≅ψ {p = p} {σ = σ} (lᵢ≅ {p = q} {q = q′} e h) with <ᴵ-dec (σ q′) p
... | injᵃ (via _ ())
... | injᵇ _ = l≅ (λ n → ψ⁰≅ψ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)
... | injᶜ _ = l≅ (λ n → ψ⁰≅ψ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ e (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ e)

iter-ext : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ a n → iter f a n ≡ iter g a n
iter-ext h a zero    = refl
iter-ext {g = g} h a (suc n) = trans (h _) (cong g (iter-ext h a n))

FGH-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → ∀ n → FGH x n ≡ FGH y n
FGH-≅ z≅     n = refl
FGH-≅ (s≅ e) n = iter-ext (FGH-≅ e) n n
FGH-≅ (l≅ h) n = FGH-≅ (h n) n
FGH-≅ (lᵢ≅ {p = ()} e h) n
FGH-≅ (upˡ {r = ()} e) n
FGH-≅ (upʳ {r = ()} e) n
```

## §7 叶子为 $\cong$ 的结构序

Cumulative §6 逐字, 只有 `≺-respʳ` 的 `limᵢ` 情况改了: 左边经分支 $x$ (第 $j$ 层) 下降, 右边的节点在 $j'$ 层, 对应的分支取 `tr e x`.

```agda
infix 4 _≺_ _⊑_
data _≺_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  ≺z : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≅ b → c ≺ suc b
  ≺s : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≺ b → c ≺ suc b
  ≺l : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → c ≺ f n → c ≺ lim f
  ≺i : ∀ {ℓ₁ ℓ₂ j} {c : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
       (x : Ordᶜ j) → x ≅ x → c ≺ f (into (<→◃ p) x) → c ≺ limᵢ p f
  ≺u : ∀ {ℓ₁ ℓ₂ k} {c : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → c ≺ out (◃₁→◃ r) y → c ≺ up r y

_⊑_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ⊑ b = ∀ {ℓ} {c : Ordᶜ ℓ} → c ≺ a → c ≺ b

≺-respˡ : ∀ {ℓ₁ ℓ₁′ ℓ₂} {c : Ordᶜ ℓ₁} {c′ : Ordᶜ ℓ₁′} {b : Ordᶜ ℓ₂} → c ≅ c′ → c ≺ b → c′ ≺ b
≺-respˡ e (≺z e′)      = ≺z (≅-trans (≅-sym e) e′)
≺-respˡ e (≺s h)       = ≺s (≺-respˡ e h)
≺-respˡ e (≺l n h)     = ≺l n (≺-respˡ e h)
≺-respˡ e (≺i x ex h)  = ≺i x ex (≺-respˡ e h)
≺-respˡ e (≺u h)       = ≺u (≺-respˡ e h)

≺-respʳ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {a : Ordᶜ ℓ₂} {b : Ordᶜ ℓ₃} → c ≺ a → a ≅ b → c ≺ b
≺-respʳ h (upʳ {r = zero} e)   = ≺u (≺-respʳ h e)
≺-respʳ h (upʳ {r = self n} e) = ≺u (≺-respʳ h e)
≺-respʳ (≺u {r = zero} h)   (upˡ e) = ≺-respʳ h e
≺-respʳ (≺u {r = self n} h) (upˡ e) = ≺-respʳ h e
≺-respʳ (≺z e₀)   (s≅ e) = ≺z (≅-trans e₀ e)
≺-respʳ (≺s h)    (s≅ e) = ≺s (≺-respʳ h e)
≺-respʳ (≺l n h)  (l≅ e) = ≺l n (≺-respʳ h (e n))
≺-respʳ (≺i {p = p} x ex h) (lᵢ≅ e h′) =
  ≺i (tr e x) (tr-≅ e (≅-tr e ex)) (≺-respʳ h (h′ x (tr e x) (≅→R (<→◃ p) (≅-tr e ex))))

≅→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ⊑ b
≅→⊑ e h = ≺-respʳ h e

⊑-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p q h = q (p h)

⊑-lim : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ⊑ f n → a ⊑ lim f
⊑-lim n p h = ≺l n (p h)

lim-⊑ : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ⊑ b) → lim f ⊑ b
lim-⊑ k (≺l n h) = k n h

⊑-limᵢ : ∀ {ℓ₁ ℓ₂ j} {a : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
         (x : Ordᶜ j) → x ≅ x → a ⊑ f (into (<→◃ p) x) → a ⊑ limᵢ p f
⊑-limᵢ x ex p h = ≺i x ex (p h)

data Acc≺ {ℓ} (a : Ordᶜ ℓ) : Set where
  acc : (∀ {ℓ′} {b : Ordᶜ ℓ′} → b ≺ a → Acc≺ b) → Acc≺ a

acc≺ : ∀ {ℓ} (a : Ordᶜ ℓ) {ℓ′} {b : Ordᶜ ℓ′} → b ≺ a → Acc≺ b
acc≺ (suc a)          (≺z e)      = acc (λ h → acc≺ a (≺-respʳ h e))
acc≺ (suc a)          (≺s h)      = acc≺ a h
acc≺ (lim f)          (≺l n h)    = acc≺ (f n) h
acc≺ (limᵢ p f)       (≺i x ex h) = acc≺ (f (into (<→◃ p) x)) h
acc≺ (up zero y)      (≺u h)      = acc≺ y h
acc≺ (up (self n) y)  (≺u h)      = acc≺ y h

≺-irrefl : ∀ {ℓ} {a : Ordᶜ ℓ} → ¬ (a ≺ a)
≺-irrefl {a = a} = go (acc (acc≺ a)) where
  go : ∀ {ℓ} {a : Ordᶜ ℓ} → Acc≺ a → ¬ (a ≺ a)
  go (acc h) p = go (h p) p
```

$\prec$ 良基, 故无自反, $\sqsubseteq$ 不退化 (与 Cumulative 相同).

## §8 $\Omega$ 与 $\psi\circ\Omega$ 的单调性

陈述与 Cumulative §7–§9 相同: $a\sqsubseteq^\mathsf{I}b\Rightarrow\Omega_a\sqsubseteq\Omega_b$ (`Ω-mono`), $a\sqsubseteq^\mathsf{I}b\Rightarrow\psi_i(\Omega_a)\sqsubseteq\psi_i(\Omega_b)$ (`Ψ-mono`, 任意目标层、任意折叠证据), 以及目标层 0 的无证明版本 (`Ψ⁰-mono`). 改动都在 `s⊑ e q` 情况: 它现在给出 $a\cong^\mathsf{I}a'<^\mathsf{I}b$ 而不是 $a<b$, 证明先用 $\Omega$ (或 $\psi\circ\Omega$) 尊重 $\cong$ 把 $a$ 换成 $a'$, 再走原来的字面情况 (`below`, `Ψ<`, `Ψ⁰<` 逐字不变). `Ψ-suc` 的穿透分支用 `tr⁻`. `Ψ⁰-mono` 在 Cumulative 里是对**字面**的 $\sqsubseteq^0$ 陈述的; 这里是 $\cong$-版 (`_⊑_` 的第 0 层实例): 字面版在 `s⊑` 情况不成立, 因为 $a$ 与 $a'$ 只 $\cong^\mathsf{I}$.

```agda
𝟎 : ∀ {ℓ} → Ordᶜ ℓ
𝟎 = zero

z≺Ω : ∀ {ℓ₀} b → 𝟎 {ℓ₀} ≺ Ω b
z≺Ω zero      = ≺z z≅
z≺Ω (suc b)   = ≺i (suc zero) (s≅ z≅) (≺u (≺z z≅))
z≺Ω (lim f s) = ≺l 0 (≺u (z≺Ω (f 0)))

below : ∀ {a b} → a <ᴵ b → {x : Ordᶜ a} → x ≅ x → x ⊑ Ω b
below zero      ex h = ≺i _ ex (≺u h)
below {b = suc b} (suc q)   ex h = ≺i (Ω b) (Ω-refl b) (≺u (below q ex h))
below (lim n q) ex h = ≺l n (≺u (below q ex h))

Ω-mono : ∀ {a b} → a ⊑ᴵ b → Ω a ⊑ Ω b
Ω-mono {b = b} z⊑ (≺z e) = ≺-respˡ (≅-sym e) (z≺Ω b)
Ω-mono (s⊑ e q) (≺i x ex (≺u h)) = below q (tr-≅ e (≅-tr e ex)) (≺-respʳ h (≅-tr e ex))
Ω-mono (l⊑ k) (≺l n (≺u h))      = Ω-mono (k n) h

Ψ-suc : ∀ {i c ℓ ℓ′} {p : i <ᴵ ℓ} {σ : Simᴵ c ℓ} {p′ : i <ᴵ ℓ′} {σ′ : Simᴵ (suc c) ℓ′} →
        ψ p σ (Ω c) ⊑ ψ p′ σ′ (Ω (suc c))
Ψ-suc {i} {c = c} {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} with <ᴵ-dec (σ′ zero) p′
... | injᵃ (via {a′ = c′} e r) = ⊑-limᵢ (Ω c′) (Ω-refl c′)
        (subst (λ u → ψ p σ (Ω c) ⊑ ψ p′ σ′ (up zero (tr⁻ e u))) (sym (out-into (<→◃ r) (Ω c′)))
               (≅→⊑ (ψ-≅ (≅ᴵ-refl i) (≅-tr⁻ e (Ω-≅ e)))))
... | injᵇ _ = ⊑-lim 0 (≅→⊑ (ψ-≅ (≅ᴵ-refl i) (Ω-refl c)))
... | injᶜ _ = ⊑-lim 0 (≅→⊑ (ψ-≅ (≅ᴵ-refl i) (Ω-refl c)))

Ψ0 : ∀ {i ℓ ℓ′} b {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {p′ : i <ᴵ ℓ′} {σ′ : Simᴵ b ℓ′} →
     ψ p σ (Ω zero) ⊑ ψ p′ σ′ (Ω b)
Ψ0 {i} zero  = ≅→⊑ (ψ-≅ (≅ᴵ-refl i) (Ω-refl zero))
Ψ0 (suc b) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-trans (Ψ0 b {p = p} {σ = σ} {p′ = p′} {σ′ = λ q → σ′ (suc q)}) (Ψ-suc {p = p′} {σ = λ q → σ′ (suc q)})
Ψ0 (lim g t) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-lim 0 (Ψ0 (g 0) {p = p} {σ = σ} {p′ = p′} {σ′ = λ q → σ′ (lim 0 q)})

Ψ< : ∀ {i a b ℓ ℓ′} → a <ᴵ b → {p : i <ᴵ ℓ} {σ : Simᴵ (suc a) ℓ} {p′ : i <ᴵ ℓ′} {σ′ : Simᴵ b ℓ′} →
     ψ p σ (Ω (suc a)) ⊑ ψ p′ σ′ (Ω b)
Ψ< {i} zero = ≅→⊑ (ψ-≅ (≅ᴵ-refl i) (Ω-refl _))
Ψ< (suc q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-trans (Ψ< q {p = p} {σ = σ} {p′ = p′} {σ′ = λ r → σ′ (suc r)}) (Ψ-suc {p = p′} {σ = λ r → σ′ (suc r)})
Ψ< (lim n q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-lim n (Ψ< q {p = p} {σ = σ} {p′ = p′} {σ′ = λ r → σ′ (lim n r)})

sim-s : ∀ {a b c} → a <ᴵ b → c <ᴵ suc a → c <ᴵ b
sim-s q zero    = q
sim-s q (suc r) = <ᴵ-trans r q

Ψ-mono : ∀ {i a b ℓ ℓ′} → a ⊑ᴵ b → {p : i <ᴵ ℓ} {σ : Simᴵ a ℓ} {p′ : i <ᴵ ℓ′} {σ′ : Simᴵ b ℓ′} →
         ψ p σ (Ω a) ⊑ ψ p′ σ′ (Ω b)
Ψ-mono {b = b} z⊑ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} = Ψ0 b {p = p} {σ = σ} {p′ = p′} {σ′ = σ′}
Ψ-mono {i} (s⊑ e q) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  ⊑-trans (≅→⊑ (ψ-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = λ r → σ′ (sim-s q r)} (≅ᴵ-refl i) (Ω-≅ (s≅ e))))
          (Ψ< q {p = p′} {σ = λ r → σ′ (sim-s q r)} {p′ = p′} {σ′ = σ′})
Ψ-mono (l⊑ k) {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} =
  lim-⊑ (λ n → Ψ-mono (k n) {p = p} {σ = λ r → σ (lim n r)} {p′ = p′} {σ′ = σ′})

Ψ⁰-suc : ∀ c → ψ⁰ (Ω c) ⊑ ψ⁰ (Ω (suc c))
Ψ⁰-suc c h = ≺l 0 h

Ψ⁰0 : ∀ b → ψ⁰ (Ω zero) ⊑ ψ⁰ (Ω b)
Ψ⁰0 zero      h = h
Ψ⁰0 (suc b)   h = Ψ⁰-suc b (Ψ⁰0 b h)
Ψ⁰0 (lim g t) h = ≺l 0 (Ψ⁰0 (g 0) h)

Ψ⁰< : ∀ {a b} → a <ᴵ b → ψ⁰ (Ω (suc a)) ⊑ ψ⁰ (Ω b)
Ψ⁰< zero      h = h
Ψ⁰< {b = suc b} (suc q) h = Ψ⁰-suc b (Ψ⁰< q h)
Ψ⁰< (lim n q) h = ≺l n (Ψ⁰< q h)

Ψ⁰-mono : ∀ {a b} → a ⊑ᴵ b → ψ⁰ (Ω a) ⊑ ψ⁰ (Ω b)
Ψ⁰-mono {b = b} z⊑ = Ψ⁰0 b
Ψ⁰-mono (s⊑ e q)   = ⊑-trans (≅→⊑ (ψ⁰-≅ (Ω-≅ (s≅ e)))) (Ψ⁰< q)
Ψ⁰-mono (l⊑ k) (≺l n h) = Ψ⁰-mono (k n) h

z≺ψ⁰ : ∀ {ℓ₀ k} (y : Ordᶜ k) → 𝟎 {ℓ₀} ≺ ψ⁰ y
z≺ψ⁰ zero            = ≺z z≅
z≺ψ⁰ (suc a)         = ≺l 1 (z≺ψ⁰ a)
z≺ψ⁰ (lim f)         = ≺l 0 (z≺ψ⁰ (f 0))
z≺ψ⁰ (limᵢ {i = j} q f) = ≺l 0 (z≺ψ⁰ (f (into (<→◃ q) (Ω j))))
z≺ψ⁰ (up zero x)     = z≺ψ⁰ x
z≺ψ⁰ (up (self n) x) = z≺ψ⁰ x
```

`Ψ⁰-mono` 是对角线的引擎: 层号一步 $L_n\sqsubseteq^\mathsf{I}L_{n+1}$ 推出下一项一步 $\psi^0(\Omega_{L_n})\sqsubseteq\psi^0(\Omega_{L_{n+1}})$ (Diagonal §2).

## §9 遗传步进 `HS` 与证书 `toLevel`

`HS` 按接口定义, $\sqsubseteq^0$ 是 §7 的 $\sqsubseteq$ 在第 0 层的实例 (叶子为 $\cong$). 第 0 层没有 `limᵢ` 与 `up`, 第 0 层的 $\cong$ 对一切树自反.

```agda
infix 4 _⊑⁰_
_⊑⁰_ : Ordᶜ zero → Ordᶜ zero → Set
a ⊑⁰ b = a ⊑ b

data HS : Ordᶜ zero → Set where
  hz : HS zero
  hs : ∀ {a} → HS a → HS (suc a)
  hl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → HS (f n)) → (∀ n → f n ⊑⁰ f (suc n)) → HS (lim f)

hs⁻ : ∀ {a} → HS (suc a) → HS a
hs⁻ (hs h) = h

hl₁ : ∀ {f : ℕ → Ordᶜ zero} → HS (lim f) → ∀ n → HS (f n)
hl₁ (hl h st) = h

hl₂ : ∀ {f : ℕ → Ordᶜ zero} → HS (lim f) → ∀ n → f n ⊑⁰ f (suc n)
hl₂ (hl h st) = st

≅-refl⁰ : (x : Ordᶜ zero) → x ≅ x
≅-refl⁰ zero        = z≅
≅-refl⁰ (suc x)     = s≅ (≅-refl⁰ x)
≅-refl⁰ (lim f)     = l≅ (λ n → ≅-refl⁰ (f n))
≅-refl⁰ (limᵢ () f)
≅-refl⁰ (up () x)
```

**`toLevel`.** 对树 $x$ 递归, 证书只经反演 `hs⁻`/`hl₁`/`hl₂` 读取. `lim` 的证据由 `toLevel-⊑` 现场给出: $a\sqsubseteq^0b$ (前驱包含, 叶子 $\cong$) 翻译成 $\mathtt{toLevel}\,a\sqsubseteq^\mathsf{I}\mathtt{toLevel}\,b$. 后继情况把 $a_0\prec\mathrm{suc}\,a_0$ 喂给 $a\sqsubseteq^0b$, 得到 $a_0\prec b$, 由 `toLevel-≺` 对这个推导递归 (`≺z` 的叶子由 `toLevel-≅` 翻译成 $\cong^\mathsf{I}$). 四个函数互递归, 类型里出现 `toLevel` 的隐式参数都落在比原树小的子树上, 停机检查通过.

最初的写法对证书 $h$ 递归 (`toLevel _ (hl h st) = …`), 同样通过检查, 但它在证书是抽象假设 (例如 `Uniform a`) 时卡住: 层号连 `lim` 的头都算不出来. 对 $x$ 递归后, 层号的骨架只依赖 $x$, 证书只提供步进证据.

```agda
s⊑′ : ∀ {a b} → a ≺ᴵ b → suc a ⊑ᴵ b
s⊑′ (via e q) = s⊑ e q

≺-suc : ∀ {a b} → a ≺ᴵ b → a ≺ᴵ suc b
≺-suc (via e q) = via e (suc q)

≺-lim : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a ≺ᴵ f n → a ≺ᴵ lim f s
≺-lim n (via e q) = via e (lim n q)

toLevel   : (x : Ordᶜ zero) → HS x → Ordᴵ
toLevel-⊑ : ∀ {a b} (ha : HS a) (hb : HS b) → a ⊑⁰ b → toLevel a ha ⊑ᴵ toLevel b hb
toLevel-≺ : ∀ {c b} (hc : HS c) (hb : HS b) → c ≺ b → toLevel c hc ≺ᴵ toLevel b hb
toLevel-≅ : ∀ {a b} (ha : HS a) (hb : HS b) → a ≅ b → toLevel a ha ≅ᴵ toLevel b hb

toLevel zero        h = zero
toLevel (suc a)     h = suc (toLevel a (hs⁻ h))
toLevel (lim f)     h = lim (λ n → toLevel (f n) (hl₁ h n)) (λ n → toLevel-⊑ (hl₁ h n) (hl₁ h (suc n)) (hl₂ h n))
toLevel (limᵢ () f) h
toLevel (up () x)   h

toLevel-⊑ {a = zero}      ha hb k = z⊑
toLevel-⊑ {a = suc a}     ha hb k = s⊑′ (toLevel-≺ (hs⁻ ha) hb (k (≺z (≅-refl⁰ a))))
toLevel-⊑ {a = lim f}     ha hb k = l⊑ (λ n → toLevel-⊑ (hl₁ ha n) hb (λ d → k (≺l n d)))
toLevel-⊑ {a = limᵢ () f} ha hb k
toLevel-⊑ {a = up () x}   ha hb k

toLevel-≺ hc hb (≺z e)   = via (toLevel-≅ hc (hs⁻ hb) e) zero
toLevel-≺ hc hb (≺s d)   = ≺-suc (toLevel-≺ hc (hs⁻ hb) d)
toLevel-≺ hc hb (≺l n d) = ≺-lim n (toLevel-≺ hc (hl₁ hb n) d)
toLevel-≺ hc hb (≺i {p = ()} x ex d)
toLevel-≺ hc hb (≺u {r = ()} d)

toLevel-≅ ha hb z≅     = z≅
toLevel-≅ ha hb (s≅ e) = s≅ (toLevel-≅ (hs⁻ ha) (hs⁻ hb) e)
toLevel-≅ ha hb (l≅ k) = l≅ (λ n → toLevel-≅ (hl₁ ha n) (hl₁ hb n) (k n))
toLevel-≅ ha hb (lᵢ≅ {p = ()} e k)
toLevel-≅ ha hb (upˡ {r = ()} e)
toLevel-≅ ha hb (upʳ {r = ()} e)
```

**忠实性.** 对任意证书 $h$: 层号 `toLevel (lim f) h` 的第 $n$ 项**定义性地**是 `toLevel (f n) _` (`toLevel-lim`), $\Omega$ 在它上的第 $n$ 项定义性地是 $\Omega_{\mathtt{toLevel}(f\,n)}$ (`Ω-exact`). 对照 Cumsum §0 与 Certified §7: `ordᴰ` 把 $\lim f$ 换成 $\lim(\mathrm{cumsum}(\mathsf{ord}^\mathsf{D}\circ f))$, $\omega$ 的层号第 2 项是 5 (下面最后一行, `refl`); 这里是 2.

```agda
_[_]ᴵ : Ordᴵ → ℕ → Ordᴵ
lim f _ [ n ]ᴵ = f n
a       [ n ]ᴵ = a

module _ {f : ℕ → Ordᶜ zero} {h : HS (lim f)} where
  toLevel-lim : toLevel (lim f) h ≡ lim (λ n → toLevel (f n) (hl₁ h n)) (λ n → toLevel-⊑ (hl₁ h n) (hl₁ h (suc n)) (hl₂ h n))
  toLevel-lim = refl

  toLevel-seq : ∀ n → toLevel (lim f) h [ n ]ᴵ ≡ toLevel (f n) (hl₁ h n)
  toLevel-seq n = refl

  Ω-exact : Ω (toLevel (lim f) h) ≡ lim (λ n → up (self n) (Ω (toLevel (f n) (hl₁ h n))))
  Ω-exact = refl

natᶜ : ℕ → Ordᶜ zero
natᶜ zero    = zero
natᶜ (suc n) = suc (natᶜ n)

natᶜ-HS : ∀ n → HS (natᶜ n)
natᶜ-HS zero    = hz
natᶜ-HS (suc n) = hs (natᶜ-HS n)

ωᶜ : Ordᶜ zero
ωᶜ = lim natᶜ

ωᶜ-HS : HS ωᶜ
ωᶜ-HS = hl natᶜ-HS (λ n h → ≺s h)

_ : toLevel ωᶜ ωᶜ-HS [ 2 ]ᴵ ≡ suc (suc zero)
_ = refl

_ : cumsum (ordᴰ ∘ natᴼ) 2 ≡ nat 5
_ = refl
```

**遗忘.** `forget` 把层号读回第 0 层的树. `forget (toLevel x h)` 与 $x$ 只在 $\cong$ 下相等 (`forget-toLevel`): `lim` 情况两边是 `lim (λ n → forget (toLevel (f n) _))` 与 `lim f`, 字面相等需要函数外延性. 这不影响任何使用: $\Omega$ 读的是层号本身, 逐项就是 $x$ 的各项的层号 (`Ω-exact`).

```agda
forget : Ordᴵ → Ordᶜ zero
forget zero      = zero
forget (suc a)   = suc (forget a)
forget (lim f _) = lim (forget ∘ f)

forget-toLevel : ∀ x (h : HS x) → forget (toLevel x h) ≅ x
forget-toLevel zero        h = z≅
forget-toLevel (suc a)     h = s≅ (forget-toLevel a (hs⁻ h))
forget-toLevel (lim f)     h = l≅ (λ n → forget-toLevel (f n) (hl₁ h n))
forget-toLevel (limᵢ () f) h
forget-toLevel (up () x)   h
```

## §10 移植清单

相对 [Cumulative](Cumulative.lagda.md) (下标 `Ordʷ` → `Ordᴵ`):

| 名字 | 状态 | 说明 |
|---|---|---|
| `◃`, `◃₁`, `U`, `Ordᶜ`, `into`, `out`, `out-into`, `coe`, `lift` | 逐字 | |
| `Ω`, `add`, `_+_`, `ψ⁰`, `FGH` | 逐字 | |
| `ψ` | 改一个分支 | 穿透: 节点挂在代表元 $j'$ 上, 分支经 `tr⁻ e`; 规则 4/5ω/6 与提升逐字 |
| `<ʷ-dec` → `<ᴵ-dec` | 改结论 | 三种情况都模 $\cong^\mathsf{I}$ (第一种不能字面, `lit→ext`) |
| `<ʷ-irrefl` → `≺ᴵ-irrefl` | 改陈述 | 模 $\cong^\mathsf{I}$ 的无自反 |
| `≅` (`Eq₊`) | 改 `lᵢ≅` | 两边节点可在 $\cong^\mathsf{I}$-相关的层, 多一个前提 |
| `R`, `R→≅`, `≅→R`, `R-conv` | 逐字 | |
| `≅-sym`/`R-flip` | 证明改 | 两段递归 `R-flip`+`flipR` (停机) |
| `≅-trans`/`R-reflʳ` | 证明改 | 中间元取 `tr e x`; `R-reflˡ` |
| `Ω-refl` | 推广 | `Ω-≅` |
| `lift-≅`, `lift-coh`, `lift-comp` | 逐字 | |
| `add-≅` | 几乎逐字 | 传递 `lᵢ≅` 的新前提 |
| `ψ-≅` | 推广 | 目标层 $i\cong^\mathsf{I}i'$ (被迫); 四个矛盾组合用 `clash₁`/`clash₂` |
| `ψ⁰-≅` | 拆成两个 | `ψ⁰-≅` (两边 `ψ⁰`, 新), `ψ⁰≅ψ` (原 `ψ⁰-≅`) |
| `FGH-≅`, `iter-R`, `iter-ext` | 逐字 | |
| `≺`, `⊑`, `≺-respˡ`, `≅→⊑`, `⊑-*`, `acc≺`, `≺-irrefl` | 逐字 | |
| `≺-respʳ` | 证明改一处 | `lᵢ≅` 情况的分支取 `tr e x` |
| `below`, `Ψ0`, `Ψ<`, `Ψ⁰0`, `Ψ⁰<`, `z≺Ω` | 逐字 | |
| `Ω-mono`, `Ψ-mono` | 陈述逐字, 证明改 `s⊑` 情况 | 先经 `Ω-≅`/`ψ-≅` 换代表元 |
| `Ψ-suc` | 证明改穿透分支 | 用 `tr⁻` |
| `Ψ⁰-mono` | 改为 $\cong$-版 | 字面版在 `s⊑` 情况不成立 |
| `tr`, `tr⁻`, `res`, `res⁻`, `tr-≅`, `tr⁻-≅`, `back-≅`, `back⁻-≅` | 新 | 层间结构搬运 |
| `HS`, `toLevel`, `toLevel-⊑`/`≺`/`≅`, `forget-toLevel` | 新 | 证书 |

未移植 (与本文的任务无关, 都在 Cumulative 里): 方向 B/C 的实验、`ψ-not-⊑mono` 反例 (它只依赖树族在第 1 层的形状, 原样成立)、$x_3$ 的专门检验 (被 Diagonal 的一般对角线取代)、第 0 层的字面关系 `≺⁰`.

## §11 对比: R1 与 R2

| | R1 内部 (`data Ordᴵ`, 本文) | R2 外部 ($\Sigma$ + 谓词) |
|---|---|---|
| 作树族下标 | 直接; `U` 对 $<^\mathsf{I}$/$\triangleleft$ 的证明递归, 照常通过 | 序对作下标: `UnsolvedMetaVariables` 或 `TerminationIssue` (§3); 只能以裸树为下标 |
| 有界三歧性的证据 | 在层号里, `<ᴵ-dec` 无额外参数 | 在树外, `ψ`, `ψ⁰`, `ψ-≅`, `Ψ-mono` 都要多一个证据参数并沿 `σ`/`◃` 限制 |
| 三歧性的结论 | 模 $\cong^\mathsf{I}$ | 同 (§2 的论证与表示无关) |
| 层间搬运 | 需要, `ψ` 穿透一处 | 同 |
| `toLevel` | 互递归 (`toLevel-⊑`/`≺`/`≅`), 通过停机检查 | 不平凡: 接口的 `HS` 在 `Ordᶜ zero` 上, 层号在裸树上, 要遗忘并翻译证据 |
| 基本列的忠实性 | `refl` (`toLevel-lim`, `Ω-exact`), 对任意证书 | 同 (遗忘逐项) |
| 归纳-归纳的成本 | 四个类型同时定义; $\sqsubseteq^\mathsf{I}$ 必须归纳 (函数式不严格正) | 谓词与关系可以分开定义 |

## §12 结论与边界

**已形式化** (全部 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示):

1. 下标类型 `Ordᴵ` (R1): `lim` 证据为模 $\cong^\mathsf{I}$ 的前驱包含; $\cong^\mathsf{I}$ 是等价关系; 有界三歧性 `<ᴵ-dec` (三种情况都模 $\cong^\mathsf{I}$), $\prec^\mathsf{I}$ 无自反、传递、两侧尊重 $\cong^\mathsf{I}$.
2. 否定: 字面的第一种情况推出函数外延性的实例 (`lit→ext`); 函数式的 $\sqsubseteq^\mathsf{I}$ 不严格正; R2 的序对下标过不了归纳-递归 (§3 的确切报错).
3. 层间结构搬运 `tr`/`tr⁻` 及其在 $\cong$ 下的不可见性; `ψ` 用它恰好一处 (穿透). $\Omega$, `lift`, `add`, `Sim`, `ψ⁰` 不用.
4. 树族、`ψ` (忠实规则 4/5ω/5Ω/6)、`ψ⁰`、$\cong$ (PER, 对一切树对称传递)、`ψ-≅` (推广到相关目标层)、`ψ⁰-≅`、`FGH-≅`、$\prec/\sqsubseteq$、`Ω-mono`、`Ψ-mono`、`Ψ⁰-mono`; 移植清单见 §10.
5. `HS` 与 `toLevel`: 对树递归, 互递归的 `toLevel-⊑` 给出 `lim` 证据; 基本列逐项 `refl`, 对任意证书; 无填充 (对照 `cumsum` 的 5).

**边界.**

- `Uniform` (安全路径引理) 不在本文; 对角线的组装以它为模块参数 ([Diagonal](Diagonal.lagda.md)).
- `forget ∘ toLevel` 只在 $\cong$ 下是恒等; `≡` 要函数外延性.
- 三歧性模 $\cong^\mathsf{I}$ 意味着树族在 $\cong^\mathsf{I}$-相关的层之间不共享类型, 只靠 `tr` 搬运. 搬运只在 $\cong$ 下透明; 字面上 `tr e x` 与 $x$ 在不同的类型里.
- 树的序数标签: 本文不重做对齐, `ψ` 的规则形状与 Cumulative/Finite 的 $\psi^\mathsf{E}$ 相同 (穿透分支只多一个在 $\cong$ 下不可见的搬运).
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
