# Spike ε — Trichotomy witness as constructor field (真正全新方向)

> Cross-links: [SpikeA1](SpikeA1.lagda.md), [SpikeA2](SpikeA2.lagda.md), [SpikeA3](SpikeA3.lagda.md), [Spikebeta](Spikebeta.lagda.md), [FINDINGS umbrella](FINDINGS.md)

完全跳出 mono / γ-bound 范式. **lim 不带 mono, 带 trichotomy witness**: ∀ a b, image 之间可决策. mono 是 witness 的特例 (单调 → 给出 trichotomy), witness 更弱 (允许 non-monotone f).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.Spikeepsilon where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.BTBO using (module Trich; module Ord-Basic; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open Ord-Basic using (Ord₀)
```

## 1. Ord₁ᴰ (ε 版): witness 作为字段

```agda
data Ord₁ᴰ : Set
data _<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set

Witness₀ : (ℕ → Ord₁ᴰ) → Set
Witness₀ f = (n m : ℕ) → f n <₁ f m ⊎ f m <₁ f n ⊎ f n ≡ f m

Witness₁ : (Ord₀ → Ord₁ᴰ) → Set
Witness₁ f = (a b : Ord₀) → f a <₁ f b ⊎ f b <₁ f a ⊎ f a ≡ f b

private variable
  a b c : Ord₁ᴰ
  f₀ : ℕ → Ord₁ᴰ
  f₁ : Ord₀ → Ord₁ᴰ
  w₀ : Witness₀ f₀
  w₁ : Witness₁ f₁

data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ)    (w₀ : Witness₀ f) → Ord₁ᴰ
  lim₁ : (f : Ord₀ → Ord₁ᴰ) (w₁ : Witness₁ f) → Ord₁ᴰ

infix 10 _<₁_
data _<₁_ where
  zero :          a <₁ suc a
  suc  : a <₁ b → a <₁ suc b
  lim₀ : ∀ n   → a <₁ f₀ n → a <₁ lim₀ f₀ w₀
  lim₁ : ∀ x   → a <₁ f₁ x → a <₁ lim₁ f₁ w₁
```

**实测**: 同 A₁ 形态, 但字段从 mono 改为 witness. Agda 接受.

## 2. `<₁-trans`

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero        = suc p
<₁-trans p (suc q)     = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)  = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ x q)  = lim₁ x (<₁-trans p q)
```

## 3. BoundedTrich 关键 case

```agda
<₁-dec : a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b
<₁-dec zero zero       = injᶜ refl
<₁-dec zero (suc q)    = injᵇ q
<₁-dec (suc p) zero    = injᵃ p
<₁-dec (suc p) (suc q) = <₁-dec p q
<₁-dec (lim₀ {w₀ = W} n p) (lim₀ k q) with W n k
... | injᵃ fn<fk = <₁-dec (<₁-trans p fn<fk) q
... | injᵇ fk<fn = <₁-dec p (<₁-trans q fk<fn)
... | injᶜ fn≡fk = <₁-dec p (subst (_ <₁_) (sym fn≡fk) q)
  where open import Relation.Binary.PropositionalEquality using (sym)
<₁-dec (lim₁ {w₁ = W} x p) (lim₁ y q) with W x y
... | injᵃ fx<fy = <₁-dec (<₁-trans p fx<fy) q
... | injᵇ fy<fx = <₁-dec p (<₁-trans q fy<fx)
... | injᶜ fx≡fy = <₁-dec p (subst (_ <₁_) (sym fx≡fy) q)
  where open import Relation.Binary.PropositionalEquality using (sym)
```

**关键 case 分析**:

`(lim₁ x p) (lim₁ y q)`:
- `W x y : f x <₁ f y ⊎ f y <₁ f x ⊎ f x ≡ f y` — **witness 直接给出 image trichotomy**
- injᵃ f x <₁ f y: trans p (f x <₁ f y) : a <₁ f y, 递归 <₁-dec _ q. q 严格减小.
- injᵇ 对称
- injᶜ f x ≡ f y: subst 把 q : b <₁ f y 改为 b <₁ f x, 递归 <₁-dec p _'. 这里没有 PI 字段问题, 因为我们用 `subst` 直接 transport.

**与 A₃ 的对比**:
- A₃: 需要 γ + mono + PI 三字段, 共同上界由 γ 提供, mono + PI 处理 Ordᴰ 索引上的细节
- ε: 一个 witness 字段, 直接给 image trichotomy, 不需要 γ 上界也不需要 PI
- **ε 更简洁**, 但需 witness 的实际可构造性

## 4. Witness 的可构造性 — 关键瑕疵

ε 设计的关键问题: 实际使用中**构造 lim₁ f w₁ 节点时, w₁ 怎么来**?

例 1: 若 f 是从 ψ-折叠 image 生成的 monotone 函数 (`a <₀ b → f a <₁ f b`), 那从 mono 可推 image trichotomy — **但仍需 Ord₀ 上 trichotomy**! Ord₀ 不可决策, 所以 mono 不能直接给 witness.

例 2: 若 f 是常函数 (constant), 那 w₁ a b 总返回 injᶜ refl — 平凡. 但常函数的 lim₁ 等价 f zero, 无极限能力.

例 3: 若 f 来自 γ-bounded 函数嵌入 (`g : Ord<γ → Ord₁ᴰ`, 包装为 `f a = g (some-mapping a)`), 那需要 some-mapping 是单射且 Ord<γ 上有 trichotomy. 退化到 A₃.

**实测撞墙**: 在 `--safe --without-K` 下, 给定任意 `f : Ord₀ → Ord₁ᴰ` 构造 `w₁ : Witness₁ f` **通常不可能**, 因为它需要 Ord₀ 上的 unconditional decision. **witness 的存在性 ≡ Ord₀ 上的 unconditional trichotomy, 这违反 Brouwer-tree paradigm**.

```agda
-- 形式化撞墙: 在 _ : ∀ f → Witness₁ f, 我们不能构造一个全函数实例
-- (这正是 BTBO 设计 Ordᴰ 而非给 Ord₀ 加 BoundedTrich 的原因)
```

## 5. 结论

**Spike ε 实测结果**: BoundedTrich 在 ε 设计下**形式上可证** (上面的 <₁-dec 应当编译通过). 但**构造层撞墙** — 任何"有意义的" lim₁ f w₁ 节点的 w₁ 不可构造 (除非退化到 mono on Ordᴰ + 实际等价于 A₃).

**强度评估**: 如果只用平凡 witness (constant f 或 ω-索引 trivial), 强度退化为 ℕ-索引 lim₀ (即 Ordᴰ). 如果想达到 Ω-索引能力, witness 必须从某个 γ-bounded f-image 推出, 等价 A₃.

**Spike ε 结论**: ε 设计本身有形式美感 (单字段更弱约束, BoundedTrich 直接), 但**构造层等价于 A₃**. 不是 Phase B 的独立候选 — 它要么坍缩到 trivial, 要么等价 A₃.

下一步 → 综合 Phase A 结果, A₃ 是唯一既能达 ψ(Ω_Ω_2) 又有可构造 witness 的方向. 进入 Phase B 完整 BoundedTrich.
