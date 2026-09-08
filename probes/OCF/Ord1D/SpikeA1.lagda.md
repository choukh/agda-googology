# Spike A₁ — mono on Ord₀ (历史撞墙, 重新验证)

> Cross-links: [SpikeA2](SpikeA2.lagda.md), [SpikeA3](SpikeA3.lagda.md), [Spikebeta](Spikebeta.lagda.md), [Spikeepsilon](Spikeepsilon.lagda.md), [FINDINGS umbrella](FINDINGS.md)

类比 [Ordᴰ](../../../src/OCF/BTBO.lagda.md#L639) 的 `lim : (f : ℕ → Ordᴰ) (mono : monotonic f) → Ordᴰ` 直接对偶到 Ord₁ 的 lim₁: `lim₁ : (f : Ord₀ → Ord₁ᴰ) (mono₁ : monotonic₁ f) → Ord₁ᴰ`, 其中 `monotonic₁ f = ∀ {a b : Ord₀} → a <₀ b → f a <₁ f b`.

历史判断: Ord₀ 自身不满足 BoundedTrich (BTBO 设计 BoundedTrich 是 Ord₀ → Ordᴰ 的关键约束), 给 lim₁ 加 mono on Ord₀ 时, (lim₁, lim₁) case 仍需决定 Ord₀ 上 trichotomy, 撞墙.

**本 spike 的目的**: 形式化撞墙位置, 显式记录是哪个 case 卡死, 区分与 Mahlo Phase 2 的撞墙类型.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.SpikeA1 where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.BTBO using (module Trich; module Ord-Basic; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open Ord-Basic using (Ord₀)
```

## 1. 先给 Ord₀ 加上 `_<₀_` 关系

BTBO 的 [Ord-Basic 模块](../../../src/OCF/BTBO.lagda.md#L85) 只给了 Ord₀ 的 data 定义, 没定义 < 关系. 这里补上 (类似 Ordᴰ 的 < 但无 mono 字段):

```agda
infix 10 _<₀_
data _<₀_ : Ord₀ → Ord₀ → Set where
  zero : ∀ {a} → a <₀ Ord-Basic.suc a
  suc  : ∀ {a b} → a <₀ b → a <₀ Ord-Basic.suc b
  lim  : ∀ {a f} (n : ℕ) → a <₀ f n → a <₀ Ord-Basic.lim f
```

注意: `<₀` 上不可能有 BoundedTrich, 因为 Ord-Basic.lim 接受任意 `ℕ → Ord₀`, 无单调性. 这是 BTBO 故意"不修" Ord₀ 的原因 — 真正驯化的是 Ordᴰ.

## 2. Ord₁ᴰ (A₁ 版): mono on Ord₀

互归纳定义 Ord₁ᴰ 和 _<₁_ (类似 Ordᴰ 的 induction-induction 结构):

```agda
data Ord₁ᴰ : Set
data _<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set

monotonic₀ : (ℕ → Ord₁ᴰ) → Set
monotonic₀ f = ∀ {n m} → n <ᴺ m → f n <₁ f m

monotonic₁ : (Ord₀ → Ord₁ᴰ) → Set
monotonic₁ f = ∀ {a b : Ord₀} → a <₀ b → f a <₁ f b

private variable
  a b c : Ord₁ᴰ
  f₀ : ℕ → Ord₁ᴰ
  f₁ : Ord₀ → Ord₁ᴰ
  mono₀ : monotonic₀ f₀
  mono₁ : monotonic₁ f₁

data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ) (mono₀ : monotonic₀ f) → Ord₁ᴰ
  lim₁ : (f : Ord₀ → Ord₁ᴰ) (mono₁ : monotonic₁ f) → Ord₁ᴰ

infix 10 _<₁_
data _<₁_ where
  zero :         a <₁ suc a
  suc  : a <₁ b → a <₁ suc b
  lim₀ : ∀ n   → a <₁ f₀ n → a <₁ lim₀ f₀ mono₀
  lim₁ : ∀ x   → a <₁ f₁ x → a <₁ lim₁ f₁ mono₁
```

**实测**: Agda 接受这个 induction-induction 定义, positivity 检查通过. 与 [BTBO Ordᴰ](../../../src/OCF/BTBO.lagda.md#L643-L662) 结构同形, 多一个 lim₁ 构造子.

## 3. `<₁-trans` 传递性

类比 [BTBO `<-trans`](../../../src/OCF/BTBO.lagda.md#L681) (对 q 归纳):

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero        = suc p
<₁-trans p (suc q)     = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)  = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ x q)  = lim₁ x (<₁-trans p q)
```

**实测**: 通过, 完全对偶 Ordᴰ 模式. lim₁ case 与 lim₀ case 形态一致.

## 4. BoundedTrich 尝试: 撞墙位置精确定位

我们尝试证 `<₁-dec : a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b`, 用 **Maybe-wrap** 标注撞墙 case (返回 `nothing`).

```agda
<₁-dec? : a <₁ c → b <₁ c → Maybe (a <₁ b ⊎ b <₁ a ⊎ a ≡ b)
<₁-dec? zero zero       = just (injᶜ refl)
<₁-dec? zero (suc q)    = just (injᵇ q)
<₁-dec? (suc p) zero    = just (injᵃ p)
<₁-dec? (suc p) (suc q) = <₁-dec? p q
<₁-dec? (lim₀ {mono₀} n p) (lim₀ k q) with <ᴺ-dec n k
... | injᵃ n<k  = <₁-dec? (<₁-trans p (mono₀ n<k)) q
... | injᵇ k<n  = <₁-dec? p (<₁-trans q (mono₀ k<n))
... | injᶜ refl = <₁-dec? p q
<₁-dec? (lim₁ x p) (lim₁ y q) = nothing
  -- 撞墙 case: 见下方分析
```

**实测撞墙诊断** — 这就是历史预期的死墙位置:

- `p : a' <₁ f x` (其中 a' 是 lhs 隐式参数), `q : b' <₁ f y`
- 想推 `a' <₁ b' ⊎ b' <₁ a' ⊎ a' ≡ b'`
- 沿 BTBO 模式应有: 决定 `x, y : Ord₀` 的关系, 用 mono₁ 把 a', b' 拉到同一 f-像
- 但 **Ord₀ 上无 unconditional trichotomy 也无 BoundedTrich**:
  - Ord-Basic 的 `lim : (ℕ → Ord₀) → Ord₀` 接受任意 ℕ-索引函数, 不强制单调
  - 所以 `<₀` 上没有形如 `<-dec : x <₀ ? → y <₀ ? → ...` 的决策器
  - 即使尝试 `<-dec? x y → x <₀ y ⊎ y <₀ x ⊎ x ≡ y` 也不可决策

**结论**: A₁ 撞墙位置 = `<₁-dec? (lim₁ x p) (lim₁ y q)`. 卡点本质是 Ord-Basic 的 `lim` 不带 mono 字段, Ord₀ 自身就不可决策.

## 5. 与 Mahlo Phase 2 撞墙的对比

[Mahlo Phase 2](../PastBTBO/Mahlo/Phase2.lagda.md#L115) 的撞墙是 `Sub α` 上无序: 跨 `mahlo-a` 与 `mahlo-b s'` 两个家族比较时, Sub α 索引域**没有任何序关系**.

A₁ 撞墙是 **Ord₀ 上的 < 存在但不可决策**. 这是更弱形式的撞墙 — 序存在, 只是不可计算决策.

**区分意义**: Mahlo 的撞墙是结构性的 (索引域无序), A₁ 的撞墙是"决策性"的 (索引域有序但不可决策). 这对修复方向有指导:
- Mahlo: 没法在结构上修, 必须换框架 (sized types, postulate, 或 Setzer Mahlo)
- A₁: 升级索引域为可决策的 (Ordᴰ + bounded), 这是 A₃ γ-bounded 的方向

## 6. 形式化结论

```agda
-- 验证 A₁ 撞墙 case 确实返回 nothing:
A₁-Wall-Demo : (f : Ord₀ → Ord₁ᴰ) (m : monotonic₁ f) (x y : Ord₀)
             → (p : zero <₁ f x) (q : zero <₁ f y)
             → Maybe (zero <₁ zero ⊎ zero <₁ zero ⊎ zero ≡ zero)
A₁-Wall-Demo f m x y p q = <₁-dec? (lim₁ {mono₁ = m} x p) (lim₁ y q)
-- 这个表达式实际等于 nothing — 因为 <₁-dec? 在 (lim₁, lim₁) case 卡死
```

**Spike A₁ 结论**: 历史判断**重新验证成立** — Ord₀ 的不可决策性确实把 BoundedTrich 在 (lim₁, lim₁) case 卡死. 但区别于 Mahlo Phase 2 的"索引无序"墙, A₁ 是"索引有序但不可决策"墙, 修复方向应是 A₃ (索引升级为 Ordᴰ + γ-bound).

下一步 → 见 [SpikeA2](SpikeA2.lagda.md) (mono on Ordᴰ 但无 γ-bound, 看是否真"与 Mahlo Phase 2 同构").
