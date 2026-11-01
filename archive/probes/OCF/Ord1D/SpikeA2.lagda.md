# Spike A₂ — mono on Ordᴰ, 无 γ-bound (历史推断撞墙, 重新验证)

> Cross-links: [SpikeA1](SpikeA1.lagda.md), [SpikeA3](SpikeA3.lagda.md), [Spikebeta](Spikebeta.lagda.md), [Spikeepsilon](Spikeepsilon.lagda.md), [FINDINGS umbrella](FINDINGS.md)

把 lim₁ 索引域升级为 Ordᴰ (已有 BoundedTrich 的"驯化"序数), 加 mono on Ordᴰ. 不带局部 γ-bound.

历史判断: (lim₁, lim₁) case 中要决定 α, β : Ordᴰ 的关系, 但 Ordᴰ 上的 `<-dec` 是 BoundedTrich (需共同上界 γ), lim₁ 节点不提供 γ — 撞墙. **该撞墙曾被推断为"与 Mahlo Phase 2 同构"**.

**本 spike 的目的**: 形式化实测撞墙位置, 验证或推翻"与 Mahlo Phase 2 同构"这个 framing.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.SpikeA2 where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.BTBO using (module Trich; module BoundedTrich; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; _<_; <-dec; <-trans)
```

## 1. Ord₁ᴰ (A₂ 版): mono on Ordᴰ, 无 γ-bound

```agda
data Ord₁ᴰ : Set
data _<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set

monotonic₀ : (ℕ → Ord₁ᴰ) → Set
monotonic₀ f = ∀ {n m} → n <ᴺ m → f n <₁ f m

monotonic₁ : (Ordᴰ → Ord₁ᴰ) → Set
monotonic₁ f = ∀ {α β : Ordᴰ} → α < β → f α <₁ f β

private variable
  a b c : Ord₁ᴰ
  f₀ : ℕ → Ord₁ᴰ
  f₁ : Ordᴰ → Ord₁ᴰ
  mono₀ : monotonic₀ f₀
  mono₁ : monotonic₁ f₁

data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ)   (mono₀ : monotonic₀ f) → Ord₁ᴰ
  lim₁ : (f : Ordᴰ → Ord₁ᴰ) (mono₁ : monotonic₁ f) → Ord₁ᴰ

infix 10 _<₁_
data _<₁_ where
  zero :          a <₁ suc a
  suc  : a <₁ b → a <₁ suc b
  lim₀ : ∀ n   → a <₁ f₀ n → a <₁ lim₀ f₀ mono₀
  lim₁ : ∀ α   → a <₁ f₁ α → a <₁ lim₁ f₁ mono₁
```

**实测**: Agda 接受这个定义, 与 A₁ 形态相同, 只是 lim₁ 索引域改为 Ordᴰ.

## 2. `<₁-trans` 传递性

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero        = suc p
<₁-trans p (suc q)     = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)  = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ α q)  = lim₁ α (<₁-trans p q)
```

**实测**: 通过, 同 A₁.

## 3. BoundedTrich 尝试: (lim₁, lim₁) 撞墙位置

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
<₁-dec? (lim₁ {mono₁} α p) (lim₁ β q) = nothing
  -- 撞墙: 见下方
```

**实测撞墙诊断**:

我们想在 (lim₁, lim₁) case 模仿 (lim₀, lim₀) 的处理:

`<-dec α β` 要求 α 和 β 有共同上界 γ : Ordᴰ. 但 `lim₁ f₁ mono₁` 节点**不提供这样的 γ**. f₁ 接受任意 Ordᴰ → Ord₁ᴰ, 没有"f₁ 只在某个 γ 之下取值"的限制.

**关键观察**: 虽然 Ordᴰ 上的 BoundedTrich 存在, 但**它是 conditional 的**(需上界), 不是 unconditional. 在 lim₁ 节点局部, 我们没有自然的上界提供.

**与 A₁ 的差异**: A₁ 撞墙因为 Ord₀ 上**根本没有决策器**. A₂ 撞墙因为 Ordᴰ 上有**有条件决策器**但**无法提供条件**. 这是不同的"撞墙类型".

## 4. 与 Mahlo Phase 2 撞墙的对比 (区分 framing)

[Mahlo Phase 2](../PastBTBO/Mahlo/Phase2.lagda.md#L115) 的 `b : Sub α → Ordᴹ` 撞墙: Sub α 是**无序的索引空间**, 跨 mahlo 子家族 (`mahlo-a` vs `mahlo-b s'`) 比较时, Sub α 内部没有任何关系可用.

A₂ 撞墙: Ordᴰ 上**有完整的 BoundedTrich**, 但在 lim₁ 节点局部**缺少共同上界 γ**.

**这两者是不同的失败类型**:

- Mahlo: 决策器**不存在**于索引空间内
- A₂: 决策器**存在但条件不满足** (无上界证据)

**修复方向也不同**:

- Mahlo: 必须改 Sub 的结构 (但已多次尝试撞墙)
- A₂: 给 lim₁ 节点显式注入 γ 上界 → 这就是 A₃ γ-bounded 方向

**结论**: 历史 framing "A₂ 与 Mahlo Phase 2 同构" **过度类比**. A₂ 实际是"决策性 + 缺上界证据" 的撞墙, 而 Mahlo 是"决策性根本不存在". 区分这两者后, A₃ γ-bounded 设计是 A₂ 撞墙的**自然修复**(注入上界), 而非"同构于已失败的 Mahlo 路径".

## 5. 形式化撞墙证据

```agda
A₂-Wall-Demo : (f : Ordᴰ → Ord₁ᴰ) (m : monotonic₁ f) (α β : Ordᴰ)
             → (p : zero <₁ f α) (q : zero <₁ f β)
             → Maybe (zero <₁ zero ⊎ zero <₁ zero ⊎ zero ≡ zero)
A₂-Wall-Demo f m α β p q = <₁-dec? (lim₁ {mono₁ = m} α p) (lim₁ β q)
-- 该表达式 = nothing — <₁-dec? 在 (lim₁, lim₁) case 卡死
-- 原因: 无 γ 上界, <-dec α β 无法调用
```

**Spike A₂ 结论**: 撞墙位置与 A₁ 形似 (都在 lim₁ × lim₁), 但卡点本质不同 (A₁ 无决策器, A₂ 无上界证据). 这清晰了 A₃ γ-bounded 是直接对 A₂ 的修复 (注入 γ), 而非"借鉴 BTBO Ord-Ord 的复刻".

下一步 → 见 [SpikeA3](SpikeA3.lagda.md) (γ-bounded + mono, 注入上界, 看 (lim₁, lim₁) BoundedTrich 是否真的走通).
