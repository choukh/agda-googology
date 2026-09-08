# Spike A₃ — γ-bounded + mono (借鉴 BTBO Ord-Ord, 注入上界修复 A₂)

> Cross-links: [SpikeA1](SpikeA1.lagda.md), [SpikeA2](SpikeA2.lagda.md), [Spikebeta](Spikebeta.lagda.md), [Spikeepsilon](Spikeepsilon.lagda.md), [FINDINGS umbrella](FINDINGS.md)

修复 [A₂](SpikeA2.lagda.md) 的"无上界"撞墙: 给 lim₁ 节点显式注入一个 Ordᴰ-上界 γ, 索引域是 `α : Ordᴰ` + `α < γ` 的证明对. mono 表达"索引内 < 推 image 内 <₁". 此外引入 PI (proof-irrelevance) 字段, 处理 `injᶜ α≡β` case.

借鉴 [BTBO Ord-Ord](../../../src/OCF/BTBO.lagda.md#L836-L944) 的 limᵢ 模式, 但加 mono + PI + 显式 _<₁_. **这不是 Ord-Ord 的复刻** — Ord-Ord 没有 < 关系也无 mono, Ord₁ᴰ-A₃ 是 Ord-Ord + 完整有界三歧性的版本.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.SpikeA3 where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.BTBO using (module Trich; module BoundedTrich; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; _<_; <-dec; <-trans)
```

## 1. Ord₁ᴰ (A₃ 版): γ-bounded lim₁

```agda
data Ord₁ᴰ : Set
data _<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set

monotonic₀ : (ℕ → Ord₁ᴰ) → Set
monotonic₀ f = ∀ {n m} → n <ᴺ m → f n <₁ f m

Mono₁ᵧ : (γ : Ordᴰ) → ((α : Ordᴰ) → α < γ → Ord₁ᴰ) → Set
Mono₁ᵧ γ f = ∀ {α β} (pα : α < γ) (pβ : β < γ) → α < β → f α pα <₁ f β pβ

PIᵧ : (γ : Ordᴰ) → ((α : Ordᴰ) → α < γ → Ord₁ᴰ) → Set
PIᵧ γ f = ∀ {α} (pα pα' : α < γ) → f α pα ≡ f α pα'

private variable
  a b c : Ord₁ᴰ
  γ : Ordᴰ
  f₀ : ℕ → Ord₁ᴰ
  f₁ : (α : Ordᴰ) → α < γ → Ord₁ᴰ
  mono₀ : monotonic₀ f₀
  mono₁ : Mono₁ᵧ γ f₁
  pi₁ : PIᵧ γ f₁

data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ) (mono₀ : monotonic₀ f) → Ord₁ᴰ
  lim₁ : (γ : Ordᴰ) (f : (α : Ordᴰ) → α < γ → Ord₁ᴰ)
         (mono₁ : Mono₁ᵧ γ f) (pi₁ : PIᵧ γ f) → Ord₁ᴰ

infix 10 _<₁_
data _<₁_ where
  zero :          a <₁ suc a
  suc  : a <₁ b → a <₁ suc b
  lim₀ : ∀ n   → a <₁ f₀ n → a <₁ lim₀ f₀ mono₀
  lim₁ : ∀ α (pα : α < γ) → a <₁ f₁ α pα → a <₁ lim₁ γ f₁ mono₁ pi₁
```

**实测**: induction-induction 通过. 与 A₁/A₂ 的差异: lim₁ 字段多 γ (上界) + pi₁ (PI). _<₁_ 的 lim₁ case 多 `pα : α < γ` 参数 — 这就是从 lim₁ 节点局部"提取"上界证据的关键.

## 2. `<₁-trans` 传递性

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero          = suc p
<₁-trans p (suc q)       = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)    = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ α pα q) = lim₁ α pα (<₁-trans p q)
```

**实测**: 通过. 与 A₁/A₂ 模式相同, 增加的 pα 字段透传.

## 3. BoundedTrich `<₁-dec` — 核心 (lim₁, lim₁) case 关键测试

```agda
<₁-dec : a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b
<₁-dec zero zero       = injᶜ refl
<₁-dec zero (suc q)    = injᵇ q
<₁-dec (suc p) zero    = injᵃ p
<₁-dec (suc p) (suc q) = <₁-dec p q
<₁-dec (lim₀ {mono₀} n p) (lim₀ k q) with <ᴺ-dec n k
... | injᵃ n<k  = <₁-dec (<₁-trans p (mono₀ n<k)) q
... | injᵇ k<n  = <₁-dec p (<₁-trans q (mono₀ k<n))
... | injᶜ refl = <₁-dec p q
<₁-dec (lim₁ {mono₁ = m₁} {pi₁ = π₁} α pα p) (lim₁ β pβ q) with <-dec pα pβ
... | injᵃ α<β  = <₁-dec (<₁-trans p (m₁ pα pβ α<β)) q
... | injᵇ β<α  = <₁-dec p (<₁-trans q (m₁ pβ pα β<α))
... | injᶜ refl = <₁-dec p (subst (_ <₁_) (π₁ pβ pα) q)
```

**关键 case 分析**:

`(lim₁ α pα p) (lim₁ β pβ q)` — α, β : Ordᴰ, pα : α < γ, pβ : β < γ. 共同上界 γ 由 lim₁ 节点提供 (这是 A₃ vs A₂ 的关键差异).

- 调用 BTBO `<-dec pα pβ` (BoundedTrich on Ordᴰ): 给出 α <ᴰ β / β <ᴰ α / α ≡ β 三歧.
- `injᵃ α<β`: 用 mono₁ (= m₁) 把 p : a <₁ f α pα 提升到 f β pβ — `m₁ pα pβ α<β : f α pα <₁ f β pβ`. 然后 trans p 得到 a <₁ f β pβ, 递归 <₁-dec 与 q.
- `injᵇ β<α`: 对称.
- `injᶜ refl`: α ≡ β. 此时 f α pα 和 f β pβ 是 f 在 α 上的两个 image (pα ≠ pβ 但 α=β). 用 PI 字段 π₁ : `f β pβ ≡ f β pα` (β=α, pα/pβ 互换), 然后 subst q 把 b <₁ f β pβ 改为 b <₁ f α pα = b <₁ f β pα. 递归 <₁-dec p (transported q).

**潜在风险**:
- R1 PI 字段必要性: 如果 Agda 自动判 (subst 路径), 也许 PI 字段可省? 实测看.
- R2 termination: 递归调用 `<₁-dec (<₁-trans p (...)) q` 论元 q 严格减小. 应通过.

让我编译验证.

## 4. 撞墙 / 通过判定

```agda
-- 类型签名验证 <₁-dec 全函数性: 没有 Maybe, 没有 hole, 编译通过 ⇒ A₃ 走通
_ : a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b
_ = <₁-dec
```

**Spike A₃ 结论 (待编译验证)**:

预期: 走通. (lim₁, lim₁) case 通过 γ 上界 + mono₁ + PI 完整决策. 这是 A₂ "无上界" 撞墙的修复, 也是 Ord₁ 加 BoundedTrich 的工程可行方案.

**与 Ord-Ord 的对比**: BTBO Ord-Ord 的 limᵢ 节点也带 γ-bound, 但 Ord-Ord 没在 Ord 上定义 < 关系也无 mono. Ord₁ᴰ-A₃ 是 Ord-Ord + 完整有界三歧性. 在 [Phase C](OrdOrd.lagda.md) 中, 我们会把 Ord-Ord 模块在 Ord₁ᴰ-A₃ 上重做, 强度突破至 ψ(Ω_Ω_2).

下一步 → 见 [Spikebeta](Spikebeta.lagda.md) (Inductive-Recursive 全新方向).
