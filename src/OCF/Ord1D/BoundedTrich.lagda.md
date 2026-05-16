# Ord₁ᴰ — Phase B: 完整 BoundedTrich + 辅助引理

> Cross-links: [Phase A FINDINGS](FINDINGS.md), [Phase C OrdOrd](OrdOrd.lagda.md)

基于 [Phase A SpikeA3](SpikeA3.lagda.md) 的 γ-bounded + mono + PI 设计, 完整化 Ord₁ᴰ 模块, 准备 Phase C 在其上重做 Ord-Ord (强度突破 ψ(Ω_Ω_2)).

包含:
- 与 SpikeA3 一致的 Ord₁ᴰ + _<₁_ + monotonic₀ + Mono₁ᵧ + PIᵧ
- `<₁-trans` (传递性)
- `<₁-dec` (BoundedTrich, 全函数)
- `f<l₀` (lim₀ 子项 < lim₀)
- 嵌入 `embedᴰ : Ordᴰ → Ord₁ᴰ` (把 Ordᴰ 项映入 Ord₁ᴰ, 给 Phase C 提供 ψ₁ 折叠的基础)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.BoundedTrich where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.BTBO using (module Trich; module BoundedTrich; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; _<_; <-dec; <-trans)
  renaming (zero to zeroᴰ; suc to sucᴰ; lim to limᴰ; monotonic to monotonicᴰ)
```

## 1. Ord₁ᴰ 数据类型

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

## 2. 传递性 `<₁-trans`

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero          = suc p
<₁-trans p (suc q)       = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)    = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ α pα q) = lim₁ α pα (<₁-trans p q)
```

## 3. BoundedTrich `<₁-dec` (全函数)

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

完整 BoundedTrich 通过. (lim₁, lim₁) case 用 γ 上界 + mono₁ + pi₁ 完整决策.

## 4. 辅助引理 `f<l₀`

类比 [BTBO `f<l`](../BTBO.lagda.md#L669):

```agda
f<l₀ : ∀ k → f₀ k <₁ lim₀ f₀ mono₀
f<l₀ {mono₀ = m₀} k = lim₀ (suc k) (m₀ zero')
  where open Trich renaming (zero to zero')
```

注: `lim₁` 的 f<l₁ 引理在 γ 是 lim 时可证, γ 是 suc 时也可证, 但在 γ = zero 时 lim₁ 节点本身退化 (没有 α < zero), 引理空成立. 不写显式 `f<l₁`, 直接在使用时按需构造.

## 5. 嵌入 `embedᴰ : Ordᴰ → Ord₁ᴰ`

把 Ordᴰ 项嵌入 Ord₁ᴰ. 这是 Phase C 给 ψ₁ 折叠提供素材的关键 — Ord₁ᴰ 必须能"装下"任何 Ordᴰ 项 (因为 sup(Ord₁ᴰ) ≥ sup(Ordᴰ) = Ω).

```agda
embedᴰ : Ordᴰ → Ord₁ᴰ
embedᴰ-mono : ∀ {α β} → α < β → embedᴰ α <₁ embedᴰ β

embedᴰ zeroᴰ        = zero
embedᴰ (sucᴰ α)     = suc (embedᴰ α)
embedᴰ (limᴰ f m)   = lim₀ (embedᴰ ∘ f) (λ p → embedᴰ-mono (m p))

embedᴰ-mono BoundedTrich.zero      = zero
embedᴰ-mono (BoundedTrich.suc p)   = suc (embedᴰ-mono p)
embedᴰ-mono (BoundedTrich.lim k p) = lim₀ k (embedᴰ-mono p)
```

**实测**: induction-recursion (embedᴰ + embedᴰ-mono) 同时定义, Agda 接受. embedᴰ 是 Ordᴰ → Ord₁ᴰ 的严格保序嵌入.

## 6. 一个具体的"高强度" Ord₁ᴰ 项

构造一个 Ord₁ᴰ 项, 它的 sup 估算应该达到 Ω_2 — 用 lim₁ 节点把整个 Ordᴰ 索引"展开":

```agda
-- ω₁: Ordᴰ 中嵌入的 ω (单层 ℕ-索引)
ω : Ord₁ᴰ
ω = lim₀ embed-suc embed-suc-mono
  where
    embed-suc : ℕ → Ord₁ᴰ
    embed-suc zero    = zero
    embed-suc (suc n) = suc (embed-suc n)
    embed-suc-mono : monotonic₀ embed-suc
    embed-suc-mono Trich.zero    = zero
    embed-suc-mono (Trich.suc p) = suc (embed-suc-mono p)

-- Ω₁ᴰ: 用 lim₁ γ 把 Ordᴰ 整个 γ-切片嵌入. 取 γ 为 BoundedTrich 中具体的 sucᴰ zeroᴰ (= 1):
-- 不够; 取大 γ 需 Ordᴰ 上有大项. 这里给出一个示例 — 取 γ = sucᴰ zeroᴰ 时:
Ω₁ᴰ-tiny : Ord₁ᴰ
Ω₁ᴰ-tiny = lim₁ (sucᴰ zeroᴰ) (λ α pα → embedᴰ α)
              (λ pα pβ α<β → embedᴰ-mono α<β)
              (λ {α} pα pα' → refl-irrelevance pα pα')
  where
    refl-irrelevance : ∀ {α} (pα pα' : α < sucᴰ zeroᴰ) → embedᴰ α ≡ embedᴰ α
    refl-irrelevance pα pα' = refl
```

**意义**: Ω₁ᴰ-tiny 用 lim₁ 把 Ordᴰ 在 γ = 1 之下的切片 (即 {zeroᴰ}) 嵌入 Ord₁ᴰ. 这是最小的 lim₁ 节点示例. **真正的 Ω₂-级表达力**需要 γ 取更大 (γ = ψᴰ n 等 Higher.agda 风格), 在 [Phase C](OrdOrd.lagda.md) 中通过 Ord-Ord-on-Ord₁ᴰ 实现.

## 7. Phase B 结论

A₃ 设计在 Phase B 中**完整化**:
- BoundedTrich 全函数 ✓
- `<₁-trans` 完整 ✓
- `f<l₀` 引理 ✓
- `embedᴰ` 嵌入 + 保序 ✓
- 一个具体 Ord₁ᴰ 项 (Ω₁ᴰ-tiny) 示例 ✓

下一步 [Phase C](OrdOrd.lagda.md): 在 Ord₁ᴰ 上重做 BTBO Ord-Ord 模块, 用 ℓ : Ord₁ᴰ 参数化 `Ord<₁ : (i : Ord₁ᴰ) (p : i <₁ ℓ) → Set`, 构造 ψ₁ 折叠链, 估算强度 ψ(Ω_Ω_2).
