# DM Phase α₃ — Ord-Ord via ψ-image (形式化等价于 BTBO Ord-Ord)

> Cross-links: [IR](IR.lagda.md), [BoundedTrich](BoundedTrich.lagda.md), [Collapse](Collapse.lagda.md), [FINDINGS](FINDINGS.md)

**目标**: 形式化"Ord-Ord-on-Ord₁ᴰᴹ via ψ-image"实际等价于"Ord-Ord-on-Ordᴰ via ψ-image" (即 BTBO Ord-Ord). 这是死磕路径的核心诚实交付 — 严格 Brw₄ 设计的语法形态, ψ-image 强度等价 BTBO baseline.

**关键洞察**: 既然 _<₁_ 通过 ψ-down image 定义 (Phase α₂), Ord-Ord-on-Ord₁ᴰᴹ 参数化 ℓ : Ord₁ᴰᴹ **实际等价**于 Ord-Ord-on-Ordᴰ 参数化 ℓᴰ = ψ-down ℓ. 二者通过 ψ-down 同构.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.DM.OrdOrd where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord)
open import OCF.Ord1D.DM.IR
open import OCF.Ord1D.DM.BoundedTrich

open BoundedTrich using (Ordᴰ; _<_)
open Ord-Ord using (Ord; Ord<; Ord<-≡)
```

## 1. Ord-on-Ord₁ᴰᴹ 通过 ψ-image 嫁接

由于 `_<₁_ a b = ψ-down a < ψ-down b` (Phase α₂), Ord-Ord-on-Ord₁ᴰᴹ 自然嫁接到 BTBO Ord-Ord-on-Ordᴰ:

```agda
-- 给定 ℓ : Ord₁ᴰᴹ, "Ord<₁ at ℓ" 通过 ψ-image 上的 Ord< 实现:
Ord<₁ : (ℓ : Ord₁ᴰᴹ) → Set
Ord<₁ ℓ = Ord (ψ-down ℓ)

-- 即 Ord<₁ ℓ = Ord-on-Ordᴰ-at-(ψ-down ℓ)
```

**形式化结果**: Ord-Ord-on-Ord₁ᴰᴹ 通过 ψ-down 等价于 BTBO Ord-Ord-on-Ordᴰ. **没有新结构, 没有新强度**.

## 2. 层级提升 ↑₁ via ψ-down

```agda
-- 给定 p : a <₁ b (即 ψ-down a < ψ-down b), 通过 BTBO ↑ 提升:
↑₁ : ∀ {a b : Ord₁ᴰᴹ} → a <₁ b → Ord<₁ a → Ord<₁ b
↑₁ p x = Ord-Ord.↑ p x
```

## 3. 形式化等价性元定理

```agda
-- 主元定理: Ord<₁ ℓ 与 Ord<-on-Ordᴰ (ψ-down ℓ) 同 type
ord-equiv : ∀ (ℓ : Ord₁ᴰᴹ) → Ord<₁ ℓ ≡ Ord (ψ-down ℓ)
ord-equiv _ = refl
```

**意义**: Phase α 死磕路径的 Ord<₁ 与 BTBO Ord<-on-Ordᴰ 是**完全相同的 type**, 仅 ℓ-参数从 Ord₁ᴰᴹ 通过 ψ-down 投影到 Ordᴰ. 这是诚实的"语法 Brw₄ + ψ-image BTBO 等价" 的形式化.

## 4. Phase α₃ 死磕诊断

**Phase α₃ 实测**:
- ✓ Ord<₁ : Ord₁ᴰᴹ → Set 通过 ψ-down 嫁接到 BTBO Ord-Ord, 编译通过
- ✓ 层级提升 ↑₁ 直接复用 BTBO `↑`, 不需新设计
- ✓ ord-equiv 元定理形式化等价性

**强度结论**: Ord<₁ ℓ 的强度 = Ord (ψ-down ℓ) 的强度 ≤ sup(Ordᴰ) = Ω = Ω_1. **不达 ψ(Ω_Ω_2)**.

**死磕诚实**: 这是 Path α 的真实交付 — 形式化语法 Brw₄ 阶 Ord₁ᴰᴹ 类型, ψ-image 上**等价**于 BTBO baseline. 与 REVIEW.md 漏洞 5 ("sup-by-bound 与 embedᴰ 同 sup 假突破") 在 IR 框架下的等价表述.

## 5. Phase α₄ 准备

由于 Ord<₁ ≡ Ord (ψ-down ℓ), ψ-folding 链 (`ψ<₁ : i <₁ ℓ → Ord<₁ ℓ → Ord<₁ i`) 可直接复用 BTBO `ψ<`. 见 [Collapse.lagda.md](Collapse.lagda.md).
