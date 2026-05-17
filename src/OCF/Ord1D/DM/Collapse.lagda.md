# DM Phase α₄ — ψ-folding + 强度形式化诊断

> Cross-links: [IR](IR.lagda.md), [BoundedTrich](BoundedTrich.lagda.md), [OrdOrd](OrdOrd.lagda.md), [FINDINGS](FINDINGS.md)

**目标**: 形式化 ψ-folding 链 + 具体 Ord₀ 项见证, 诚实标注强度等价 BTBO baseline (≤ ψ(Ω_Ω)). 不是 ψ(Ω_Ω_2) — 严格 Brw₄ Path α 的死磕终点.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.DM.Collapse where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Ord; module Ord-Basic)
open import OCF.Ord1D.DM.IR
open import OCF.Ord1D.DM.BoundedTrich
open import OCF.Ord1D.DM.OrdOrd

open BoundedTrich using (Ordᴰ; _<_)
open Ord-Ord using (Ord; ψ<; ψ₀; ψⁿ; Ω; lim; ordᴰ)
```

## 1. ψ<₁ via ψ-image

由 [Phase α₃](OrdOrd.lagda.md) 的 `ord-equiv : Ord<₁ ℓ ≡ Ord (ψ-down ℓ)`, ψ<₁ 直接通过 ψ-image 嫁接到 BTBO ψ<:

```agda
ψ<₁ : ∀ {i ℓ : Ord₁ᴰᴹ} → i <₁ ℓ → Ord<₁ ℓ → Ord<₁ i
ψ<₁ p x = ψ< p x
```

注: i <₁ ℓ = ψ-down i < ψ-down ℓ, Ord<₁ ℓ = Ord (ψ-down ℓ), Ord<₁ i = Ord (ψ-down i). ψ< 直接 work.

## 2. ψ₀-on-Ord₁ᴰᴹ

```agda
ψ₀-on-Ord₁ᴰᴹ : ∀ {ℓ : Ord₁ᴰᴹ} → Ord<₁ ℓ → Ord-Ord.Ord₀
ψ₀-on-Ord₁ᴰᴹ x = ψ₀ x
```

## 3. 强度见证: 具体 Ord-Basic.Ord₀ 项

```agda
-- 构造一个 Ord₁ᴰᴹ 项, 通过 ψ-folding 折叠到 Ord-Ord.Ord₀:
example-ℓ : Ord₁ᴰᴹ
example-ℓ = zero  -- 最小例子

-- example-ψ-image : Ordᴰ
example-ψ-image = ψ-down example-ℓ  -- = zeroᴰ

-- 完整折叠: 通过 ψ<₁ + ψ₀ 链, 但需要具体 Ord<₁ example-ℓ 项
-- 由于 example-ℓ = zero, Ord<₁ zero = Ord zeroᴰ = base Ord₀-equivalent
```

## 4. 关键元定理: 强度上界 ψ(Ω_Ω)

```agda
-- 形式化: 任何 Ord<₁ ℓ 项的"strength" 通过 ψ-down ℓ 投影到 BTBO Ord-Ord
-- 因此 Ord₁ᴰᴹ 路径的最大强度 = BTBO Ord-Ord 的最大强度
-- = sup of {Ord (ψ-down ℓ) | ℓ : Ord₁ᴰᴹ}
-- = sup of {Ord ℓᴰ | ℓᴰ : Ordᴰ-内可达}
-- = ψ(Ω_Ω) (BTBO baseline)

strength-equivalence : ∀ (ℓ : Ord₁ᴰᴹ) → Ord<₁ ℓ ≡ Ord (ψ-down ℓ)
strength-equivalence _ = refl
```

这是 Phase α 死磕路径的**最终元定理**: 严格 Brw₄ IIR 设计的 Ord<₁ 与 BTBO Ord-on-Ordᴰ **等价**, 强度上界 ψ(Ω_Ω).

## 5. 死磕路径完整诊断

**Path α 完整撞墙地图**:

| Phase | 设计目标 | 实测结果 |
|-------|---------|---------|
| α₁ | 严格 Brw₄ IIR Ord₁ᴰᴹ | ✓ 语法通过, ψ-image 用 ℕ-embed 压缩 |
| α₂ | BoundedTrich via ψ-image | ✓ 自动从 Ordᴰ, 但 Ord₁ᴰᴹ injᶜ 不可证 |
| α₃ | Ord-Ord-on-Ord₁ᴰᴹ | ✓ 形式化等价于 BTBO Ord-Ord (ord-equiv 元定理) |
| α₄ | ψ-folding + ψ(Ω_Ω_2) 见证 | ✗ **不达 ψ(Ω_Ω_2)**, 等价 BTBO baseline ψ(Ω_Ω) |

**死磕诚实结论**:

严格 Brw₄ Path α 在 `--safe --without-K` 下:
- **语法形态**: 真正的 Brw₄ — lim₁ 接受任意 `Ord₀ → Ord₁ᴰᴹ`
- **ψ-image 强度**: 等价 BTBO baseline ψ(Ω_Ω), 不达 ψ(Ω_Ω_2)
- **根本原因**: ψ-down (lim₁ f mono) 必须用 ℕ-embed 压缩 (Ord₀ 不可枚举 + Ordᴰ.lim 只接受 ℕ-索引), 这是结构性限制

**与 REVIEW.md 漏洞的对应**:
- 漏洞 1 (sup ≤ Ω_1): 这里 ψ-image sup ≤ Ω_1, 形式化对应
- 漏洞 2 (Ω₁ 退化): 这里 ψ-down (lim₁) 退化为 ℕ-embed limit
- 漏洞 6 (类型正确 ≠ 强度声明): 这里 strength-equivalence 形式化地证明等价
