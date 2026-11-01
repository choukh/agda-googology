# DM Phase α₂ — BoundedTrich via ψ-image

> Cross-links: [IR](IR.lagda.md), [OrdOrd](OrdOrd.lagda.md), [FINDINGS](FINDINGS.md)

**目标**: 在 Phase α₁ 建立的 IR Ord₁ᴰᴹ 上证 BoundedTrich, 通过 ψ-image (Ordᴰ-level) 派发. 关键测试: (lim₁, lim₁) case 能否走通?

**死磕焦点**: ψ-image 上的 BoundedTrich 自动从 Ordᴰ 的 `<-dec` 获得. 但要从 ψ-image trichotomy 推 Ord₁ᴰᴹ 上 trichotomy, 需要 ψ-down 是单射 — 它不是 (lim₁ case 用 ℕ-embed 压缩).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.DM.BoundedTrich where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Basic; injᵃ; injᵇ; injᶜ)
open import OCF.Ord1D.DM.IR

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; <-dec; <-trans)
  renaming (zero to zeroᴰ; suc to sucᴰ; lim to limᴰ; _<_ to _<ᴰ_)
```

## 1. ψ-image 诱导的 _<₁_ 关系

由于 ψ-down : Ord₁ᴰᴹ → Ordᴰ 是 IR-recursion 的输出, 我们可以定义 _<₁_ 为 ψ-image 上的 < 关系:

```agda
infix 10 _<₁_
_<₁_ : Ord₁ᴰᴹ → Ord₁ᴰᴹ → Set
a <₁ b = ψ-down a <ᴰ ψ-down b
```

**注**: 这与 Phase A-D 的 data type _<₁_ 不同 — Phase D 上 _<₁_ 是 inductive data, 而这里是函数定义 (从 ψ-image 诱导).

## 2. <₁-trans (传递性)

直接由 Ordᴰ 上的 `<-trans` 给出:

```agda
<₁-trans : ∀ {a b c} → a <₁ b → b <₁ c → a <₁ c
<₁-trans = <-trans
```

## 3. BoundedTrich via ψ-image

关键: BoundedTrich on Ord₁ᴰᴹ 通过 BoundedTrich on Ordᴰ (BTBO 已证) 直接获得:

```agda
<₁-dec-ψ : ∀ {a b c} → a <₁ c → b <₁ c
         → a <₁ b ⊎ b <₁ a ⊎ ψ-down a ≡ ψ-down b
<₁-dec-ψ p q = <-dec p q
```

**关键差异**: 第三个分支是 `ψ-down a ≡ ψ-down b` (ψ-image 相等), 不是 `a ≡ b` (Ord₁ᴰᴹ 相等).

**ψ-down 非单射的后果**:

由于 ψ-down (lim₁ f mono) 通过 ℕ-embed 压缩 (Phase α₁ 撞墙), 多个 distinct Ord₁ᴰᴹ 项可以有相同 ψ-image. 例如:

```agda
-- 任意两个 Ord₀-索引 lim₁ f, lim₁ f' 若 ψ-image (f ∘ ℕ-embed) ≡ ψ-image (f' ∘ ℕ-embed), 则 ψ-down 同
-- 即 f, f' 在 ℕ-embed image 上行为相同 → ψ-down 同
```

这意味着 `<₁-dec-ψ` 的 injᶜ 分支**不能** transfer 到 Ord₁ᴰᴹ 上的 ≡. 真正的 BoundedTrich (含 `a ≡ b`) 在 Ord₁ᴰᴹ 上**不可证**.

## 4. 死磕诊断: ψ-image trichotomy 的局限

```agda
-- 我们尝试: 假设 ψ-image 上 trichotomy 能 transfer 到 Ord₁ᴰᴹ 上
-- <₁-dec-true : ∀ {a b c} → a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b
-- 这个签名在 ψ-image 不单射时不可证

-- 我们能做的是弱化版:
<₁-dec-weak : ∀ {a b c} → a <₁ c → b <₁ c
            → a <₁ b ⊎ b <₁ a ⊎ ψ-down a ≡ ψ-down b
<₁-dec-weak = <₁-dec-ψ
```

**Phase α₂ 死磕诊断**:

- ψ-image 上 BoundedTrich ✓ (从 Ordᴰ 自动)
- Ord₁ᴰᴹ 上 BoundedTrich ✗ — injᶜ 分支退化为 ψ-image ≡, 不是 syntactic ≡

**与 [REVIEW.md 漏洞 6](../REVIEW.md) 同型**: 形式化的 trichotomy 退化为 ψ-image 上的, 与 "Agda 类型正确不等于元数学声明成立" 一致.

## 5. 是否能用弱化 BoundedTrich 走通 Ord-Ord-on-Ord₁ᴰᴹ?

[BTBO ψ<](../../../../src/OCF/BTBO.lagda.md#L1009) 在 limᵢ case 用 `<-dec q p` 派发, 三歧给三种 ψ 输出 (limᵢ / lfp / lfp). injᶜ refl 分支用 `refl : i ≡ j` 推 `Ord< i p = Ord< j p` (类型相等).

如果用 ψ-image trichotomy, injᶜ 分支只得 `ψ-down i ≡ ψ-down j`, 不是 `i ≡ j`. 推不出 `Ord< i = Ord< j` (因为 Ord< 依赖 i 而非 ψ-down i).

**但**: 如果 Ord-Ord-on-Ord₁ᴰᴹ 的 `Ord<₁` 参数化用 ψ-image (而非 Ord₁ᴰᴹ 本身), 即 `Ord<₁-via-ψ : (i : Ordᴰ) (p : i <ᴰ ℓᴰ) → Set`, 那 ψ-image trichotomy 可用. 这退回到 BTBO Ord-Ord 在 Ordᴰ-参数化 — 与 BTBO baseline 同, 无强度增益.

## 6. Phase α₂ 结论

**Phase α₂ 实测**:
- ψ-image 上的 BoundedTrich ✓ (自动从 Ordᴰ)
- Ord₁ᴰᴹ 上的真 BoundedTrich ✗ — ψ-down 非单射, injᶜ 分支不能 transfer
- 用 ψ-image BoundedTrich 派发 ψ-folding → 强度等价 BTBO Ord-Ord (在 Ordᴰ 上)

**死磕路径核心问题**: 严格 Brw₄ + IIR ψ-down 设计**形式化达成 Brw₄ 阶语法**, 但 ψ-image 上**等价 BTBO baseline 强度**.

**Phase α₃ 选项**:
- A. 接受弱化 BoundedTrich, 尝试 Ord-Ord-on-Ord₁ᴰᴹ via ψ-image (强度 ≤ ψ(Ω_Ω))
- B. 撞墙诊断, 转 Path β (universe polymorphism)
- C. 形式化"ψ-image BoundedTrich → ψ(Ω_Ω) 等价" 的元定理

由于死磕目标是 ψ(Ω_Ω_2), 选项 A 不达成. 选项 B 几乎肯定也撞墙 (universe 不增强度). 选项 C 是诚实的形式化结论.

**推荐**: 进入 Phase α₃ 尝试选项 A (Ord-Ord via ψ-image), 形式化"语法 Brw₄ + ψ-image BTBO 等价" 的具体见证. 这是死磕路径的最终诚实交付.
