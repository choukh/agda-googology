# DM Phase α₁ — 严格 Brw₄ IIR Ord₁ᴰᴹ + ψ-down

> Death Match 路线主推 Path α 的核心创新尝试. 严格 `--safe --without-K`, 不接受 postulate / sized types / cubical.

**目标**: 让 lim₁ 真正接受 `Ord₀ → Ord₁ᴰᴹ` 任意函数 (Brw₄ 阶), 通过 IIR mutual `Ord₁ᴰᴹ + ψ-down` 把 mono 表达在 ψ-image (Ordᴰ-level) 上, 绕开 Ord₀ trichotomy 需求.

**死磕焦点**: ψ-down 在 lim₁ case 的可计算性. [Spikebeta](../Spikebeta.lagda.md) 撞强度坍缩. Phase α₁ 形式化此撞墙位置, Phase α₂ 测试 ψ-image BoundedTrich 是否走通.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.DM.IR where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Basic)

open Trich renaming (_<_ to _<ᴺ_)
open BoundedTrich using (Ordᴰ)
  renaming (zero to zeroᴰ; suc to sucᴰ; lim to limᴰ; _<_ to _<ᴰ_; monotonic to monoᴰ)
open Ord-Basic using (Ord₀)
```

## 1. Ord₀ 上的 <₀ (BTBO 没给, 补上)

```agda
infix 10 _<₀_
data _<₀_ : Ord₀ → Ord₀ → Set where
  zero : ∀ {a} → a <₀ Ord-Basic.suc a
  suc  : ∀ {a b} → a <₀ b → a <₀ Ord-Basic.suc b
  lim  : ∀ {a f} (n : ℕ) → a <₀ f n → a <₀ Ord-Basic.lim f
```

## 2. IIR mutual: Ord₁ᴰᴹ + ψ-down

**关键设计**: lim₁ 接受任意 `Ord₀ → Ord₁ᴰᴹ` (严格 Brw₄), mono 通过 ψ-down image 表达 (不要求 Ord₀ trichotomy).

```agda
mutual
  data Ord₁ᴰᴹ : Set
  ψ-down : Ord₁ᴰᴹ → Ordᴰ

  data Ord₁ᴰᴹ where
    zero : Ord₁ᴰᴹ
    suc  : Ord₁ᴰᴹ → Ord₁ᴰᴹ
    lim₀ : (f : ℕ → Ord₁ᴰᴹ)
           (mono : ∀ {n m} → n <ᴺ m → ψ-down (f n) <ᴰ ψ-down (f m))
         → Ord₁ᴰᴹ
    lim₁ : (f : Ord₀ → Ord₁ᴰᴹ)
           (mono : ∀ {x y : Ord₀} → x <₀ y → ψ-down (f x) <ᴰ ψ-down (f y))
         → Ord₁ᴰᴹ

  ψ-down zero          = zeroᴰ
  ψ-down (suc a)       = sucᴰ (ψ-down a)
  ψ-down (lim₀ f mono) = limᴰ (ψ-down ∘ f) mono
  ψ-down (lim₁ f mono) = limᴰ (ψ-down ∘ f ∘ ℕ-embed) ψ-down∘f∘ℕ-embed-mono
    where
      ℕ-embed : ℕ → Ord₀
      ℕ-embed zero    = Ord-Basic.zero
      ℕ-embed (suc n) = Ord-Basic.suc (ℕ-embed n)

      ℕ-embed-mono : ∀ {n m} → n <ᴺ m → ℕ-embed n <₀ ℕ-embed m
      ℕ-embed-mono Trich.zero    = zero
      ℕ-embed-mono (Trich.suc p) = suc (ℕ-embed-mono p)

      ψ-down∘f∘ℕ-embed-mono : ∀ {n m} → n <ᴺ m → ψ-down (f (ℕ-embed n)) <ᴰ ψ-down (f (ℕ-embed m))
      ψ-down∘f∘ℕ-embed-mono p = mono (ℕ-embed-mono p)
```

**实测 — lim₁ case 的死磕成本**:

ψ-down (lim₁ f mono) 通过 **ω-枚举 Ord₀** (`ℕ-embed`) 把任意 Ord₀-索引 lim₁ 压缩到 ℕ-索引 Ordᴰ.lim. 这是**形式化的强度坍缩**:

- `ℕ-embed : ℕ → Ord₀` 只取 Ord₀ 的 ω-级"finite ordinals" (suc^n zero), 完全忽略 Ord₀ 的 ω-级以上结构 (lim 形态等)
- ψ-down (lim₁ f mono) 实际只取 f 在 `{0, 1, 2, ...}` 上的 image 之 limᴰ
- sup of ψ-image ≤ ω-iter sup of f ≤ ω × sup(individual ψ-down (f n)) — 与 ω-索引等价

**强度结论**: 在 ψ-image 上, lim₁ 与 lim₀ **无区别**. Ord₁ᴰᴹ 的 lim₁ 创新构造子被 ψ-down 完全降级.

这是 Spikebeta 撞过的强度坍缩在 IR 框架下的等价形式. 但 Phase α₁ 让 Agda 接受这个设计, 编译通过 — 是死磕路径的第一步.

## 3. 关键里程碑 (Phase α₁ 完成判定)

```agda
-- ✓ IIR mutual block 通过 (Ord₁ᴰᴹ + ψ-down 互递归编译)
_ : Ord₁ᴰᴹ → Ordᴰ
_ = ψ-down

-- ✓ lim₁ 接受任意 Ord₀ → Ord₁ᴰᴹ, 类型签名通过
_ : (f : Ord₀ → Ord₁ᴰᴹ)
    (mono : ∀ {x y : Ord₀} → x <₀ y → ψ-down (f x) <ᴰ ψ-down (f y))
  → Ord₁ᴰᴹ
_ = lim₁
```

**实测**: lim₁ 接受任意 `Ord₀ → Ord₁ᴰᴹ` 函数 + mono 字段, 类型签名编译通过. 这是 Brw₄ 阶语法形态的 Agda 形式化.

注意: 构造 lim₁ 的具体实例需要 f 提供 mono 见证 — 例如 f = const zero 时 mono 要求 `zeroᴰ <ᴰ zeroᴰ` (不真), 所以 const f 不可作 lim₁ 实例. 真正的 lim₁ 实例需要 f 在 ψ-image 上严格单调, 例如:

```agda
-- f x = (depth-encoded form of x in Ord₁ᴰᴹ): 这需要 embedᴰ-style 嵌入, 留 Phase α₂
-- 此处 Phase α₁ 仅形式化类型可表达性
```

## 4. 死磕诊断: ψ-image collapse 实测

ψ-down (lim₁ f mono) 在定义中已显示用 `ℕ-embed` 把 Ord₀ 索引压缩到 ℕ. 这是 ω-枚举式坍缩 — Ord₀ 中所有 lim 形态项都被忽略, 只取 `zero`, `suc zero`, `suc (suc zero)`, ... 的有限链.

形式上: image of `ψ-down ∘ f ∘ ℕ-embed` 在 Ordᴰ 中 sup ≤ ω-iter ≤ Ord₀-finite-segment-sup. 不达 Brw₄ 阶, 也不达 Brw₃ 全集.

这与 [REVIEW.md 漏洞 5 "假突破"](../REVIEW.md) 同结构 — 形式上的 Brw₄ 节点, ψ-image 上的 ω-iter 强度.

## 5. Phase α₁ 结论 + Phase α₂ 准备

**Phase α₁ 达成**:
- ✓ 严格 Brw₄ IIR Ord₁ᴰᴹ + ψ-down 互递归编译通过 (`--safe --without-K`)
- ✓ lim₁ 接受任意 `Ord₀ → Ord₁ᴰᴹ` 函数, 无 γ-bound
- ✓ mono 通过 ψ-image 表达, 不要求 Ord₀ trichotomy

**Phase α₁ 撞墙诊断**:
- **ψ-image 上的强度坍缩** — ψ-down (lim₁ f mono) 通过 ω-枚举 Ord₀ 压缩, 强度等价 ω-iter (≈ lim₀)
- lim₁ 的"Brw₄ 阶" 在语法上保持 (Ord₁ᴰᴹ 接受 Ord₀ 任意函数), 但 ψ-image 上不实现 Brw₄ 阶
- 这与 [REVIEW.md 漏洞 5 "假突破"](../REVIEW.md) 同结构

**Phase α₂ 关键测试**: 即使 ψ-image 坍缩, 是否能在 Ord₁ᴰᴹ 上证 BoundedTrich (via ψ-image)? 如果走通, 强度仍受 ψ-image 上限制 (≤ ψ(Ω_Ω)), 但形式化可达成. 进入 [BoundedTrich.lagda.md](BoundedTrich.lagda.md).
