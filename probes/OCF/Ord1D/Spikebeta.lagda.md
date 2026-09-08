# Spike β — Inductive-Recursive Ord₁ᴰ ⇄ ψ₁ (真正全新方向)

> Cross-links: [SpikeA1](SpikeA1.lagda.md), [SpikeA2](SpikeA2.lagda.md), [SpikeA3](SpikeA3.lagda.md), [Spikeepsilon](Spikeepsilon.lagda.md), [FINDINGS umbrella](FINDINGS.md)

完全跳出 mono / γ-bound 范式. **不在 Ord₁ᴰ 内部定义 `_<₁_` data**, 而是用 ψ₁ 折叠 image 诱导:

- `ψ₁ : Ord₁ᴰ → Ordᴰ` (互递归定义)
- mono 字段: ψ₁-image 单调 (`ψ₁ (f n) < ψ₁ (f m)`)
- BoundedTrich on Ord₁ᴰ 通过 Ordᴰ 的 BoundedTrich 转移

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Ord1D.Spikebeta where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.BTBO using (module Trich; module BoundedTrich; module Ord-Basic; injᵃ; injᵇ; injᶜ)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; _<_; <-dec; <-trans; monotonic)
  renaming (zero to zeroᴰ; suc to sucᴰ; lim to limᴰ)
open Ord-Basic using (Ord₀)
```

## 1. 设计核心: Ord₁ᴰ ⇄ ψ₁ 互递归

```agda
data Ord₁ᴰ : Set
ψ₁ : Ord₁ᴰ → Ordᴰ
```

mono 谓词用 ψ₁-image 表达:

```agda
mono₀-β : (ℕ → Ord₁ᴰ) → Set
mono₀-β f = ∀ {n m} → n <ᴺ m → ψ₁ (f n) < ψ₁ (f m)

mono₁-β : (Ord₀ → Ord₁ᴰ) → Set
mono₁-β f = (a b : Ord₀) → ψ₁ (f a) < ψ₁ (f b) ⊎ ψ₁ (f b) < ψ₁ (f a) ⊎ ψ₁ (f a) ≡ ψ₁ (f b)
-- 注意: 由于 Ord₀ 上无序, mono₁-β 必须是 image 上的 unconditional trichotomy
-- (类似 ε witness, 但用 ψ₁-投影后的 Ordᴰ 关系)
```

```agda
data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ) (mono₀ : mono₀-β f) → Ord₁ᴰ
  lim₁ : (f : Ord₀ → Ord₁ᴰ) (mono₁ : mono₁-β f) → Ord₁ᴰ
```

ψ₁ 定义:

```agda
ψ₁ zero        = zeroᴰ
ψ₁ (suc a)     = sucᴰ (ψ₁ a)
ψ₁ (lim₀ f m)  = limᴰ (ψ₁ ∘ f) m
ψ₁ (lim₁ f m)  = ψ₁ (f Ord-Basic.zero)  -- 强度坍缩点 (见诊断)
```

**实测撞墙诊断 — ψ₁ (lim₁ f m) 的强度损失墙**:

我们想给 `ψ₁ (lim₁ f m)` 一个有意义的 Ordᴰ 值, 它应该是 "Ord₀-索引极限" 在 Ordᴰ 中的 collapse. 但:

- `Ordᴰ` 的 lim 只接受 `ℕ → Ordᴰ` 索引函数 (即 ω-索引极限).
- `ψ₁ ∘ f : Ord₀ → Ordᴰ` 不能直接用 `limᴰ` 收尾.
- 没有 `enum : ℕ → Ord₀` 全函数 (Ord₀ 不可数).

可能的"折叠"方式:
1. ψ₁ (lim₁ f m) = `ψ₁ (f Ord-Basic.zero)`  — **坍缩到单点**, 强度退化为 Ordᴰ (本实现)
2. ψ₁ (lim₁ f m) = `limᴰ (ψ₁ ∘ f ∘ enum) m-modified` — 需 enum : ℕ → Ord₀, 不存在
3. ψ₁ 输出参数化: `ψ₁ : Ord₁ᴰ → Ord (ψᴰ n)` — 进入 Higher.agda 框架, 不是 Spikebeta 设计

**强度评估**: 选项 1 (本实现) 强度坍缩为 Ordᴰ (≈ ψ(Ω_Ω) baseline), **远低于 ψ(Ω_Ω_2)**. lim₁ 的 Ω-索引能力被 ψ₁ 完全忽略.

## 2. 诱导关系 `_<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set`

```agda
_<₁_ : Ord₁ᴰ → Ord₁ᴰ → Set
a <₁ b = ψ₁ a < ψ₁ b
```

这是非-inductive (不是 data type, 是定义).

## 3. BoundedTrich (诱导)

由于 `_<₁_` 是 ψ₁-诱导的, BoundedTrich 直接由 Ordᴰ 上的 BoundedTrich 给出:

```agda
<₁-dec-β : ∀ {a b c} → a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ (ψ₁ a ≡ ψ₁ b)
<₁-dec-β {a} {b} p q with <-dec p q
... | injᵃ ψa<ψb = injᵃ ψa<ψb  -- a <₁ b
... | injᵇ ψb<ψa = injᵇ ψb<ψa  -- b <₁ a
... | injᶜ ψa≡ψb = injᶜ ψa≡ψb   -- ψ₁ a ≡ ψ₁ b (注意 ≠ a ≡ b)
```

**关键瑕疵**: 诱导的 `_<₁_` 不是 Ord₁ᴰ 上"自然"的 < 关系 — 多个 distinct Ord₁ᴰ 项可以有相同的 ψ₁ 投影. 所以 `<₁-dec-β` 的 injᶜ 给出的是 `ψ₁ a ≡ ψ₁ b`, 不是 `a ≡ b`. 这是"信息损失".

实际上, BoundedTrich 的真实需求是 `a <₁ b ⊎ b <₁ a ⊎ a ≡ b`. 在 Spikebeta 设计下, **无法证 ψ₁ 是单射**, 所以 `ψ₁ a ≡ ψ₁ b` 不能推出 `a ≡ b`. 这意味着:

```agda
-- 真正的 BoundedTrich on Ord₁ᴰ 是不可证的:
-- <₁-dec : a <₁ c → b <₁ c → a <₁ b ⊎ b <₁ a ⊎ a ≡ b
-- 因为 injᶜ case 我们只能给 ψ₁ a ≡ ψ₁ b, 不能推 a ≡ b
```

## 4. 撞墙诊断: 双重墙

Spikebeta 方向**撞两堵墙**, 都是设计的内在限制:

**墙 1 — 强度坍缩** (ψ₁ collapse Ord₀-索引): lim₁ 的 Ω-索引能力被 ψ₁ 投影丢失. 实测强度上限 ≈ Ordᴰ, 远低于目标 ψ(Ω_Ω_2).

**墙 2 — BoundedTrich 不真** (ψ₁ 非单射): 诱导 `_<₁_` 不能区分 ψ₁-同投影但 syntactically distinct 的 Ord₁ᴰ 项. 真正的 BoundedTrich (含 `a ≡ b` 分支) 在 Spikebeta 不可证.

## 5. 结论

**Spike β 实测结果**: IR 设计在 Agda 中**形式上可编译**, 但**两个本质墙**让它不能达成 Ord₁ᴰ 的目标:

1. ψ₁ 的输出类型 (Ordᴰ) 表达力不够装下 Ord₀-索引信息
2. 诱导 `_<₁_` 不是真正的 Ord₁ᴰ 上的良序, BoundedTrich 不可证

**与 [Higher.agda](../Higher.agda) 的关系**: Higher.agda 的 ψ<Ω 用了输出参数化 (`Ord (ψᴰ n)` 而非 Ordᴰ), 巧妙绕开墙 1. Spikebeta 没有这个参数化, 不能复现. 如果引入参数化, 就成为 Higher.agda 的复刻, 不再是"Ord₁ᴰ" 的 IR 设计.

```agda
-- 形式化验证 (允许编译但不达成 BoundedTrich):
β-Wall-Demo : (f : Ord₀ → Ord₁ᴰ) (m : mono₁-β f) (a b : Ord₀)
            → ψ₁ (lim₁ f m) ≡ ψ₁ (f Ord-Basic.zero)
β-Wall-Demo f m a b = refl  -- 表明 ψ₁ 完全忽略 a, b, 强度坍缩到 f zero
```

**Spike β 结论**: 不是 Phase B 候选. IR mono via ψ-image 在不引入参数化输出的前提下, 必然撞"输出表达力"和"诱导关系不真"两堵墙.

下一步 → 见 [Spikeepsilon](Spikeepsilon.lagda.md) (Witness as field 全新方向).
