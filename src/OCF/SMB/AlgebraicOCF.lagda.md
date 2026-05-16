# 算律 OCF 原型 — sup-based ψ on Tree-indexed Ordˢ

> 算律 OCF 的最小可编译原型. 设计分析见 [AlgebraicOCF.md](AlgebraicOCF.md).
>
> **目标**: 展示一种**无决策性**的 ψ 折叠. 强度有限 (≤ ψ(Ω_Ω)), 但作为对称性 / 教学示例存在.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.SMB.AlgebraicOCF where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import OCF.SMB.Core using (Tree; Z; ↑; Lim; indMax)
```

## §1 — 算律序数 `Ordˢ`

```agda
data Ordˢ : Set where
  Zˢ   : Ordˢ
  ↑ˢ   : Ordˢ → Ordˢ
  Limˢ : (ℕ → Ordˢ) → Ordˢ
  ΩLim : (Tree → Ordˢ) → Ordˢ      -- Tree-索引的无界 limit
```

**与 BTBO Ord-Ord 的差异**: `ΩLim` 不带 `(p : t < ℓ)` bound. 这是"无界" Ω-索引 — 标准 BTBO 不允许 (∵ 缺 trich).

## §2 — `maxˢ`: 算律 max (类比 indMax)

```agda
maxˢ : Ordˢ → Ordˢ → Ordˢ
maxˢ Zˢ        b            = b
maxˢ (↑ˢ a)    Zˢ           = ↑ˢ a
maxˢ (↑ˢ a)    (↑ˢ b)       = ↑ˢ (maxˢ a b)
maxˢ (↑ˢ a)    (Limˢ g)     = Limˢ (λ n → maxˢ (↑ˢ a) (g n))
maxˢ (↑ˢ a)    (ΩLim g)     = ΩLim (λ t → maxˢ (↑ˢ a) (g t))
maxˢ (Limˢ f)  b            = Limˢ (λ n → maxˢ (f n) b)
maxˢ (ΩLim f)  b            = ΩLim (λ t → maxˢ (f t) b)
```

**关键**: 不需要 mono 约束 (∵ Ordˢ 的 lim 不要求 mono — 论 setup 上更宽松).

## §3 — `walk-Tree`: 算律 sup over Tree-depth

```agda
-- 给定 g : Tree → Ordˢ, 算律地构造一个序数, "近似" sup_{t : Tree} g t
-- 通过结构递归 Tree:
walk-Tree : (Tree → Ordˢ) → Tree → Ordˢ
walk-Tree g Z       = g Z
walk-Tree g (↑ t)   = maxˢ (g (↑ t)) (walk-Tree g t)
walk-Tree g (Lim f) = Limˢ (λ n → walk-Tree g (f n))
```

`walk-Tree g t` 视为 "g 在所有 ≤ t 的 Tree 上取的 sup". 由 Tree 结构归纳保证终止.

## §4 — 算律 `ψ<ˢ` 折叠

```agda
ψ<ˢ : Ordˢ → Ordˢ
ψ<ˢ Zˢ        = Zˢ
ψ<ˢ (↑ˢ a)    = ↑ˢ (ψ<ˢ a)
ψ<ˢ (Limˢ f)  = Limˢ (λ n → ψ<ˢ (f n))
ψ<ˢ (ΩLim f)  = Limˢ (λ n → walk-Tree (ψ<ˢ ∘ f) (Tree-at-depth n))
  where
    Tree-at-depth : ℕ → Tree
    Tree-at-depth zero    = Z
    Tree-at-depth (suc n) = ↑ (Tree-at-depth n)
```

**关键**: 无决策性, 无三歧. ΩLim 的折叠用 `walk-Tree` 在递增深度上算 sup. Limˢ 把所有深度上的结果聚合.

## §5 — 强度 demo

```agda
-- 基本元素
ω : Ordˢ
ω = Limˢ (λ n → iter ↑ˢ n Zˢ)
  where
    iter : ∀ {A} → (A → A) → ℕ → A → A
    iter f zero    a = a
    iter f (suc n) a = f (iter f n a)

-- ε_0-级近似 (有限 Limˢ 嵌套)
ε₀-approx : Ordˢ
ε₀-approx = Limˢ (λ n → ω-tower n)
  where
    ω-tower : ℕ → Ordˢ
    ω-tower zero    = ω
    ω-tower (suc n) = Limˢ (λ k → ω-tower n)   -- 简化, 实际 ω^(ω^...)

-- ΩLim 演示 — 无界 Tree-索引的 limit
ω-via-ΩLim : Ordˢ
ω-via-ΩLim = ΩLim (λ _ → Zˢ)   -- trivial: 所有 t 映射到 Zˢ

-- 用 ψ<ˢ 折叠 ΩLim 测试
ψ-of-ΩLim : Ordˢ
ψ-of-ΩLim = ψ<ˢ ω-via-ΩLim
```

## §6 — 算律 ψ 的限制

强度估算:
- `Limˢ` 给可数 ω-级
- `ΩLim` 看似 uncountable, 但 `walk-Tree` 算律下只见到 countable Tree
- ψ<ˢ 折叠后, 强度 ≤ ψ(Ω_Ω) (countable Brouwer-tree 上限)

**没有突破 BTBO 现有强度**. 仅展示算律方法可编译.

## §7 — 与 BTBO ψ< 的对比

| 维度 | BTBO ψ< | Ordˢ ψ<ˢ (算律) |
|------|--------|----------------|
| 决策依赖 | `<ᴺ-dec`, `<-dec` | **无** |
| 单调性 | strict mono | 仅 weak mono (≤) |
| 强度 | ψ(Ω_Ω) ~ ψ(Ω_(Ω^Ω)) (Higher.agda) | ≤ ψ(Ω_Ω) |
| 工程复杂度 | 高 (大量 case 分析) | 低 (统一 sup) |
| OCF 标准性 | 接近 Buchholz 标准 | 偏离, 等同于 "max-fold of countable approx" |

## §8 — 总结

✅ 算律 OCF **可编译** — 原理上可行.

⚠️ 强度天花板 = countable Brouwer-tree max ≈ ψ(Ω_Ω). **不超过 BTBO**.

💡 关键洞察: 决策性是 ψ 强度的**信息源**. 用算律 lub 替代会丢失 m vs n 的精确分级信息, 强度大幅下降. 在 ψ-folding 这个具体场景, "决策" 不仅是工程选择, 是**强度本质**.

📋 工程结论: 不推荐在本仓库继续走算律 OCF 路线. 回 [ROADMAP §3.1](../ROADMAP.md) Phase 7 HigherOrdᴰ² (机械迭代, 高确定性 ψ(Ω_(Ω·2)) 强度).
