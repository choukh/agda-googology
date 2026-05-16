# SMB Naive Probe: 用 SMB Core 重攻 Naive `<-1-dec` (诊断报告)

> **目的**: 检验 [SMB/Core](Core.lagda.md) 的 `bound` 算子能否解锁 [PastBTBO/Naive/Phase1](../PastBTBO/Naive/Phase1.lagda.md) 撞过的 BoundedTrich 障碍.
>
> **结论 (剧透)**: ❌ 失败. SMB-trees 解 *算律* (+-lmono 类), 不解 *决策* (BoundedTrich 类). 详见 §3-4.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.SMB.Naive where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import OCF.BTBO
open import OCF.SMB.Core
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich using (Ordᴰ; cumsum; cumsum-mono) renaming (_<_ to _<ᴰ_; zero to zeroᴰ; suc to sucᴰ; lim to limᴰ; monotonic to monotonicᴰ)
```

## §1 — 重温目标

[PastBTBO/Naive/Phase1.lagda.md](../PastBTBO/Naive/Phase1.lagda.md) 在 `<-1-dec` 的 `limΩ/limΩ` 情形撞墙:

    <-1-dec (limΩ x p) (limΩ y q) = ???    -- 需 Ordᴰ 上 x, y 三歧

需要 `bound : Ordᴰ → Ordᴰ → Ordᴰ` 满足 `x <ᴰ bound x y` 与 `y <ᴰ bound x y`, 然后 `BoundedTrich.<-dec` 给三歧.

[FINDINGS §5.3](../PastBTBO/Naive/FINDINGS.md) 诊断: 所有 `+ᴰ`, `sucᴰ`, `limᴰ` 组合的"自然上界"都需要 `+-lmono` (`a < b → a + c < b + c`), 而**该定理在 Ordᴰ 上不真** (`0 + ω = 1 + ω`).

## §2 — SMB 提供的工具

`SMB.Core` 给出:
- `Tree`: 不带 mono 约束的 Brouwer 树
- `indMax : Tree → Tree → Tree`
- `bound : Tree → Tree → Tree = ↑ (indMax a b)`
- `a<bound`, `b<bound`: 在 **Tree** 上 ✓
- `toTree : Ordᴰ → Tree`: 桥接
- `toTree-< : a <ᴰ b → toTree a < toTree b`: 桥接保 <

## §3 — 尝试: `bound` 在 Ordᴰ 上的构造

```agda
-- Step 1: 桥接到 Tree
-- Step 2: 在 Tree 上用 indMax 取 max
-- Step 3: 桥接回 Ordᴰ ???

fromTree : Tree → Ordᴰ
fromTree Z       = zeroᴰ
fromTree (↑ t)   = sucᴰ (fromTree t)
fromTree (Lim f) = limᴰ (cumsum (fromTree ∘ f)) (cumsum-mono _)
```

**关键障碍**: 要让 `bound-ᴰ x y := fromTree (bound (toTree x) (toTree y))` 给出 `x <ᴰ bound-ᴰ x y`, 需:

    toTree-≤-implies-Ordᴰ-≤ : toTree x ≤ t → x ≤ᴰ fromTree t

(其中 `_≤ᴰ_ a b := a <ᴰ b ⊎ a ≡ b`).

```agda
-- 弱不等 on Ordᴰ
_≤ᴰ_ : Ordᴰ → Ordᴰ → Set
a ≤ᴰ b = a <ᴰ b ⊎ a ≡ b
```

尝试证明 `toTree-≤-implies-Ordᴰ-≤`:

- **limᴰ 情形 (`≤-limiting`)**: 需 `∀ k → toTree (f' k) ≤ t  ⇒  limᴰ f' mf' ≤ᴰ fromTree t`.
- 但 `limᴰ f' mf' ≤ᴰ fromTree t` 在 BTBO 上**结构性**难证 — `_<ᴰ_` 没有 "limᴰ < X" 的直接构造子, 需 X 含有 "包含 limᴰ" 的子结构.
- 通常这需要 `fromTree t` 的 cumsum-展开能"超出" `limᴰ f' mf'` 的所有 `f' k`.
- 由 cumsum 是 `+` 累加, **该步退化为 +-lmono**.

因此 `toTree-≤-implies-Ordᴰ-≤` 在 `limᴰ/Lim` 情形再次撞 `+-lmono`.

## §4 — 诊断: SMB 不解 Naive 障碍

| 角度 | SMB 解的 | Naive 需的 | 差距 |
|------|---------|----------|------|
| 算律 | `indMax (↑ a) (↑ b) = ↑ (indMax a b)` strict 单调 | `a + b` 左单调 (`+-lmono`) | 不一样 — SMB 给 `indMax`, 不给 `+` |
| 上界 | `indMax-≤L/R` 在 **Tree** 上的 LUB | strict 共同上界在 **Ordᴰ** 上 | Tree 是新类型, 桥接需 +-lmono 退化 |
| 决策 | 不解 — Tree 上 `<-dec` 是 [constructive taboo](https://arxiv.org/abs/2602.10844) | BoundedTrich 上的 trich | SMB 不增强决策 |

**核心命题**: SMB-trees 的设计目标是**多参数 well-founded recursion**, 不是 OCF 折叠的决策性. 论文 ([Eremondi 2023 §1](https://arxiv.org/abs/2312.06962)) 明确说 "for assigning sizes for termination" — 是 size, 不是 OCF 折叠.

## §5 — 局部胜利: bounded Ord-Ord 已经够了

回看 [BTBO.lagda.md:836-857](../BTBO.lagda.md#L836-L857) 的 `Ord-Ord`:

```agda
-- 已存在的 BTBO 模板:
-- module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
--   data Ord₊ : Set where
--     ...
--     limᵢ : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊
```

`limᵢ p f` 携带 `p : i < ℓ` — **bound 已内嵌**. 这就是 Naive Phase 1 §5 路径 B 的本质实现 — **BTBO 已经做了**, 给出 ψ(Ω_Ω). 用 SMB 重做相同结构 = 无强度增益.

要超过 ψ(Ω_Ω), 必须让 `limΩ` 真正**无界** (over all Ordᴰ). 这需要 Ordᴰ 上的无条件 trich, 而无条件 trich on Brouwer 树是 [constructive taboo](https://arxiv.org/abs/2602.10844).

## §6 — 验证: 至少 Tree-上的 bound 可用

为证 Phase A 工具非空, 端到端 demo:

```agda
-- bound on Tree 顶级 binding
example-bound : Tree
example-bound = bound Z (↑ Z)   -- = ↑ (indMax Z (↑ Z)) = ↑ (↑ Z) ≈ 2

example-bound-eq : example-bound ≡ ↑ (↑ Z)
example-bound-eq = refl

-- 一个稍复杂的: bound (toTree (sucᴰ zeroᴰ)) (toTree zeroᴰ)
example-Ordᴰ-bound : Tree
example-Ordᴰ-bound = bound (toTree (sucᴰ zeroᴰ)) (toTree zeroᴰ)

example-Ordᴰ-bound-eq : example-Ordᴰ-bound ≡ ↑ (↑ Z)
example-Ordᴰ-bound-eq = refl

-- 在 Tree 上的严格上界:
example-< : toTree (sucᴰ zeroᴰ) < example-Ordᴰ-bound
example-< = a<bound (toTree (sucᴰ zeroᴰ)) (toTree zeroᴰ)
```

✅ 编译通过 — **SMB Core 工具集在 Tree 上完全可用**, 但 **不能桥接回 Ordᴰ** 以解锁 BoundedTrich 障碍.

## §7 — Phase B-1 总结

- ✅ Phase A SMB Core 落地 (Tree + indMax + bound)
- ❌ Naive `<-1-dec` 的 limΩ/limΩ **未解锁** — 因 SMB 在 Ordᴰ 上桥接需 +-lmono 退化
- 📊 强度增益: **0** — Tree 上的 bound 不能拿到 Ordᴰ 上用
- 💡 真正洞察: BoundedTrich 障碍是**决策性**问题 (constructive taboo), 不是**算律**问题 (SMB 解的)

后续路线: 见 [FINDINGS.md](FINDINGS.md).
