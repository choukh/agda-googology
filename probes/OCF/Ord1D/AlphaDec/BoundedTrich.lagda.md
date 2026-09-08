---
title: Ord₁ᴰ - BoundedTrich (R4: α-decidable 软化版本)
---

# Ord₁ᴰ BoundedTrich (Phase R4)

> 本文件: Phase R4, 在 [R3-alt mutual data Ord₁ᴰ](IR.lagda.md) 上尝试 `<₁-dec` 与 `<₁-α-dec` (α-decidable 软化版本).
>
> **核心检验**: lim₁/lim₁ case 是否真撞 Ord₀ 不可决性墙? α-decidable 命题截断版本能否绕道?

## 模块声明

```agda
{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module OCF.Ord1D.AlphaDec.BoundedTrich where
```

## 依赖

```agda
open import Cubical.Foundations.Prelude using (Type; _≡_; refl)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁; rec)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import OCF.BTBO using (module Trich; module Ord-Basic)
open Trich using () renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open Ord-Basic using (Ord₀)
open import OCF.Ord1D.AlphaDec.IR
  using (Ord₁ᴰ; _<₁_; _<₀_; <₁-trans; monotonic₀; monotonic₁)
```

## 1. 全函数 trichotomy 试探 (lim₀/lim₀ ✓, lim₁/lim₁ ✗)

仿 BTBO `<-dec` (行 699-707) 与 Ord1D/BoundedTrich `<₁-dec` (行 80-92).

**lim₀/lim₀ case**: 用 BTBO Trich.ℕ <-dec, 同 BTBO 标准模式.

**lim₁/lim₁ case**: 需要 Ord₀ 上的 BoundedTrich, 但 Ord₀ 是 Brw₃ 顶层无 monotonic 约束, **不可决**.

我们先尝试构造 `<₁-dec`, 形式化记录撞墙位置:

```agda
open Ord₁ᴰ
open _<₁_
```

构造 `<₁-dec` 的核心子 case (suc/suc, lim₀/lim₀):

```agda
<₁-dec-trivial : ∀ {a b : Ord₁ᴰ} → a <₁ suc b → b ≡ a ⊎ a <₁ b
<₁-dec-trivial zero    = inj₁ refl
<₁-dec-trivial (suc q) = inj₂ q
```

`<₁-dec-trivial` 是子引理: a < suc b 时, a = b 或 a < b. 这避免完整 `<₁-dec` 的复杂性, 先抓子 case.

实际上, 完整 `<₁-dec` 在 lim₁/lim₁ case 撞墙的本质是: 我们不能从 `a <₁ lim₁ f mono` 与 `b <₁ lim₁ f mono` 反推 a, b 的相对大小, 因为 lim₁ 的 Ord₀-index 无法决策.

## 2. lim₁/lim₁ case 撞墙诊断

考虑 `<₁-dec (lim₁ x p) (lim₁ y q)`, 其中:
- `lim₁ x p : a <₁ lim₁ f mono` 通过 index `x : Ord₀` 与证据 `p : a <₁ f x`
- `lim₁ y q : b <₁ lim₁ f mono` 通过 index `y : Ord₀` 与证据 `q : b <₁ f y`

要决定 `a <₁ b ⊎ b <₁ a ⊎ a ≡ b`, 仿 BTBO 模式应该 dispatch on (x, y) 的大小:
- 若 x <₀ y: f x <₁ f y (mono), 于是 a <₁ f y, 与 q 一起用 IH 递归
- 若 y <₀ x: 对偶
- 若 x ≡ y: f x ≡ f y, 用 path 转换 p, q 后递归

但 `x <₀ y ⊎ y <₀ x ⊎ x ≡ y` 在 Ord₀ (Brw₃ 顶层) 上**不可决** — 这是 constructive taboo 在 R3-alt mutual data 设计上的具体表现.

**形式化 hole**:

> 完整 `<₁-dec` 的 lim₁/lim₁ case 需要 `(x y : Ord₀) → x <₀ y ⊎ y <₀ x ⊎ x ≡ y`, 此项在 Agda --safe (含 cubical) 内**不可证**.
>
> 历史 [Phase A-D γ-bounded](../BoundedTrich.lagda.md) 通过把 lim₁ 索引从 Ord₀ 改为 γ-bounded Ordᴰ (`(α : Ordᴰ) → α < γ → Ord₁ᴰ`) 绕道, 代价: sup(Ord₁ᴰ) ≤ Ω_1 (Brw₃), 强度仅达 ψ(Ω_Ω).
>
> R3-alt 保留 lim₁ via Ord₀ 期望 sup(Ord₁ᴰ) ≤ Ω_2 (Brw₄), 但 `<₁-dec` 撞 Ord₀ 不可决性墙.

## 3. α-decidable 软化: ∥-∥₁ 截断版本

尝试用命题截断弱化 trichotomy. 因 Ord₀ 不可决, 我们也不能直接证 `∥ x <₀ y ⊎ y <₀ x ⊎ x ≡ y ∥₁` — 命题截断只隐藏决策的"哪个", 不创造决策本身.

实际上, 论文 α-decidable 给出更弱的形式: `α-dec α P = ∥ Σ y. P ↔ z ≤ y ∥₁`. 这等价于"存在 y 使 P 真等价于 z ≤ y". 对 P = trichotomy, 这要求构造 y : Ordᴰ 使得"三歧真 ↔ 某固定 Ordᴰ 关系".

但 Ord₀ trichotomy 不是单调命题 (truth value 不随 y 单调变化), 因此 α-decidable 形式**不适用**于 Ord₀ trichotomy.

**形式化 finding**: α-decidable 框架 (论文 Def 5) 处理的是**单调命题** (即 P → z ≤ y 单调 in y). Ord₀ trichotomy 不是这种命题, 因此 α-decidable 不提供 Ord₀ 上的"分级决策"绕道.

这与 [Plan B 审稿](../../../.claude/plans/src-ocf-memoized-sparrow.md#关键风险预诊断) 的"目标错位"批判精确对应: α-decidable 改的是"命题决策性的分类", 不能创造原本不可决命题的决策性.

## 4. R4 判定结果

**R3-alt + R4 综合判定**:

1. **R3-alt 数据层 ✓**: mutual data Ord₁ᴰ + _<₁_ + lim₁ via Ord₀ typecheck 通过 ([IR.lagda.md](IR.lagda.md))
2. **R4 `<₁-dec` ✗**: lim₁/lim₁ case 不可证 — Ord₀ trichotomy 是 constructive taboo
3. **R4 α-decidable 软化 ✗**: 论文 α-decidable 框架适用于单调命题, 不适用于 trichotomy
4. **强度论证**: 即使 R3-alt 数据层达 Brw₄, 缺 BoundedTrich 阻塞 Ord-Ord 模块的移植 (Phase R5 需要 `<₁-dec` 作 ψ<₁ dispatch)

**形式化结论**: R3-alt + α-decidable 路径在 Agda `--safe --cubical` 内**不增强度突破 ψ(Ω_Ω_2)**.

## 5. 与已知撞墙的对照表

| 路径 | lim₁ 索引域 | <₁-dec | sup(Ord₁ᴰ) | 撞墙形态 |
|------|------------|--------|------------|---------|
| **历史 Phase A-D γ-bounded** | `(α : Ordᴰ) → α < γ → Ord₁ᴰ` | ✓ (BTBO `<-dec`) | ≤ Ω_1 (Brw₃) | 强度坍缩到 ψ(Ω_Ω) |
| **DM Path α (IIR ψ-image)** | `Ord₀ → Ord₁ᴰᴹ` (但 mono via ψ-down) | ψ-image only | ≤ Ω_1 (Brw₃) | strength-equivalence refl |
| **R3-alt mutual data** | `Ord₀ → Ord₁ᴰ` (mono via _<₁_) | ✗ (Ord₀ trichotomy 不可决) | Brw₄ 可达 但无 BoundedTrich | Ord₀ trichotomy taboo |
| **R3-alt + α-decidable** | 同上 | ∥-∥₁ 截断也不可证 | 同上 | α-decidable 不适用 trichotomy |

三种设计都形式化达到了"sup-or-trich"的两难: 要么 sup 受限 (γ-bounded), 要么 trich 不可证 (Ord₀-indexed). **没有第三条路在 Brouwer-tree paradigm + cubical 内**.

## 6. 与 de Jong-Eremondi-Forsberg 2026 taboo 的关系

形式化验证了论文 constructive taboo: "Brouwer trees + total trichotomy" 不可兼.

具体表现:
- 历史 γ-bounded 牺牲 Brw 阶 (sup ≤ Ω_1) 换 trichotomy
- DM Path α 牺牲 trichotomy 强度 (ψ-image only) 保 Brw₄ 语法
- R3-alt + α-decidable 牺牲 trichotomy 可证性 (∥-∥₁ 截断也不可) 保 Brw₄ 语法 + 直接 _<₁_

cubical 工具 (HIT trunc, 命题截断) 不改变 taboo 边界 — 这是 [Plan B 审稿](../../../.claude/plans/src-ocf-memoized-sparrow.md#关键风险预诊断) "cubical 是工程简化不是强度突破启用器" 的形式化实证.

## 7. 是否推进 R5-R6?

按 plan, R5-R6 依赖 R4 `<₁-dec` 工作:
- R5 Ord-Ord 移植需要 `<₁-dec` 作 ψ<₁ 的三歧 dispatch
- R6 strength-witness 需要 R5 的 ψ<₁

**R4 结论**: <₁-dec 不可证, α-decidable 不可绕道. R5-R6 在此设计下**注定与 DM Path α 同形撞墙**.

**判定**: 不推进 R5-R6. 写 [FINDINGS.md](FINDINGS.md) 总结诚实诊断. 类比 DM Path α 的形式化撞墙地图.
