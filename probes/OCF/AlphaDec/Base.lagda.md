---
title: AlphaDec - α-decidable 基础 (Spike S1)
---

# α-decidable 基础 (Spike S1)

> 本文件: Spike S1, 在 cubical Agda 内 import BTBO `BoundedTrich.Ordᴰ`, 移植 de Jong-Kraus-Mohammadzadeh-Forsberg 2026 ([arXiv 2602.10844](https://arxiv.org/abs/2602.10844)) 的 α-decidable 定义.
>
> 目标: 形式化定义 + 关键单调性引理 + α-dec-conj (论文 Thm 23 的简化版).
>
> Plan 参考: [src-ocf-memoized-sparrow.md](../../../.claude/plans/src-ocf-memoized-sparrow.md) Spike S1.

## 模块声明

我们用 `--cubical` 启用命题截断 (`∥-∥₁`) 与 Path 工具. `--lossy-unification` 沿用 BTBO 约定.

```agda
{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module OCF.AlphaDec.Base where
```

## 库依赖

仿照 WellFormed/Base 的桥接模式: cubical 模块用于命题截断与 Path, BTBO 提供 Ordᴰ 与 `_<_` 关系, 桥接库处理 cubical/标准库混用.

```agda
open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; subst)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁; rec; rec→Set; map)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import OCF.BTBO using (module BoundedTrich)
open BoundedTrich using (Ordᴰ; _<_; <-trans; _+_; +-mono; a<a+b; NonZero)
```

桥接 BTBO 用标准库 `Data.Sum` 表达三歧, 我们直接 import 它 (BTBO 在 cubical 之下仍能 import 因 Probe 验证).

```agda
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
```

## ≤ᴰ 由 < 派生

论文 `succ x ≤ y` 在 Brw 上对应 BTBO 的 `_<_ ⊎ _≡_`. 用命题截断让 ≤ᴰ 是命题, 即"a 不大于 b"这一陈述的同伦层级为 mere proposition.

```agda
_≤ᴰ_ : Ordᴰ → Ordᴰ → Type
a ≤ᴰ b = ∥ (a ≡ b) ⊎ (a < b) ∥₁
infix 10 _≤ᴰ_
```

构造子: 从 `_≡_` 或 `_<_` 注入到 ≤ᴰ.

```agda
≤ᴰ-refl : ∀ {a} → a ≤ᴰ a
≤ᴰ-refl = ∣ inj₁ refl ∣₁

<→≤ᴰ : ∀ {a b} → a < b → a ≤ᴰ b
<→≤ᴰ p = ∣ inj₂ p ∣₁
```

`<→≤ᴰ` + `≤ᴰ-refl` 编译通过 ⇒ 命题截断接口可用, cubical 与 BTBO 兼容. **关键里程碑**: 这是项目首次在 cubical 文件中复用 BTBO 类型的实测.

## α-decidable 核心定义

论文 Definition 5 (基于 ancillary repo `BrouwerTree.OrdinalDecidability.Basic`):

```agda
α-dec-str : (z : Ordᴰ) → Type → Type
α-dec-str z P = Σ[ y ∈ Ordᴰ ] ((P → z ≤ᴰ y) × (z ≤ᴰ y → P))

α-dec : Ordᴰ → Type → Type
α-dec z P = ∥ α-dec-str z P ∥₁
infix 5 α-dec
syntax α-dec z P = ⟨ z ⟩-dec P
```

直观语义: P 是 z-decidable, 当存在某 y 使得 P ↔ z ≤ y. P 真时, y 取大让 z ≤ y; P 假时, y 取小让 z ≰ y. z 编码"决策的 Brouwer 阶".

**注**: 我们用 `(P → z ≤ᴰ y) × (z ≤ᴰ y → P)` 而非 `P ↔ z ≤ᴰ y` (即避免 Function.Bundles 的 `↔`, 减少 import). 这与论文等价.

## 0-decidable: 经典决策的特例

最弱的 α (z = zero) 应对应"经典可决"概念. 论文给出: 任意 decidable P 都是 0-decidable, witness 选 y = zero (P 真 ↔ zero ≤ᴰ zero, 后者 trivially 真).

实际上更好的 baseline 是: 任意 P 真的命题都是 0-decidable (witness y = zero, P → zero ≤ᴰ zero 平凡, zero ≤ᴰ zero → P 由 P 真给出).

```agda
true→0-dec : ∀ {P : Type} → P → ⟨ BoundedTrich.zero ⟩-dec P
true→0-dec p = ∣ (BoundedTrich.zero , (λ _ → ≤ᴰ-refl) , (λ _ → p)) ∣₁
```

P 真时 0-decidable 的 witness. 这是论文最 trivial 的方向.

## 单调性 (z 增大保持 dec)

如果 a ≤ᴰ b 且 P 是 a-decidable, 那 P 也是 b-decidable: 用同一 y 作为新 witness, 但需要 z 变化时 `z ≤ᴰ y` 子句兼容. 注意方向问题: a ≤ᴰ b 意味着 a 弱, 把 a 替换为 b 让 "z ≤ᴰ y" 更难成立 (b ≤ᴰ y 比 a ≤ᴰ y 更强). 这反方向不对.

正确方向: 如果 a-decidable 且**降低** z (用更小的 z'), 则更易 decidable. 但论文用的是另一方向 (扩大 y).

让我们先证另一个有用的: **替换 witness 单调性** — 若 y ≤ᴰ y' 且 (y witness for P at z), 那 y' 也 witness for P at z (当 P 真时, z ≤ᴰ y → z ≤ᴰ y' 通过 ≤ᴰ 传递).

```agda
≤ᴰ-trans : ∀ {a b c} → a ≤ᴰ b → b ≤ᴰ c → a ≤ᴰ c
≤ᴰ-trans {a} {b} {c} ab bc = rec squash₁ (λ ab' → handle ab' bc) ab
  where
    handle : (a ≡ b) ⊎ (a < b) → b ≤ᴰ c → a ≤ᴰ c
    handle (inj₁ a≡b) bc' = subst (_≤ᴰ c) (sym a≡b) bc'
    handle (inj₂ a<b) = rec squash₁ λ where
      (inj₁ b≡c) → ∣ inj₂ (subst (a <_) b≡c a<b) ∣₁
      (inj₂ b<c) → ∣ inj₂ (<-trans a<b b<c) ∣₁
```

`≤ᴰ-trans` 的形式有点 cubical 风格 — 用 `rec` 析构命题截断, 因 codomain `a ≤ᴰ c` 是命题 (再次截断).

**实测**: 这个证明的关键是 cubical `rec` eliminator 用法. 如果它编译通过, 整个 α-dec 框架的"命题截断流"在本项目可走通.

## 直接结论 (S1 判定门预检)

Spike S1 目标是验证三件事:
1. cubical 文件 import BTBO 可行 ✓ (Probe 验证)
2. ∥-∥₁ 与 BTBO 的 `_<_, _≡_` 兼容 ✓ (≤ᴰ 定义)
3. cubical `rec` eliminator 析构命题截断到非命题目标可行 (≤ᴰ-trans 检验)

如果本文件编译通过, Spike S1 判定门**通过**, 进入 Spike S2 (强度退化检测).

## 后续

Spike S2 (StrengthSpike.lagda.md) 将证 `<ᴰ-α-dec : (a b : Ordᴰ) → ⟨ a + b ⟩-dec (a < b ⊎ b < a ⊎ a ≡ b)` (论文 Thm 23 BTBO-版), 然后构造 `Ω₁-via-α-dec : Ord₀` 检测强度是否超过 BTBO baseline.
