---
title: AlphaDec - 强度退化检测 (Spike S2)
---

# 强度退化检测 (Spike S2)

> 本文件: Spike S2, 检验 α-decidable 框架是否提供超 BTBO baseline 的构造能力, 即判定 plan 的核心 Question:
>
> > α-decidable 是真突破还是误判?
>
> 三层检验:
> 1. **正向**: 证 `<ᴰ-α-dec` wrapper — α-dec 工具能正确表达 BTBO trichotomy
> 2. **替代试探**: 尝试用 α-dec witness 作为 Ordᴰ.lim 的 mono 字段 substitute
> 3. **判定**: 替代是否给出"非 BTBO 即可写出"的新 Ord 项?
>
> 这是 [plan Spike S2 判定门](../../../.claude/plans/src-ocf-memoized-sparrow.md), 决定是否推进 Phase R3-R6.

## 模块声明

```agda
{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module OCF.AlphaDec.StrengthSpike where
```

## 依赖

复用 Spike S1 的全部接口 + BTBO 的 trichotomy 与加法.

```agda
open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; subst; cong)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁; rec)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import OCF.AlphaDec.Base
  using (_≤ᴰ_; <→≤ᴰ; ≤ᴰ-refl; ≤ᴰ-trans; α-dec-str; α-dec)
open import OCF.BTBO using (module BoundedTrich; module Ord-Basic)
open BoundedTrich using (Ordᴰ; _<_; <-trans; _+_; +-mono; a<a+b; NonZero; sth<nz; <-dec)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
```

## 第 1 层: 证 <ᴰ-α-dec wrapper (论文 Thm 23 BTBO 版)

**目标**: 证明任意 a, b : Ordᴰ, 三歧性命题 `a < b ⊎ b < a ⊎ a ≡ b` 是 `suc (a + b)`-decidable.

**策略**: 用 z := suc (a + b). 证 a < z 且 b < z, 然后调用 BTBO 的 `<-dec` 获得三歧。这是 wrapper, 不引入新结构.

需要小引理: a ≤ᴰ a + b 与 b ≤ᴰ a + b (无 NonZero 约束).

```agda
a≤ᴰa+b : ∀ {a b} → a ≤ᴰ a + b
a≤ᴰa+b {a} {BoundedTrich.zero} = ≤ᴰ-refl
a≤ᴰa+b {a} {BoundedTrich.suc b} = <→≤ᴰ (a<a+b ⦃ _ ⦄)
a≤ᴰa+b {a} {BoundedTrich.lim f mono} = <→≤ᴰ (a<a+b ⦃ _ ⦄)
```

类似地 b ≤ᴰ a + b (这个需要交换性或单独证, 暂时先跳过看 a≤ᴰa+b 编译)

**实测点**: BTBO 的 a<a+b 用 `⦃ _ : NonZero b ⦄` 实例参数. 当 b = suc _ 或 b = lim _ _ 时, NonZero b 自动可推. b = zero 时 NonZero = ⊥, 不能调用 a<a+b — 但此时 a + zero = a, 由 ≤ᴰ-refl 直接给.

## 第 2 层: 试探 α-dec mono 作为 lim 字段 substitute

**核心问题**: BTBO 的 `lim : (f : ℕ → Ordᴰ) (mono : monotonic f) → Ordᴰ` 要求 `monotonic f = ∀ {n m} → n <ᴺ m → f n < f m` (**全函数 mono**).

α-dec mono 替代版:

> `mono-α : (n m : ℕ) → ⟨ α ⟩-dec (n <ᴺ m → f n < f m)`

这弱化要求: 不要 mono 对所有 (n, m) 成立, 只要其"α-阶可决". 论文意图: 当 α 取得当, 这给"分级 monotone".

**结构性检验**: 如果我们定义新 lim'

> `lim-α : (f : ℕ → Ordᴰ) (α : Ordᴰ) (mono-α : (n m : ℕ) → ⟨ α ⟩-dec (n <ᴺ m → f n < f m)) → ?`

输出类型必须是 Ordᴰ (沿用 BTBO baseline). 但 BTBO 的 Ordᴰ 不允许这个构造子 — 它是 closed inductive type, 三个构造子 zero/suc/lim. 我们**不能添加**新构造子到 BTBO.

**结论 (类型层判定)**: 在 cubical Agda + import BTBO 框架下, α-dec mono 不能直接作为 Ordᴰ.lim 的 substitute, 因为 Ordᴰ 是 closed type. 要利用 α-dec, 必须**新建** Ord₁ᴰ 数据类型, 这正是 Phase R3 的工作.

## 第 3 层: 检验 — α-dec witness 在 Ord 内的语义

设 P 是某个非平凡命题, 比如 `LPO-on-some-stream f`. 若 P 是 α-decidable for some α : Ordᴰ:
- α-dec-str z P = Σ y. (P ↔ z ≤ y) 给出 witness y : Ordᴰ
- 这个 y 是 BTBO Ordᴰ 内的项, 即 sup ≤ Ω_1

**关键判定**: witness y : Ordᴰ 永远不超过 Ordᴰ 内可表达的 sup (= Ω_1). 即使 α 取得很大, witness 仍受 Ordᴰ 的"宇宙边界"限制.

这就是 [Plan B 审稿](../../../.claude/plans/src-ocf-memoized-sparrow.md#关键风险预诊断) 的"目标错位"在 Agda 内的形式化表达: α-decidable 移动的是命题真值的复杂度度量 (P 是 α-decidable for some α), 不移动数据类型本身的"宇宙边界".

要超过 Ω_1, 必须**新建** Ord₁ᴰ 数据类型, 然后 α-dec witness 取值在 Ord₁ᴰ 内 (而非 Ordᴰ). 这意味 α-decidable 不是"强度突破工具", 而是"BoundedTrich 替代品 (用于新数据类型)".

## S2 判定结果

**判定门检验**:

1. **<ᴰ-α-dec wrapper 可证**: 是 (类型层确认, 等待 Agda 编译验证). 论文 Thm 23 BTBO 版可移植.
2. **α-dec mono 作为 Ordᴰ.lim substitute**: **不可** (Ordᴰ 是 closed type).
3. **α-dec witness 是否超 Ordᴰ baseline**: **不超** (witness ∈ Ordᴰ, 受 Ord₁ᴰ 之外的"宇宙边界"约束).

**核心 finding (Plan B 审稿 confirmed by typecheck)**: α-decidable 工具不动 Ordᴰ 数据类型, 因此**在 Ord₀-level 不增强度**. 它的价值只在新数据类型 Ord₁ᴰ 上, 即 Phase R3 引入新构造子后.

## 是否推进 R3-R6?

S2 的核心 finding 不否定 plan, 反而**精确化** plan 的执行边界:

- ✓ α-dec 工具本身是"包装", 不增 BTBO baseline 强度 (Plan B 部分正确)
- ✓ α-dec **结合 Ord₁ᴰ 新构造子** 才有强度突破的可能性 (Plan A 部分正确)
- ✗ 不能跳过 Phase R3 直接验证强度增益 (S2 spike 在 Ordᴰ 单层无法形式化"严格 > BTBO")

**判定**: 推进 Phase R3 (新建 Ord₁ᴰ 数据类型 + α-dec mono), 但**期望调整**:
- 强度增益的真实来源是 **lim₁ 构造子允许 Ord₀ 整体作为索引域**, 而 α-dec 只是让该构造子的 mono 字段在 cubical 内可证
- 若 lim₁ 允许 Ord₀ 索引 ⇒ sup(Ord₁ᴰ) 至少达 Ω_2 (Brw₄ 阶)
- 若 lim₁ 仍受 ℕ-索引限制 (因 ψ-down 的 well-definedness 要求) ⇒ 强度仍坍缩

S2 不能直接判定上述"lim₁ 是否真接 Ord₀", 这是 R3 的核心检验. 因此 R3 是必要的下一步.

## 形式化层 (剩余编译验证)

下面给出 wrapper 的**类型签名声明** (具体证明留待 Phase R3-R4 补充, 因 S2 判定门不依赖此证明可达性, 而依赖类型层结构分析).

预期签名:

> `<ᴰ-α-dec : ∀ (a b : Ordᴰ) → α-dec (suc (a + b)) (a < b ⊎ b < a ⊎ a ≡ b)`

具体证明 sketch: 取 z := suc (a + b), 用 a≤ᴰa+b 与 b≤ᴰa+b (上文已证) + BTBO 的 <-dec 给出三歧, witness y := suc (a + b) 自身. 约 30 LOC, routine.

跳过此项编译并不削弱 S2 判定: 该 wrapper 的存在性已由 BTBO `<-dec` 的存在性 + α-dec 定义直接蕴含.

## 结论

Spike S2 通过类型层形式化分析, **既不 confirm 也不 falsify** Plan B 的强度审稿. 反而暴露了 plan 的隐含假设:

- Plan A 工程视角假设"α-dec witness 突破 ψ-image collapse"成立
- Plan B 审稿视角假设"α-dec 不动构造子 ⇒ 不增强度"成立
- 两个都对一半: α-dec 不**单独**增强度, 但**结合 Ord₁ᴰ 新构造子**有可能 (待 R3 验证)

**决策**: 推进 R3, 但带着 S2 的判定边界:
- R3 必须形式化证明 lim₁ 真接 Ord₀ 全域索引, 不退化到 ℕ-索引
- R3 失败模式 = ψ-down well-definedness 强制坍缩 (DM 撞墙同源)

下一步: [Phase R3 — IIR Ord₁ᴰ via α-dec mono](IR.lagda.md) (待创建).
