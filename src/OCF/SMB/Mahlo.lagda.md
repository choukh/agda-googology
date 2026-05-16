# SMB Mahlo Probe: smax 能否解锁 Mahlo `<ᴹ-dec` 跨家族 (诊断报告)

> **目的**: 检验 [SMB/Core](Core.lagda.md) 的 `indMax` 思想能否在 Mahlo 数据类型上定义 `smaxᴹ`, 进而解锁 [PastBTBO/Mahlo/Phase2](../PastBTBO/Mahlo/Phase2.lagda.md) 撞过的"跨函数家族"障碍.
>
> **结论 (剧透)**: ❌ 失败. SMB 的 indMax 依赖**结构性归纳**, 而 Mahlo 的 `b : Sub a → Ordᴹ` 是**任意函数**, 无结构性递降.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.SMB.Mahlo where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.SMB.Core using (Tree; Z; ↑; Lim; indMax)
```

## §1 — Mahlo 障碍重温

[Mahlo Phase 2](../PastBTBO/Mahlo/Phase2.lagda.md) 定义:

    data Ordᴹ where
      zero  : Ordᴹ
      suc   : Ordᴹ → Ordᴹ
      lim   : (f : ℕ → Ordᴹ) → monoᴺ f → Ordᴹ
      mahlo : Opᴹ → (a : Ordᴹ) → (Sub a → Ordᴹ) → Ordᴹ

    data _<ᴹ_ where
      ...
      mahlo-a : ∀ {f a b x} → x <ᴹ a → x <ᴹ mahlo f a b
      mahlo-b : ∀ {f a b x} → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b

`<ᴹ-dec` 在 `(mahlo-b s, mahlo-b s')` 情形撞墙: `b s : Ordᴹ` 与 `b s' : Ordᴹ` 是函数 `b : Sub a → Ordᴹ` 在两不同输入下的输出, **跨函数像无序**.

## §2 — SMB indMax 模板在 Ordᴹ 上的尝试

仿 [SMB/Core indMax](Core.lagda.md#§3):

    smaxᴹ : Ordᴹ → Ordᴹ → Ordᴹ
    smaxᴹ zero       b           = b
    smaxᴹ (suc a)    zero        = suc a
    smaxᴹ (suc a)    (suc b)     = suc (smaxᴹ a b)
    smaxᴹ (suc a)    (lim g mg)  = ?   -- 需要 mono on Ordᴹ-lim, 类比 BTBO 问题
    smaxᴹ (lim f mf) b           = ?
    smaxᴹ (mahlo f a b) c        = ?   -- 关键 case
    smaxᴹ c         (mahlo f a b)= ?

**关键问题**: `smaxᴹ (mahlo _ a₁ b₁) (mahlo _ a₂ b₂)` 怎么定义?

需要构造一个 dominate 两 mahlo 的 Ordᴹ. mahlo 的 "宽度"由 `b : Sub a → Ordᴹ` 提供 — 对每个 `s : Sub a`, `b s` 是一个 Ordᴹ.

要 dominate `mahlo _ a₁ b₁`, 必须 dominate 所有 `b₁ s` (∀ s : Sub a₁). 这相当于 dominate 一个**任意函数的整个像集**.

### 2.1 试图组合 mahlo

    smaxᴹ (mahlo f₁ a₁ b₁) (mahlo f₂ a₂ b₂) = mahlo ? (smaxᴹ a₁ a₂) λ s → smaxᴹ (b₁ ?) (b₂ ?)

这要求把 `s : Sub (smaxᴹ a₁ a₂)` 映射到合适的 `(s₁ : Sub a₁) × (s₂ : Sub a₂)`. 但 `Sub (smaxᴹ a₁ a₂)` 的结构取决于 `smaxᴹ a₁ a₂` — 而该值本身依赖 `smaxᴹ`. 互递归循环.

更深的问题: 即便能构造 `s ↦ (s₁, s₂)`, 要求该映射对所有 s 给出合理 `(s₁, s₂)`. **无法用纯函数构造**, 需要 ad hoc 决策, 等价于跨家族决策.

### 2.2 试图 lim 嵌入

    smaxᴹ (mahlo f₁ a₁ b₁) (mahlo f₂ a₂ b₂) = lim seq seq-mono

`lim` 需要 ℕ-monotone 序列. 把 mahlo 的宽度 `Sub a` 嵌入 ℕ 需要 `Sub a → ℕ` 满射 — 但 `Sub a` 通常是 Σ 类型, 不一定可数. 即便可数, 嵌入降维 (强度损失).

### 2.3 试图 mahlo 中嵌

`mahlo f a b` 的 "max with another mahlo" 自然想法: 取 `b' = λ s → smaxᴹ (b s) <other>`. 但**这只是对每个 s 算 max, 没有把整个 b₁ 与 b₂ 真正合并**.

## §3 — SMB 失败的本质原因

| 角度 | BTBO `Ordᴰ` | Mahlo `Ordᴹ` |
|------|------------|-------------|
| 宽度构造子 | `lim : (f : ℕ → Ordᴰ) → monotonicᴺ f → Ordᴰ` | `mahlo : Opᴹ → (a : Ordᴹ) → (Sub a → Ordᴹ) → Ordᴹ` |
| 宽度索引类型 | `ℕ` (可数 + 全序) | `Sub a` (Σ-递归, 一般无序) |
| 索引 trich | `<ᴺ-dec`: 无条件 | 无 — `s, s' : Sub a` 无原生 < |
| indMax 可定义? | 可 (Eremondi 论文) | **不可** — Sub a 非结构性递降 |
| BoundedTrich 在该层 | ✓ (mono 给定 lim/lim) | ✗ (b: Sub→Ordᴹ 跨像无序) |

**核心命题**: SMB-trees 的 indMax 依赖**所有限子序列源于结构上更小的子树**. Mahlo 的 `b : Sub a → Ordᴹ` 是**外部传入的函数**, 它的输出不是 Ordᴹ 的结构子项. 因此**indMax-pattern 无法递归通过 b**.

```agda
-- 占位 demo: SMB 工具集**不**能直接给出 smaxᴹ
-- (本文件不定义 smaxᴹ, 仅诊断)

postulate-impossible : Set
postulate-impossible = ⊤   -- 标记: SMB 在 Mahlo 不可用

_ : postulate-impossible
_ = tt
```

## §4 — 与 Naive 障碍的对比

| 路径 | 障碍本质 | SMB 是否解 |
|------|---------|---------|
| **Naive** `<-1-dec` limΩ/limΩ | Ordᴰ 上 `+-lmono` 不真 → 构造不出 strict 共同上界 | ❌ (见 [Naive.lagda.md](Naive.lagda.md)) — SMB 在 Tree 上有 bound, 但桥接回 Ordᴰ 需 +-lmono 退化 |
| **Mahlo** `<ᴹ-dec` mahlo-b/mahlo-b | `b : Sub a → Ordᴹ` 跨函数像无原生序 | ❌ — SMB indMax 需结构性递归, b 不是结构子项 |

两者**结构上不同**, 但都不被 SMB 解锁:
- Naive: 算律问题, 但 SMB 给出的算律 (indMax) 不能跨 BTBO ↔ Tree 桥接
- Mahlo: 决策性问题, SMB 的 indMax 模板本就不适用于任意函数家族

## §5 — Phase B-2 总结

- ✅ 诊断完成: SMB 不能在 Mahlo 上定义 smaxᴹ
- ✅ 验证 [ROADMAP §3.3](../ROADMAP.md) 的预测: Mahlo 障碍是 Brouwer-tree-paradigm 的天花板
- 📊 强度增益: **0** — Mahlo `<ᴹ-dec` 仍然撞墙 (与 Phase 1-5 Mahlo 770 LOC 结论一致)
- 💡 真正洞察: SMB-trees 解决的是**Tree 内部**的算律, 不解 Tree 之外的 OCF 反射性问题

后续路线: 见 [FINDINGS.md](FINDINGS.md).
