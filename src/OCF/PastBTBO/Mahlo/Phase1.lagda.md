# Mahlo Phase 1 基础: Brouwer-MLQ 骨架

> 本文件是 Mahlo 探索的**工作基底**, 供 Phase 2 直接构建. 历史失败变体 (V1/V3/V3'/V4 等 naive 写法) 与全部诊断推理见 [FINDINGS.md](FINDINGS.md).
>
> 核心结论 (来自 Takahashi 2024 [arxiv 2402.15074](https://arxiv.org/abs/2402.15074)): IR-Mahlo 在 Agda 中不能用 Setzer 教科书直译 (positivity 拒), 但用**互递归两层 universe** (𝕄 + ℚ 互递归, "Ordᴹ → Ordᴹ" 改走 "Ordᴹ ↔ Opᴹ" 路径) 可行. 此文件给 Brouwer 化版.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
```

## Brouwer-MLQ 互递归骨架

`Ordᴹ` 是 Brouwer 风格的 Mahlo 序数, `Opᴹ` 代理"`Ordᴹ` 上的算子" (MLQ 中的 ℚ). `Sub` 是 size decoder (每个节点对应的 sub-universe 元素集合). 关键: mahlo 构造子接收一个 `Opᴹ` (不是 `Ordᴹ → Ordᴹ`), 绕开 strict positivity.

```agda
mutual
  data Ordᴹ : Set
  data Opᴹ  : Set
  Sub : Ordᴹ → Set

  data Ordᴹ where
    zero  : Ordᴹ
    suc   : Ordᴹ → Ordᴹ
    lim   : (ℕ → Ordᴹ) → Ordᴹ
    mahlo : Opᴹ → (a : Ordᴹ) → (Sub a → Ordᴹ) → Ordᴹ

  data Opᴹ where
    op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

  Sub zero            = ⊥
  Sub (suc _)         = ⊤
  Sub (lim _)         = ℕ
  Sub (mahlo _ _ _)   = ⊤   -- Phase 2 占位; 真正的 sub-universe reflection 见 Takahashi §2.1
```

通过 Agda 2.8.0 + `--safe --without-K --cubical-compatible` 编译.

## Phase 2 / 3 / 4 实测结果

Phase 工作文件 + 实施日志:
- Phase 2: [Phase2.lagda.md](Phase2.lagda.md) + [FINDINGS_Phase2.md](FINDINGS_Phase2.md)
- Phase 3: [Phase3.lagda.md](Phase3.lagda.md) + [FINDINGS_Phase3.md](FINDINGS_Phase3.md)
- Phase 4: [Phase4.lagda.md](Phase4.lagda.md) + [FINDINGS_Phase4.md](FINDINGS_Phase4.md)

| Step | Phase 2 | Phase 3 | Phase 4 | 备注 |
|------|---------|---------|---------|------|
| 1. `Sub (mahlo …)` Σ-closure | ✓ | ✓ | ✓ | Setzer 反射 Brouwer 化 |
| 2. `_<ᴹ_` + `_<ᴼ_` 互递归 | ✓ | ✓ | ✓ | `<ᴹ-trans` 5 case |
| 3. monoSub 字段 | — | ✓ | ✓ | Phase 3 引入, Phase 4 保留 |
| 4. `_<ˢ_` 内禀序 + `<ˢ-dec` | — | ✓ | ✓ | IR 函数版 + lex 序 |
| 5. strat 字段 `∀ s → a <ᴹ b s` | — | ✓ | **去** | Phase 4 去掉, 接受 partial trichotomy |
| 6. Bounded trichotomy `<ᴹ-dec` | partial 1/4 | **full 4/4** | partial 2/4 | Phase 3 用 strat 换 full, Phase 4 退回 partial |
| 7. `level : Ordᴹ → Ordᴰ` | — | — | ✓ (新) | mahlo +1 rank, lim cumsum |
| 8. ψ_M collapser | ✗ skip | ⏸ TODO | ✓ v1+v2 | Phase 4 编译, ψ_M : Ordᴹ → Ord₀ |
| **强度量级** | (无) | ≲ Higher.agda | **≲ Higher.agda** | 未超过 |

**累积负面结论 (Phase 4 §6 诚实记账)**: Mahlo 路径 4 个 Phase ~550 LOC, 强度上限 ≲ Higher.agda 的 50 行. Phase 5 三路径并行 spike 探索.

## Phase 5 三路径 spike 实测结果

工作文件: [Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md), [Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md), [Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md). 实施日志: [FINDINGS_Phase5.md](FINDINGS_Phase5.md).

| 路径 | spike LOC | 编译 | 强度 binding | 核心目标 |
|------|-----------|------|--------------|----------|
| **A: Sub 升级 Ord-indexed** | 85 | ✓ | 仅 sample 构造, 无 ψ_M | 结构通, ψ_M 留 Phase 6 |
| **B: Higher² 迭代** | 60 | ✓ | `lim (n → ψ₀ (ψ<Ω² {n} ΩΩ²))` 顶级 binding | **✓ 严格超过 Higher.agda** |
| **C: Opᴹ 语义化 v0** | 120 | ✓ (内联绕过) | ⟦_⟧ 独立可用, ψ_M-C 退化 | **✗ Agda 终止检查拒绝直接用 ⟦_⟧** |

**Phase 6 推荐**: **走 Path B (Higher^n / Higher^ω 完整迭代)** — 仅 60 LOC spike 已达成超过 Higher.agda, 进一步迭代到 Higher^ω 预计 200-300 LOC 触达 ψ(Ω_(Ω+ω)). 详 [FINDINGS_Phase5.md §5](FINDINGS_Phase5.md#5-phase-6-主线推荐).

**Mahlo 路径定性结论**: 在 Agda `--safe --without-K` 下结构性受限, 无法在合理工程量下超过 Higher.agda. 其价值在结构性贡献 (IR-Mahlo MLQ 编码, `<ˢ`, monoSub, level rank, ⟦_⟧ post-mutual), 不在 ordinal 强度.

## 与已有模块的关系

- [BTBO.lagda.md](../../BTBO.lagda.md): 提供 `Ordᴰ`, `Ord`, `cumsum`, ψ-框架. Phase 4-5 阶段 ψ_M 与 `ord-M : Ord₀ → Ordᴹ`-style 嵌入需要用到.
- [Higher.agda](../../Higher.agda): `OrdΩ.limₙ` 的 `<ᴺ-dec` 折叠模板可类比为 `<ᴹ-dec` 的折叠目标.
- [../Naive/Phase1.lagda.md](../Naive/Phase1.lagda.md): 多层互递归 + 三歧性的工作模板.
