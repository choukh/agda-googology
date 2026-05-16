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

## Phase 2 实测结果

Phase 2 工作文件: [Phase2.lagda.md](Phase2.lagda.md). 实施日志: [FINDINGS_Phase2.md](FINDINGS_Phase2.md).

| Step | 状态 | 结论 |
|------|------|------|
| 1. `Sub (mahlo …)` Σ-closure | ✓ | `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)`. Setzer 反射的 Brouwer 化. |
| 2. `_<ᴹ_` + `_<ᴼ_` 互递归 | ✓ | `<ᴹ` 跨 mahlo 两进路 (mahlo-a / mahlo-b); `<ᴼ` 仅 op-c 头比较. `<ᴹ-trans` 通过. |
| 3. mono on lim | ✓ (部分) | `lim` 带 `monoᴺ`. **mahlo 未带 monoSub** — `Sub a` 内禀序构造循环依赖, Phase 3 todo. |
| 4. Bounded trichotomy | ⚠️ partial | non-mahlo case 全通; mahlo 4 子 case 中 1 通 (mahlo-a × mahlo-a), 3 blocked. 退回 `Maybe`-wrapped. **与 Naive `+-lmono` 死墙结构同构**. |
| 5. ψ_M collapser | ✗ skip | Step 4 partial → collapser 在 mahlo 输入上不可定. |

详细诊断见 [FINDINGS_Phase2.md](FINDINGS_Phase2.md). 修复路径: Phase 3 需在 `Sub a` 上加内禀序 + 在 mahlo 加 monoSub, 这是 Takahashi 2024 未做的扩展.

## 与已有模块的关系

- [BTBO.lagda.md](../../BTBO.lagda.md): 提供 `Ordᴰ`, `Ord`, `cumsum`, ψ-框架. Phase 4-5 阶段 ψ_M 与 `ord-M : Ord₀ → Ordᴹ`-style 嵌入需要用到.
- [Higher.agda](../../Higher.agda): `OrdΩ.limₙ` 的 `<ᴺ-dec` 折叠模板可类比为 `<ᴹ-dec` 的折叠目标.
- [../Naive/Phase1.lagda.md](../Naive/Phase1.lagda.md): 多层互递归 + 三歧性的工作模板.
