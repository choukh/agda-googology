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

## Phase 2 待办清单

按 [FINDINGS.md §7](FINDINGS.md) 的路线:

1. **`Sub (mahlo f a b)`** 填非平凡定义. Takahashi paper §2.1 的 reflection rule 给出"`q f a b` 是一个 sub-universe 的 code, `T_𝕄 (q f a b)` 是该 sub-universe 的元素". 移植到 Brouwer 上下文.
2. **`_<ᴹ_` 互递归**. 既要在 `Ordᴹ` 上定义 `<`, 又要在 `Opᴹ` 上 (跨 mahlo 节点的比较). 互递归 data 至少 4 层 (Ordᴹ, Opᴹ, <ᴹ, <ᴼ).
3. **Mono 条件**. 当前 `lim`/`mahlo` 不带 mono. 仿 BTBO 加 mono 后, 互递归扩张为 6 层 (再加 monoᴺ, monoSub).
4. **Bounded trichotomy**. 是 Phase 3 的预期最大墙. 函数外延性在 mahlo 节点比较时再次浮现 (类比 [../Naive/Phase1.lagda.md](../Naive/Phase1.lagda.md) 的 +-lmono 不真).
5. **ψ_M collapser**. 类比 [Higher.agda:31-38](../../Higher.agda#L31-L38) 的 `ψ<Ω` 写法.

工作量估算: 2 通过, 3 中等, 4 不一定通, 5 看 4 结果.

## 与已有模块的关系

- [BTBO.lagda.md](../../BTBO.lagda.md): 提供 `Ordᴰ`, `Ord`, `cumsum`, ψ-框架. Phase 4-5 阶段 ψ_M 与 `ord-M : Ord₀ → Ordᴹ`-style 嵌入需要用到.
- [Higher.agda](../../Higher.agda): `OrdΩ.limₙ` 的 `<ᴺ-dec` 折叠模板可类比为 `<ᴹ-dec` 的折叠目标.
- [../Naive/Phase1.lagda.md](../Naive/Phase1.lagda.md): 多层互递归 + 三歧性的工作模板.
