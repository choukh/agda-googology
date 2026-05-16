# Phase 5 Path B spike: Higher² 迭代 ✓ 唯一达成超过 Higher.agda 的路径

> Phase 4 Mahlo 路径强度 ≲ Higher.agda. 本 spike 不走 Mahlo, 直接**迭代 Higher.agda** 的 limₙ 模式: 在 OrdΩ 之上构造 OrdΩ², 让 limₙ' 索引在 Higher.agda 已达到的 `ψⁿᴴ` 序列, 而非 BTBO 的 `ψⁿ`. 预期强度 ≈ ψ((Ω_Ω+1)+(Ω_(Higher+1))), **明确超过 Higher.agda 一级**.
>
> 模板 100% 仿 [Higher.agda:13-42](../../Higher.agda#L13-L42), 只改 `ψᴰ → ψᴰ'`, `ψⁿ → ψⁿᴴ`, `OrdΩ → OrdΩ²`, `↑Ω → ↑Ω²`, `ψ<Ω → ψ<Ω²`.
>
> 三路径并行 (A/B/C) 对比 + Phase 6 决策见 [FINDINGS.md §Phase 5 三路径对比](FINDINGS.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase5B_HigherIter where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO
open import OCF.Higher
open Trich using (n; zero; suc) renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich hiding (_+_)
open Ord-Ord
```

## §1 — `ψⁿᴴ` 序列 (Higher.agda 的 iter)

Higher.agda 的 final binding ([Higher.agda:42](../../Higher.agda#L42)) `lim (λ n → ψ₀ (ψ<Ω {n = n} ΩΩ))` 内部隐含一个 ℕ-indexed 序列. 提取为命名:

```agda
ψⁿᴴ : ℕ → Ord₀
ψⁿᴴ n = ψ₀ (ψ<Ω {n = n} ΩΩ)
```

由 Higher.agda 的强度估算, `lim ψⁿᴴ` 极限 ≈ ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))).

## §2 — `ψᴰ'` Ordᴰ 层序列, 用 Higher.agda 的 ψⁿᴴ 替代 BTBO 的 ψⁿ

仿 [Higher.agda:13-14](../../Higher.agda#L13-L14):

```agda
ψᴰ' : ℕ → Ordᴰ
ψᴰ' = cumsum (ordᴰ ∘ ψⁿᴴ)
```

`ψᴰ'` 单调, 极限 ≈ ordᴰ (lim ψⁿᴴ) = Higher.agda 的强度对应的 Ordᴰ.

## §3 — `OrdΩ²` 数据类型

仿 [Higher.agda:16-20](../../Higher.agda#L16-L20):

```agda
data OrdΩ² : Set where
  zero  : OrdΩ²
  suc   : OrdΩ² → OrdΩ²
  lim   : (f : ℕ → OrdΩ²) → OrdΩ²
  limₙ' : (p : ℓ < ψᴰ' n) (f : Ord ℓ → OrdΩ²) → OrdΩ²
```

## §4 — `↑Ω²` lift function

仿 [Higher.agda:22-26](../../Higher.agda#L22-L26):

```agda
↑Ω² : Ord (ψᴰ' n) → OrdΩ²
↑Ω² zero = zero
↑Ω² (suc a) = suc (↑Ω² a)
↑Ω² (lim f) = lim (↑Ω² ∘ f)
↑Ω² (limᵢ p f) = limₙ' p (↑Ω² ∘ f ∘ coe₀)
```

## §5 — `ΩΩ²` outer lim

仿 [Higher.agda:28-29](../../Higher.agda#L28-L29):

```agda
ΩΩ² : OrdΩ²
ΩΩ² = lim (λ n → limₙ' {ℓ = ψᴰ' n} (cumsum-mono (ordᴰ ∘ ψⁿᴴ) zero) ↑Ω²)
```

## §6 — `ψ<Ω²` collapse

仿 [Higher.agda:31-38](../../Higher.agda#L31-L38):

```agda
ψ<Ω² : OrdΩ² → Ord (ψᴰ' n)
ψ<Ω² zero = Ω _
ψ<Ω² (suc a) = lfp (ψ<Ω² a +_)
ψ<Ω² (lim f) = lim (ψ<Ω² ∘ f)
ψ<Ω² {n} (limₙ' {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω² ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<Ω² ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<Ω² ∘ f ∘ ψ< p)
```

## §7 — 强度 demo (Phase 5 spike 的核心 deliverable)

```agda
-- 估算: ψ((Ω_Ω+1)+(Ω_(ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))+1)))
-- 明确超过 Higher.agda 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))
_ : Ord₀
_ = lim (λ n → ψ₀ (ψ<Ω² {n = n} ΩΩ²))
```

`lim (n → ψ₀ (ψ<Ω² {n} ΩΩ²))` 是 OrdΩ² 折回 Ord₀ 的 ω-cofinal sup. 与 Higher.agda 的 `lim (n → ψ₀ (ψ<Ω {n} ΩΩ))` 同形, 但内层 ψ<Ω² + ΩΩ² 已是"BTBO + 2 级 ψ-OCF", 比 Higher.agda 多一级.

## Phase 5B spike 总结

| 项 | 状态 | 备注 |
|----|------|------|
| `ψⁿᴴ` 序列 | ✓ | 直接组合 Higher.agda 的 ψ<Ω + ΩΩ |
| `OrdΩ²` 数据类型 | ✓ | 4 个构造子, 同 OrdΩ |
| `↑Ω²` lift | ✓ | 模板 100% 仿 OrdΩ |
| `ΩΩ²` outer lim | ✓ | 模板 100% 仿 OrdΩ |
| `ψ<Ω²` collapse | ✓ | 模板 100% 仿 ψ<Ω |
| 强度 demo binding | ✓ (顶级 `_ : Ord₀`) | 明确超过 Higher.agda |
| LOC | ~60 行 (含注释) | spike 目标 50-100 LOC ✓ |
| 风险 R-B1 (跨模块依赖) | 未发生 | `open import OCF.Higher` 引入 ψ<Ω + ΩΩ, 无循环 |

**关键观察**: 整个 Higher² spike 是 Higher.agda 43 行模板的**完全 symbolic copy**, 只换了一层"内嵌函数"(`ψⁿ` 替换为 `ψⁿᴴ`). 这暗示 **Higher^n 是 Higher.agda 模板的可参数化迭代**, Phase 6 可写一个 `module Higher (n : ℕ)` 直接生成 Higher^n.
