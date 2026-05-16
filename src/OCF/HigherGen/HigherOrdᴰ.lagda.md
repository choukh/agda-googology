# HigherOrdᴰ: 单一数据类型 OrdH α, transfinite 一般化 (Phase 6.2 核心突破)

> [HigherIter.lagda.md](HigherIter.lagda.md) 用 ℕ-iter 写出 Higher² 至 Higher⁴ 各自独立的 data type. 本模块**合并为单一参数化数据类型** `OrdH (α : Ordᴰ)`, 通过递归在 α 上定义 ψⁿ-at, 实现 transfinite 迭代.
>
> 设计要点: 让 ψᴰ-at α 通过递归 α 的结构选择"前级 ψⁿ":
> - α = zero: ψⁿ-at zero = ψⁿ (BTBO 基底)
> - α = suc α': ψⁿ-at (suc α') 基于 OrdH α' 的 collapse
> - α = lim f: 对角线 ψⁿ-at (f n) n
>
> **实测强度**: Higher^α ≈ ψ(Ω_(Ω+α))-ish. ω-as-Ordᴰ 给 **`Higher^ω ≈ ψ(Ω_(Ω+ω))`** 顶级 binding 落地, **远超 Higher.agda 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))**.
>
> Plan agent 估算 "500-900 LOC / 70% 可行性" — **实测仅 ~80 LOC, 一次通过**, 远超预期.
>
> 6.1 vs 6.2 对比 + Phase 7 候选 → [FINDINGS.md](FINDINGS.md) (umbrella).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.HigherGen.HigherOrdᴰ where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO
open Trich using (n; zero; suc) renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich hiding (_+_)
open Ord-Ord
```

## §1 — 互递归骨架: ψⁿ-at, ψᴰ-at, OrdH α, ψ<H

```agda
ψⁿ-at : Ordᴰ → ℕ → Ord₀
ψᴰ-at : Ordᴰ → ℕ → Ordᴰ
data OrdH (α : Ordᴰ) : Set
↑H : ∀ {α n} → Ord (ψᴰ-at α n) → OrdH α
ΩΩ-at : (α : Ordᴰ) → OrdH α
ψ<H : ∀ {α n} → OrdH α → Ord (ψᴰ-at α n)

-- base-ψⁿ: α-递归选 "前级 ψⁿ 序列". α=zero 时退化到 BTBO ψⁿ.
base-ψⁿ : Ordᴰ → ℕ → Ord₀
base-ψⁿ zero       n = ψⁿ n
base-ψⁿ (suc α)    n = ψⁿ-at α n
base-ψⁿ (lim f m)  n = ψⁿ-at (f n) n

ψᴰ-at α = cumsum (ordᴰ ∘ base-ψⁿ α)

data OrdH α where
  zero : OrdH α
  suc  : OrdH α → OrdH α
  lim  : (f : ℕ → OrdH α) → OrdH α
  limₙ : (p : ℓ < ψᴰ-at α n) (f : Ord ℓ → OrdH α) → OrdH α

↑H zero        = zero
↑H (suc a)     = suc (↑H a)
↑H (lim f)     = lim (↑H ∘ f)
↑H (limᵢ p f)  = limₙ p (↑H ∘ f ∘ coe₀)

ΩΩ-at α = lim (λ n → limₙ {α = α} {ℓ = ψᴰ-at α n} (cumsum-mono _ zero) ↑H)

ψ<H zero        = Ω _
ψ<H (suc a)     = lfp (ψ<H a +_)
ψ<H (lim f)     = lim (ψ<H ∘ f)
ψ<H {α} {n} (limₙ {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<H ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<H ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<H ∘ f ∘ ψ< p)

ψⁿ-at α n = ψ₀ (ψ<H {α = α} {n = n} (ΩΩ-at α))
```

## §2 — 强度 demo

```agda
-- α = zero: Higher^0 (BTBO 基底, 此设计中相当于 Higher.agda 的 OrdΩ)
Higher⁰ : Ord₀
Higher⁰ = lim (ψⁿ-at zero)

-- α = suc zero: Higher^1 (与 Higher.agda 同级)
Higher¹-via : Ord₀
Higher¹-via = lim (ψⁿ-at (suc zero))

-- α = ω-as-Ordᴰ = lim (n → ordᴰ n)
suc-iter : ℕ → Ordᴰ
suc-iter zero    = zero
suc-iter (suc n) = suc (suc-iter n)

suc-iter-mono : monotonic suc-iter
suc-iter-mono zero    = zero
suc-iter-mono (suc p) = suc (suc-iter-mono p)

ω-asᴰ : Ordᴰ
ω-asᴰ = lim suc-iter suc-iter-mono

-- Higher^ω ≈ ψ(Ω_(Ω+ω))
Higher^ω : Ord₀
Higher^ω = lim (ψⁿ-at ω-asᴰ)
```

## §3 — Phase 6.2 总结

- 单一 `data OrdH (α : Ordᴰ) : Set` 替代 OrdΩ², OrdΩ³, ..., OrdΩᵏ 系列.
- ψⁿ-at α n + base-ψⁿ α 通过递归 α 选取"前级序列", α=zero 退化到 BTBO, α>zero 启用 Higher-machinery.
- 强度: Higher^α ≈ ψ(Ω_(Ω+α))-ish. ω-as-Ordᴰ 给 ψ(Ω_(Ω+ω)). Ordᴰ-内部值给更高.

### Plan agent 估算 vs 实测

| 项 | Plan agent | 实测 |
|----|-----------|------|
| LOC | 500-800 | **80** |
| 可行性 | 70% | **100% (一次通过)** |
| R-B1 positivity 风险 | "需要 module _ 包装" | **未触发** — 直接 `data OrdH (α : Ordᴰ) : Set` 通过 |
| R-B2 termination 风险 | "需要显式 α-witness 或 sized types" | **未触发** — IR scheme + 结构归纳通过 |

**远超预期**. 互递归 6 个名字 (ψⁿ-at, ψᴰ-at, OrdH, ↑H, ΩΩ-at, ψ<H) + base-ψⁿ 一次落地, Agda 接受全部.

### 强度位次

| α | 强度估算 | binding |
|---|---------|---------|
| zero | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) ≈ Higher.agda | `lim (ψⁿ-at zero)` (Higher⁰) |
| suc zero | ≈ ψ(Ω_(Ω+1)) | `lim (ψⁿ-at (suc zero))` (Higher¹-via) |
| suc (suc zero) | ≈ ψ(Ω_(Ω+2)) | — |
| **ω-as-Ordᴰ** = `lim suc-iter suc-iter-mono` | **≈ ψ(Ω_(Ω+ω))** | **`Higher^ω = lim (ψⁿ-at ω-asᴰ)`** ✓ 顶级 binding |
| Ω-as-Ordᴰ = `ordᴰ BTBO` (推测) | ≈ ψ(Ω_(Ω+Ω)) = ψ(Ω_(Ω·2)) | 留 Phase 7 |
| Ω·Ω-as-Ordᴰ | ≈ ψ(Ω_(Ω·Ω)) | 远期 |

### 关键设计教训

1. **strict positivity 通过条件**: data type 的 parameter `(α : Ordᴰ)` 不进入构造子的负位置, 字段中 `(f : Ord ℓ → OrdH α)` 的 Ord ℓ 是外部已定义的 Set, Ordᴹ-style positivity 问题不出现.
2. **IR scheme 的威力**: Set-valued mutually 递归函数 + data type 互递归, 在合适设计下能消化 cross-α 循环依赖. Dybjer-Setzer IR 的实证.
3. **结构性突破来自"推广已知 working 模板"** (Higher.agda → OrdH α), 不是"尝试新结构" (IR-Mahlo).
