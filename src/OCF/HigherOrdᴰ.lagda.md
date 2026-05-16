# HigherOrdᴰ: 单一数据类型 OrdH α, transfinite 一般化

> [HigherIter.lagda.md](HigherIter.lagda.md) 用 ℕ-iter 写出 Higher² 至 Higher⁴ 各自独立的 data type. 本模块**合并为单一参数化数据类型** `OrdH (α : Ordᴰ)`, 通过递归在 α 上定义 ψⁿ-at, 实现 transfinite 迭代.
>
> 设计要点: 让 ψᴰ-at α 通过递归 α 的结构选择"前级 ψⁿ":
> - α = zero: ψⁿ-at zero = ψⁿ (BTBO 基底)
> - α = suc α': ψⁿ-at (suc α') 基于 OrdH α' 的 collapse
> - α = lim f: 对角线 ψⁿ-at (f n) n
>
> **强度估算 (Explore agent)**: Higher^α 对应 ψ(Ω_(Ω+α))-ish. α = Ω-as-Ordᴰ 给出 ψ(Ω_(Ω·2)) — **大举提升**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.HigherOrdᴰ where

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
