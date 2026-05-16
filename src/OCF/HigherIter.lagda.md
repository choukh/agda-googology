# Higher Iteration: Higher^k 至 ψ(Ω_(Ω+k))

> [Higher.agda](Higher.agda) 用 `limₙ` + `ψ<Ω` 把 BTBO 推到 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))). 本模块**机械迭代** Higher.agda 模板, 每层提供下一层的 `ψⁿ` 序列. Higher^k 估算强度 ψ(Ω_(Ω+k))-ish, 远超 Higher.agda 单层.
>
> 模板 100% 仿 Higher.agda. 每层符号化拷贝 (替换 `ψᴰ → ψᴰᵏ`, `OrdΩ → OrdΩᵏ`, `↑Ω → ↑Ωᵏ`, `ΩΩ → ΩΩᵏ`, `ψ<Ω → ψ<Ωᵏ`). 4 层 (Higher² 至 Higher⁴) 已足以远超 Higher.agda. ω 层透过 Phase 6.2 `OrdH α` 实现.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.HigherIter where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO
open import OCF.Higher
open Trich using (n; zero; suc) renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich hiding (_+_)
open Ord-Ord
```

## Layer 1: 提取 Higher.agda 的 ψⁿᴴ¹

```agda
ψⁿᴴ¹ : ℕ → Ord₀
ψⁿᴴ¹ n = ψ₀ (ψ<Ω {n = n} ΩΩ)
```

`lim ψⁿᴴ¹` ≈ Higher.agda 强度 ≈ ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))).

## Layer 2: OrdΩ², ψ<Ω², ψⁿᴴ²

```agda
ψᴰ² : ℕ → Ordᴰ
ψᴰ² = cumsum (ordᴰ ∘ ψⁿᴴ¹)

data OrdΩ² : Set where
  zero  : OrdΩ²
  suc   : OrdΩ² → OrdΩ²
  lim   : (f : ℕ → OrdΩ²) → OrdΩ²
  limₙ² : (p : ℓ < ψᴰ² n) (f : Ord ℓ → OrdΩ²) → OrdΩ²

↑Ω² : Ord (ψᴰ² n) → OrdΩ²
↑Ω² zero = zero
↑Ω² (suc a) = suc (↑Ω² a)
↑Ω² (lim f) = lim (↑Ω² ∘ f)
↑Ω² (limᵢ p f) = limₙ² p (↑Ω² ∘ f ∘ coe₀)

ΩΩ² : OrdΩ²
ΩΩ² = lim (λ n → limₙ² {ℓ = ψᴰ² n} (cumsum-mono (ordᴰ ∘ ψⁿᴴ¹) zero) ↑Ω²)

ψ<Ω² : OrdΩ² → Ord (ψᴰ² n)
ψ<Ω² zero = Ω _
ψ<Ω² (suc a) = lfp (ψ<Ω² a +_)
ψ<Ω² (lim f) = lim (ψ<Ω² ∘ f)
ψ<Ω² {n} (limₙ² {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω² ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<Ω² ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<Ω² ∘ f ∘ ψ< p)

ψⁿᴴ² : ℕ → Ord₀
ψⁿᴴ² n = ψ₀ (ψ<Ω² {n = n} ΩΩ²)
```

`lim ψⁿᴴ²` ≈ ψ(Ω_(Ω+2))-ish.

## Layer 3: OrdΩ³, ψ<Ω³, ψⁿᴴ³

```agda
ψᴰ³ : ℕ → Ordᴰ
ψᴰ³ = cumsum (ordᴰ ∘ ψⁿᴴ²)

data OrdΩ³ : Set where
  zero  : OrdΩ³
  suc   : OrdΩ³ → OrdΩ³
  lim   : (f : ℕ → OrdΩ³) → OrdΩ³
  limₙ³ : (p : ℓ < ψᴰ³ n) (f : Ord ℓ → OrdΩ³) → OrdΩ³

↑Ω³ : Ord (ψᴰ³ n) → OrdΩ³
↑Ω³ zero = zero
↑Ω³ (suc a) = suc (↑Ω³ a)
↑Ω³ (lim f) = lim (↑Ω³ ∘ f)
↑Ω³ (limᵢ p f) = limₙ³ p (↑Ω³ ∘ f ∘ coe₀)

ΩΩ³ : OrdΩ³
ΩΩ³ = lim (λ n → limₙ³ {ℓ = ψᴰ³ n} (cumsum-mono (ordᴰ ∘ ψⁿᴴ²) zero) ↑Ω³)

ψ<Ω³ : OrdΩ³ → Ord (ψᴰ³ n)
ψ<Ω³ zero = Ω _
ψ<Ω³ (suc a) = lfp (ψ<Ω³ a +_)
ψ<Ω³ (lim f) = lim (ψ<Ω³ ∘ f)
ψ<Ω³ {n} (limₙ³ {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω³ ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<Ω³ ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<Ω³ ∘ f ∘ ψ< p)

ψⁿᴴ³ : ℕ → Ord₀
ψⁿᴴ³ n = ψ₀ (ψ<Ω³ {n = n} ΩΩ³)
```

## Layer 4: OrdΩ⁴, ψ<Ω⁴, ψⁿᴴ⁴

```agda
ψᴰ⁴ : ℕ → Ordᴰ
ψᴰ⁴ = cumsum (ordᴰ ∘ ψⁿᴴ³)

data OrdΩ⁴ : Set where
  zero  : OrdΩ⁴
  suc   : OrdΩ⁴ → OrdΩ⁴
  lim   : (f : ℕ → OrdΩ⁴) → OrdΩ⁴
  limₙ⁴ : (p : ℓ < ψᴰ⁴ n) (f : Ord ℓ → OrdΩ⁴) → OrdΩ⁴

↑Ω⁴ : Ord (ψᴰ⁴ n) → OrdΩ⁴
↑Ω⁴ zero = zero
↑Ω⁴ (suc a) = suc (↑Ω⁴ a)
↑Ω⁴ (lim f) = lim (↑Ω⁴ ∘ f)
↑Ω⁴ (limᵢ p f) = limₙ⁴ p (↑Ω⁴ ∘ f ∘ coe₀)

ΩΩ⁴ : OrdΩ⁴
ΩΩ⁴ = lim (λ n → limₙ⁴ {ℓ = ψᴰ⁴ n} (cumsum-mono (ordᴰ ∘ ψⁿᴴ³) zero) ↑Ω⁴)

ψ<Ω⁴ : OrdΩ⁴ → Ord (ψᴰ⁴ n)
ψ<Ω⁴ zero = Ω _
ψ<Ω⁴ (suc a) = lfp (ψ<Ω⁴ a +_)
ψ<Ω⁴ (lim f) = lim (ψ<Ω⁴ ∘ f)
ψ<Ω⁴ {n} (limₙ⁴ {n = m} p f) with <ᴺ-dec m n
... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω⁴ ∘ f ∘ ψ< p ∘ coe {q = zero})
... | injᵇ n<m = lfp (ψ<Ω⁴ ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
... | injᶜ refl = lfp (ψ<Ω⁴ ∘ f ∘ ψ< p)

ψⁿᴴ⁴ : ℕ → Ord₀
ψⁿᴴ⁴ n = ψ₀ (ψ<Ω⁴ {n = n} ΩΩ⁴)
```

## 强度 demo

每层一个顶级 binding, 验证端到端 type-check + 强度阶梯递增:

```agda
Higher¹ : Ord₀
Higher¹ = lim ψⁿᴴ¹     -- ≈ ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) = Higher.agda

Higher² : Ord₀
Higher² = lim ψⁿᴴ²     -- ≈ ψ(Ω_(Ω+2))-ish, 严格 > Higher.agda

Higher³ : Ord₀
Higher³ = lim ψⁿᴴ³     -- ≈ ψ(Ω_(Ω+3))-ish

Higher⁴ : Ord₀
Higher⁴ = lim ψⁿᴴ⁴     -- ≈ ψ(Ω_(Ω+4))-ish
```

外层 `lim k → Higher^k` 不能直接写为 ℕ → Ord₀ (因每层是不同 data type, 不能函数化). 真正的 Higher^ω 需 Phase 6.2 `OrdH α` 的 transfinite 单一数据类型.

## Phase 6.1 总结

| 层 | data type | 估算强度 |
|----|-----------|---------|
| 0 (BTBO) | Ord₀ | ψ(Ω_Ω) |
| 1 (Higher.agda) | OrdΩ | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) |
| **2** (本模块) | OrdΩ² | **≈ ψ(Ω_(Ω+2))** |
| **3** (本模块) | OrdΩ³ | **≈ ψ(Ω_(Ω+3))** |
| **4** (本模块) | OrdΩ⁴ | **≈ ψ(Ω_(Ω+4))** |

每层 ~30 LOC 符号化拷贝, **完全机械化**. 这暗示 Phase 6.2 单一数据类型 `OrdH α` 是自然的下一步, 把 k = ℕ 推广到 α = Ordᴰ.

强度量级评估留待 [FINDINGS_Phase6.md](FINDINGS_Phase6.md).
