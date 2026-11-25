# YiUB 第 1 层：主线折叠对参照 ψ₀(Ω₁) 的两个方向

**验收文件，档位：编译定理，无前提。** `ub₁ : read (F (fin 1) tt) ≼ L.ψ⁰ (L.Ω (L.toLevel (read (fin 1)) (HS-read (fin 1) tt)))`，并且两个方向都在 `≼ˣ` 里 (`ub₁ˣ`, `lb₁ˣ`)。
`F (fin 1)` 与 `F top` 定义性相同，内层链就是 [YiChainOne](YiChainOne.lagda.md) 的 `cc`；上界用 [YiChainBack](YiChainBack.lagda.md) 的 `PHIR`, `GcR`，下界用 `PHI`, `Gc`。只谈第 1 层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUBOne where

open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (F)
open import OCF.Lean.YiLeanAccFin using (read; fin)
open import OCF.Lean.YiLeanValFin using (HS-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ≼lˣ; lˣ; ˣ→≼)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ)
open import OCF.Lean.YiChainBase using (transˣ)
open import OCF.Lean.YiChainOne using (cc; Gc; x₁; module Phi)
open import OCF.Lean.YiChainBack using (GcR; module PhiR)
```

参照 ψ⁰ (Ω 1) 定义性地是 `lim (λ k → ψ⁰ (D.G k))`；主线 `F (fin 1)` 定义性地是 `lim (λ k → Ψ⁰ (cc k))`，逐项对齐，不错开下标。

```agda
Ω₁ᵀ : L.Ordᶜ L.zero
Ω₁ᵀ = L.ψ⁰ (L.Ω (L.toLevel (read (fin 1)) (HS-read (fin 1) tt)))

ub₁ˣ : read (F (fin 1) tt) ≼ˣ Ω₁ᵀ
ub₁ˣ = lˣ (λ k → ≼lˣ k (transˣ (proj₁ (PhiR.PHIR x₁ (cc k))) (ψ⁰ˣ (GcR k))))

lb₁ˣ : Ω₁ᵀ ≼ˣ read (F (fin 1) tt)
lb₁ˣ = lˣ (λ k → ≼lˣ k (transˣ (ψ⁰ˣ (Gc k)) (proj₁ (Phi.PHI x₁ (cc k)))))

ub₁ : read (F (fin 1) tt) ≼ Ω₁ᵀ
ub₁ = ˣ→≼ ub₁ˣ

≈₁ : (Ω₁ᵀ ≼ˣ read (F (fin 1) tt)) × (read (F (fin 1) tt) ≼ˣ Ω₁ᵀ)
≈₁ = lb₁ˣ , ub₁ˣ
```
