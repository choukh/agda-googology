# $\psi_0(\Omega_{\Omega+1})$ 的条件定理的前提为假

> 接 [OmegaPlus1](OmegaPlus1.lagda.md) 与 [OmegaSqA](OmegaSqA.lagda.md). OmegaPlus1 的 `TO-label¹`、`TO·2-label¹` 以 `HΩ̂` 为前提, 当时未知它是否有居留. OmegaSqA 的 `¬TΩ2-label` 说现行统一树没有 $\psi_0(\Omega_\Omega^2)$ 的标签. 本文把两者接起来:
>
> 1. **`¬H1`**: `tow1` 在深度 1 的闭包假设无居留. 证明就是 Uniform2 的 `TΩ2-cond` 的三行, 把 `BranchΩ` 换成该假设, 再交给 `¬TΩ2-label`.
> 2. **`¬HΩ̂¹`、`¬HΩ̂≤1`**: 所以 `Generic.HΩ̂ tow1` 与 `HΩ̂≤ 1` 都假, `TO-label¹`、`TO·2-label¹` 与 `TO-pt` 在 $n\ge1$ 处在现行树族上是空真命题.
>
> 这不否定 $\Omega_{\Omega+1}$ 替身的设计, 也不否定对任意塔的归约定理 `goodΩ⁺`; 否定的是现行 `fold` 的 `up (self n)` 地板子句下这个前提能被满足. 地板收紧之后要重新检验.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaPlus1Neg where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using ([]; _∷_; _++_)

open import OCF.Align.Level
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2Depth1
open import OCF.Align.Uniform2 using (good∅ᴿ; wkGA1)
open import OCF.Align.OmegaKBase using (tΩ2-NF)
open import OCF.Align.OmegaSqA using (¬TΩ2-label)
open import OCF.Align.OmegaPlus1Base using (tow1; module Generic)
open import OCF.Align.OmegaPlus1 using (module T1)
```

```agda
¬H1 : (∀ {fl} {E : A 1 fl} {ζ} → GA1 E ζ → GA1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])) → ⊥
¬H1 H = ¬TΩ2-label (λ ev z → g0 (gv1 GΨ good∅ᴿ) ev z tΩ2-NF)
  where
  GΨ : GA1 (Ψ ∅ᵀ 1 (Ω̂A 0)) (ψΩᵗ [])
  GΨ = wkGA1 {φ = fk zero ⊔ fk zero} {ψ = fk zero ⊔ (fk zero ⊔ fz)} (λ { (u , v) → u , proj₁ v }) (λ { (inl k) → inl k ; (inr (inl k)) → inr k ; (inr (inr ())) })
             (H goodΩ̂₀)

¬HΩ̂≤1 : T1.HΩ̂≤ 1 → ⊥
¬HΩ̂≤1 H = ¬H1 (proj₂ (H 1 (s≤s z≤n)))

¬HΩ̂¹ : Generic.HΩ̂ tow1 → ⊥
¬HΩ̂¹ H = ¬H1 (proj₂ (H 1))
```
