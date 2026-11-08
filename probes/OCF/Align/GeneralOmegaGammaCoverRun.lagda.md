# 已证γ下界沿真实后继地板传播

验收专用。这里的升层使用原floor-up的Coded证明及原后继run的完整
回调定理，不把任意输入Same直接送过run。它提供可实例化的错位
机制，但不会凭空把ψ₀(Ω₁)变成ψ₀(Ω₂)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaCoverRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.LHRecTy using (LH; lz; ls)
open import OCF.Lean.Fold1If using (≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf using (Layer; lz′; ls′)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeActual using (floor-up)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (strict-step)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaGammaCoverIf

lift : ∀ {t h x} → Layer x x → Cover t h x → Cover t h (ls x)
lift {x = x} p c = record { lower = ≤-trans (Cover.lower c)
  (≤-trans (same-value (floor-up p))
    (≤-trans (≤s (≤-refl _)) (strict-step x))) }

shift : ℕ → LH
shift zero = ls (ls lz)
shift (suc n) = ls (shift n)
shift-self : ∀ n → Layer (shift n) (shift n)
shift-self zero = ls′ (ls′ lz′)
shift-self (suc n) = ls′ (shift-self n)
one-shifted : ∀ n → Cover (L.suc L.zero) (L.hs L.hz) (shift n)
one-shifted zero = one
one-shifted (suc n) = lift (shift-self n) (one-shifted n)
```

one-shifted是全部自然数n的真实非零实例。下界始终是ψ₀(Ω₁)，
不是下标随n增长的ψ₀(Ω_n)。要处理前篇γ₂首回调，仍缺后者的统一
原typed坐标模拟；这里不以这个缺口否定更高ΩL源或错位覆盖。
