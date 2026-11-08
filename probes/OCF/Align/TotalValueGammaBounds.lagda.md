# 原完整 BTBO 链吸收有限加法

对实际 NC.γ 证明，不把阶段名当作加法封闭性。相邻项有严格前驱，
于是一次有限二倍落进下一反馈阶段；给上界归纳使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueGammaBounds where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.TotalValueCumulativeAbsorb as V

strict : ∀ n → N.γ n ≺ N.γ (suc n)
strict zero = ≺l 0 (≺l 2 (≺z (s≅ z≅)))
strict (suc n) = V.Ψ⁰-mono
  (s⊑′ (toLevel-≺ (N.cert n) (N.cert (suc n)) (strict n)))
  (V.Fstep (N.D.L n))

monotone : ∀ n → N.γ n ≼ N.γ (suc n)
monotone n = ≺→≼ (≺→s≼ (strict n))

ordered : ∀ {n m} → n ≤ m → N.γ n ≼ N.γ m
ordered {m = zero} z≤n = ≼-refl _
ordered {m = suc m} z≤n = ≼-trans (ordered {m = m} z≤n) (monotone m)
ordered (s≤s p) = step p
  where
  step : ∀ {n m} → n ≤ m → N.γ (suc n) ≼ N.γ (suc m)
  step {n} {m} p = ⊑→≼ _ (V.Ψ⁰-mono
    (toLevel-⊑ (N.cert n) (N.cert m) (position p)))
    where
    position : ∀ {n m} → n ≤ m → N.γ n ⊑⁰ N.γ m
    position {m = zero} z≤n = λ h → h
    position {m = suc m} z≤n = ⊑-trans (position {m = m} z≤n) (λ h → V.≺→⊑₀ (strict m) h)
    position (s≤s q) = V.Ψ⁰-mono
      (toLevel-⊑ (N.cert _) (N.cert _) (position q))

double-next : ∀ n → N.γ n + N.γ n ≼ N.γ (suc n)
double-next zero = ≺→s≼ (strict zero)
double-next (suc n) = ≼-trans (≼l 2 (≼-refl _))
  (≼-trans (⊑→≼ _ (V.Fmul (N.D.L n)))
    (⊑→≼ _ (V.Ψ⁰-mono (s⊑′
      (toLevel-≺ (N.cert n) (N.cert (suc n)) (strict n))))))

double : ∀ n → N.γ n + N.γ n ≼ N.γ (suc (suc n))
double n = ≼-trans (double-next n) (monotone (suc n))
```
