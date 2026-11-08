# 原规范观察沿合法高度位置的完整包含

每次比较都给出同一个合法高度B以及a在B内的实际路径。较小侧
合法证据正是沿该路径从B取得的证据，不要求任意合法证据无关。
这是对原collapse的统一位置定理，不是Γ对任意输入值序单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObservePosition where
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCanonical
  using (collapse; canonical-component)
open import OCF.Lean.GeneralOmegaCountableRegularCompareInflation
  using (module Successor)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)

position-collapse : ∀ {a B : Cd} (lB : LgB B) (p : a ⊲ B) →
  collapse a (lgB⊲ p tt lB) ≤ᵛ collapse B lB
position-collapse lB hself = ≤-refl _
position-collapse {B = hs B} lB (hsuc p) = ≤-trans
  (position-collapse lB p)
  (≤-trans (≤s (≤-refl _)) (Successor.strict B lB))
position-collapse {B = hl f} lB (hlim n p) = ≤-trans
  (position-collapse (proj₂ lB n) p) (canonical-component f lB n)
position-collapse lB (hLim {κ = ()} e p)

actual-Γ-position : ∀ {a} c (p : a ⊲ leg c) →
  collapse a (lgB⊲ p tt (Lg-leg c)) ≤ᵛ Γ c
actual-Γ-position c p = position-collapse (Lg-leg c) p

-- 所有原Γ调用都有实际实例；并非空的位置条件。
zero-position : ∀ c →
  collapse hz (lgB⊲ (z⊲ᴮ (leg c)) tt (Lg-leg c)) ≤ᵛ Γ c
zero-position c = actual-Γ-position c (z⊲ᴮ (leg c))
```

actual-Γ-position捕获原Γ完成输入高度的全部实际位置。较小侧仍是
collapse a而非Γ a；若要替成Γ a，须独立处理a的再次完成，不能
把这一区别隐藏为一般leg或Γ单调。
