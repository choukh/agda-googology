# 标准ω到其完成的整观察值捕获

所有n使用同编号的真实部分和分量，预算为n≤0+1+⋯+n。
不是有限测试。闭项取已有逐点观察输出的合法完成；它的原Γ包含
由既有Point.actual-Γ提供，不把任意值比较送过leg。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableOuterCaptureActual where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; omega; omega-legal)
open import OCF.Lean.GeneralOmegaCountableCapturePath using (sum-leg-num; sum-large; num-path)
open import OCF.Lean.GeneralOmegaCountableOuterCaptureIf
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
import OCF.Lean.GeneralOmegaCountableNextCapturePointActual as Point
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.GeneralOmegaCountableOuterCaptureRun using (capture)

completed-branch : ℕ → Cd
completed-branch n = Σ₀ (λ k → leg (num k)) n
budget : ∀ n → num n ⊲ completed-branch n
budget n rewrite sum-leg-num (λ k → k) n = num-path (sum-large (λ k → k) n)
access : ∀ n → Σ ℕ (λ m → num n ⊲ completed-branch m)
access n = n , budget n

whole-omega : point-root omega omega-legal ≤ᵛ point-root (leg omega) (Lg-leg omega)
whole-omega = capture num completed-branch omega-legal (Lg-leg omega) access

closed : Cd
closed = leg (point-root (leg omega) (Lg-leg omega))
legal-closed : LgB closed
legal-closed = Lg-leg _
whole≤closed : point-root omega omega-legal ≤ᵛ closed
whole≤closed = ≤-trans whole-omega (inflation _)
closed≤Γomega : closed ≤ᵛ Γ omega
closed≤Γomega = Point.actual-Γ omega
whole≤Γomega : point-root omega omega-legal ≤ᵛ Γ omega
whole≤Γomega = ≤-trans whole≤closed closed≤Γomega
```

whole-omega比较两个完整观察输出，whole≤closed同时给出合法闭项
及其值下界。它只填完成比较在标准ω上的真实实例；一般后继内部
完成、Γ右高度加法吸收、整个γ₂输入完成律仍未由本篇推出。
