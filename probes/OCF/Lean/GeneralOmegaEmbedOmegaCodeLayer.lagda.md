# 全部有证原层的完整后继闭包公式

原A x与低层地板输出的跨up身份已经证明。现在将其代回先前保留A x
的完整后继公式；只在纯动作反馈上运输Same，不将Same喂任意源分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaCodeLayer where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (ls)
open import OCF.Lean.LHRecLay using (twL; ΛL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf using (Layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaLayer using (tower-layer; lambda-layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeActual using (floor-up)
open import OCF.Lean.GeneralOmegaConsumeLayerIf using (A; H; closure)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (whole; act-same; leg-same; same-trans; strict-step)
import OCF.Lean.GeneralOmegaConsumeRun as R
import OCF.Lean.BoundedDiagonalSame as D

closure-same : ∀ {a b : Cd} → Same a b → Same (closure a) (closure b)
closure-same {a} {b} p = D.Compare.result (H a) (H b) (H a) (H b)
  (λ q → act-same p (leg-same q)) (λ q → act-same p (leg-same q))

successor-whole : ∀ {x} → Layer x x →
  Same (R.run (ls x) (flL (ls x))) (closure (R.run x (flL x)))
successor-whole {x} p = same-trans (whole x) (closure-same (same-sym (floor-up p)))
successor-strict : ∀ {x} → Layer x x →
  hs (R.run x (flL x)) ≤ᵛ R.run (ls x) (flL (ls x))
successor-strict {x} p = ≤-trans
  (OCF.Lean.Fold1If.s≤s (same-value (floor-up p))) (strict-step x)

tower-successor : ∀ n → Same
  (R.run (ls (twL n)) (flL (ls (twL n)))) (closure (R.run (twL n) (flL (twL n))))
tower-successor n = successor-whole (tower-layer n)
lambda-successor : Same (R.run (ls ΛL) (flL (ls ΛL))) (closure (R.run ΛL (flL ΛL)))
lambda-successor = successor-whole lambda-layer
```

这是一条对Layer证书的一步完整输出定理，原全部twL与Λ都有实例。
它没有把ΩL改成ls，也不自动给原EBOγ迭代的值桥；不能从后继闭包
公式推断原Λ输出已达到ψ₀Λ。
