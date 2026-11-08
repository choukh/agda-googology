# 全层算法的统一后继输出接口

A x是同一原运行器在后继层中对旧地板嵌入的输出，不偷换成run x(flL x)。
整个后继地板的回调应是以A x为零点的纯树动作再作用于leg反馈。
跨层嵌入一致性与Ω指标层归并仍是独立问题。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaConsumeLayerIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Lean.LHRecTy using (LH; ls)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.BoundedFoldRun using (diagonal)
import OCF.Lean.BoundedMixedAffine as Aff
import OCF.Lean.GeneralOmegaConsumeRun as R

A : LH → Cd
A x = R.run (ls x) (up (flL x))
H : Cd → Cd → Cd
H a d = Aff.Action.run S⊥ a (leg d)
closure : Cd → Cd
closure a = diagonal (H a) (H a)

record SuccessorLayer : Set where
  field
    whole : ∀ x → Same (R.run (ls x) (flL (ls x))) (closure (A x))
    strict-step : ∀ x → hs (A x) ≤ᵛ R.run (ls x) (flL (ls x))
```

这不是未实例化的全raw单调假设。具体证明只能在纯尾结构与实际地板
上用同余；不可把Same坐标直接喂给任意源Ω分支。
