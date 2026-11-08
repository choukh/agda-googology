# 分类实例到全部真实有限输出的连接

本篇保留分类参数，便于与原cmpB分类证明独立编译；最终无条件
结论必须另以真实Classification实例封闭。此处不声称参数已填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteWhole where
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num)
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
import OCF.Lean.GeneralOmegaFiniteObserveClosed as F
import OCF.Align.GeneralOmegaGammaCoverFinite as Ref
import OCF.Align.GeneralOmegaFiniteAmbientActual as Value
open import OCF.Align.GeneralOmegaCountableFiniteIf
open import OCF.Align.GeneralOmegaCountableFiniteRel using (floor-rel; zero-same)
open import OCF.Align.GeneralOmegaCountableFiniteNormalize using (raw-normal)
import OCF.Align.GeneralOmegaCountableFiniteRun as Run

module Bridge (classification : Classification) where
  module R = Run.Bridge classification
  raw-same : ∀ n → Same (C.rawΓ (num n)) (F.stage n)
  raw-same n = subst (λ a → Same a (F.stage n)) (sym (raw-normal n))
    (zero-same (R.observe-rel (F.zero-path n) (z⊲ᴮ (num n)) (floor-rel n)))
  raw≤finite : ∀ n → C.rawΓ (num n) ≤ᵛ F.stage n
  raw≤finite n = same-value (raw-same n)
  finite≤raw : ∀ n → F.stage n ≤ᵛ C.rawΓ (num n)
  finite≤raw n = same-value (same-sym (raw-same n))
  reference≤raw : ∀ n → Ref.finite n ≤ᵛ C.rawΓ (num n)
  reference≤raw n = ≤-trans (Value.reference≤stage n) (finite≤raw n)
  raw≤reference : ∀ n → C.rawΓ (num n) ≤ᵛ Ref.finite n
  raw≤reference n = ≤-trans (raw≤finite n) (Value.stage≤reference n)
  reference≤Γ : ∀ n → Ref.finite n ≤ᵛ C.Γ (num n)
  reference≤Γ n = ≤-trans (reference≤raw n) (inflation (C.rawΓ (num n)))
```

这里的Γ都是指定参数num n的值，不是Γ迭代的stage n。即使分类
参数实填，也不能把reference≤Γ改写成最终迭代tree的大小定理。
