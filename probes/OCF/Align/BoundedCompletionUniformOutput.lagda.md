# 全有限原动作阶段的完整输出覆盖

将统一延迟证据、全层求值补偿与原emit归并接合。左边是floor起步、
由原self-at迭代的阶段输出；不把它无证等同于Old的多槽世界轨道。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformOutput where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.BoundedStrideRun using (stride)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueIf using (coordinate)
open import OCF.Align.BoundedCompletionFiniteValueFirst using (emit; normal-shape)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionFinitePlaceSample as Sample
import OCF.Align.BoundedCompletionLowerFamily as L
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Align.BoundedNativeTerminalReady as T
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure
open import OCF.Align.BoundedCompletionUniformRun using (compare)
open import OCF.Align.BoundedCompletionUniformFirst using (model-value; coordinate-self)
open import OCF.Align.BoundedCompletionUniformStage
open import OCF.Align.BoundedCompletionUniformEmit using (chain-rel; emit-terminal)
import OCF.Align.BoundedCompletionUniformEvaluation as E
import OCF.Align.BoundedCompletionTerminalValueRun as TV

orbit-self : ∀ n k → Value (num n) (orbit n k) (orbit n k)
orbit-self n zero = floor-value n
orbit-self n (suc k) = add-rel (orbit-self n k)
  (compare n n {B = num n} {B′ = num n} (legal-num n) (legal-num n)
    hself hself hself hself (orbit-self n k))
padded-self : ∀ n k → Value (num n) (padded n k) (padded n k)
padded-self n zero = orbit-self n zero
padded-self n (suc k) = add-rel (padded-self n k) (vs (orbit-self n (suc k)))

sums : ∀ n → Cd → ℕ → Cd
sums n seed = Σ₀ (λ k → E.read n seed (orbit n k))
sums≤pad : ∀ n seed k → sums n seed k ≤ᵛ E.read n seed (padded n k)
sums≤pad n seed zero = E.monotone n (orbit-self n zero) (≤-refl seed)
sums≤pad n seed (suc k) = ≤-trans (add-mono (sums≤pad n seed k) (≤-refl _))
  (E.padded-add n (padded-self n k) (orbit-self n (suc k)) (≤-refl seed) (≤-refl seed))

emit-self : ∀ n k → Value hz
  (emit n (chain (coordinate n) k)) (emit n (chain (coordinate n) k))
emit-self n k = compare (suc n) zero {B = num (suc n)} {B′ = num (suc n)}
  (legal-num (suc n)) (legal-num (suc n)) hself hself
  (z⊲ᴮ (num (suc n))) (z⊲ᴮ (num (suc n)))
  (add-rel (up-value (num n) (model-value n)) (up-value (num n) (coordinate-self n k)))

last-value : ∀ n k → Value hz (emit n (chain (coordinate n) k))
  (Ops.partial (Native hz) (λ j → emit n (chain (coordinate n) j)) k)
last-value n zero = emit-self n zero
last-value n (suc k) = right-rel _ (emit-self n (suc k))

select : ∀ n seed k → T.fold seed (emit n (chain (coordinate n) k)) ≤ᵛ
  T.fold seed (Θ.normal (suc n))
select n seed k = subst (λ h → T.fold seed (emit n (chain (coordinate n) k)) ≤ᵛ T.fold seed h)
  (sym (normal-shape n))
  (≤l k (TV.eval (value-zero (last-value n k)) (≤-refl seed)))

padded-output : ∀ n seed k → E.read n seed (padded n k) ≤ᵛ T.fold seed (Θ.normal (suc n))
padded-output n seed k = ≤-trans
  (E.monotone n (right-rel (Θ.model n) (Stage.padded-coordinates n k)) (≤-refl seed))
  (≤-trans (same-value (emit-terminal n (chain (coordinate n) (stride k))
    (chain-rel n (stride k)) seed)) (select n seed (stride k)))

stage-output : ∀ n → Cd → Cd
stage-output n seed = hl (sums n seed)

stage-lower : ∀ n seed → stage-output n seed ≤ᵛ T.fold seed (Θ.normal (suc n))
stage-lower n seed = l≤ (λ k → ≤-trans (sums≤pad n seed k) (padded-output n seed k))

-- Sample.normalized(suc k)使用的真实阶段号正好是这个数的后继。
sampled-stage : ℕ → ℕ
sampled-stage k = L.plus (L.tri k) k

sampled-stage≤normalized : ∀ k → stage-output (sampled-stage k) V.feedback ≤ᵛ Sample.normalized (suc k)
sampled-stage≤normalized k = stage-lower (sampled-stage k) V.feedback

sampled-stage≤C : ∀ k → stage-output (sampled-stage k) V.feedback ≤ᵛ C.tree
sampled-stage≤C k = ≤-trans (sampled-stage≤normalized k) (Sample.normalized-below-C (suc k))

whole-stages≤C : hl (λ k → stage-output (sampled-stage k) V.feedback) ≤ᵛ C.tree
whole-stages≤C = l≤ sampled-stage≤C
```

stage-lower是对任意有限源层的一条完整输出定理；sampled-stage≤C实证
到原C的全部后续真实采样，而非单个常值或局部坐标条件。
这些阶段的原self-at动作与Old全世界折叠之间仍须比较，故不把whole-stages≤C
改读为Old所有有限TΩ、更不改读为EBO下界。没有修改任何原运行器。
