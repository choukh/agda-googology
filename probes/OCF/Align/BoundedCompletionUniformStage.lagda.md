# 原有限动作的阶段无关三步实例

F取原self-target at，H取原最高反馈coordinate；所有n使用同一份
StrideRun归纳。orbit是这些原动作的显式数组，尚未识别为Old的世界更新数组。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformStage where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-sym)
open import OCF.Lean.BoundedStrideIf
import OCF.Lean.BoundedStrideRun as Generic
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteValueIf using (coordinate)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure
open import OCF.Align.BoundedCompletionUniformFirst using (first-floor)
open import OCF.Align.BoundedCompletionUniformCompute

same-left : ∀ {S Q a b c} → Same a b → TreeValue S Q b c → TreeValue S Q a c
same-left zz vz = vz
same-left (ss s) (vs p) = vs (same-left s p)
same-left s (vr p) = vr (same-left s p)
same-left (ll s) (vl p) = vl (λ n → same-left (s n) (p n))
same-left s (vli n p) = vli n (same-left s p)
same-left (oo s) (vo p) = vo (λ x y r → same-left (s x) (p x y r))
same-left s (vor p) = vor (λ c → same-left s (p c))

step-inflate : ∀ n {a b} → Value (num n) a b → Value (num n) a (coordinate n b)
step-inflate n {b = b} p = same-right
  (Affine.inflate (Native (num n)) (CoordValue (num n)) (right-rel (Θ.model n) p))
  (same-sym (coordinate-run n b))
step-action : ∀ n {a b} → Value (num n) a b → Value (num n) (F n a) (coordinate n b)
step-action n {a} {b} p = same-left (self-run n a)
  (same-right (Affine.mono (Native (num n)) (CoordValue (num n)) (right-rel (Θ.model n) p))
    (same-sym (coordinate-run n b)))
step-positive : ∀ n b → Value (num n) (hs hz) (coordinate n b)
step-positive n b = same-right
  (Affine.positive (Native (num n)) (CoordValue (num n)) (Θ.model n ⊞ b))
  (same-sym (coordinate-run n b))

orbit : ∀ n → ℕ → HB (Native (num n))
orbit n zero = floor n
orbit n (suc k) = orbit n k ⊞ F n (orbit n k)
padded : ∀ n → ℕ → HB (Native (num n))
padded n zero = orbit n zero
padded n (suc k) = padded n k ⊞ hs (orbit n (suc k))

laws : ∀ n → StrideLaws (Native (num n)) (Value (num n))
  (F n) (coordinate n) (orbit n) (padded n)
laws n = record
  { old-step = λ k → refl ; pad-zero = refl ; pad-step = λ k → refl
  ; append = prefix-rel ; prepend = right-rel ; add = add-rel
  ; inflate = step-inflate n ; action = step-action n ; positive = step-positive n
  ; initial = first-floor n }

module Stage n = Generic.Run (laws n)
```

laws是全部有限层的真实动作实例，包含会坍缩层，不只base恒等实例。
Stage.coordinates/padded-coordinates/padded-partial的右边全部是原coordinate链。
它们没有自动把orbit等同于Old.TΩ的多槽世界轨道；该识别仍是独立义务。
