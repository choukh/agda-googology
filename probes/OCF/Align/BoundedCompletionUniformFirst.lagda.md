# 全有限真实反馈的有向地板覆盖

把此前裸值初界覆盖加强为可被原分支比较消费的Value关系。
最高回灌仍是原coordinate/chain，不由自造轨道代替。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformFirst where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.FrozenWorldLift using (same-sym)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueIf using (coordinate; first)
import OCF.Align.BoundedCompletionFiniteValueFirst as Actual
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure
open import OCF.Align.BoundedCompletionUniformRun using (compare)

model-value : ∀ n → Value (num n) (Θ.model n) (Θ.model n)
model-value zero = add-rel vz (floor-value zero)
model-value (suc n) = add-rel (up-value (num n) (model-value n)) (floor-value (suc n))
model-floor : ∀ n → Value (num n) (floor n) (Θ.model n)
model-floor zero = right-rel hz (floor-value zero)
model-floor (suc n) = right-rel (up (Θ.model n)) (floor-value (suc n))

first-floor : ∀ n → Value (num n) (floor n) (first n)
first-floor n = right-rel (hs hz)
  (same-right
    (Affine.inflate (Native (num n)) (CoordValue (num n))
      (prefix-rel (model-floor n) (hs hz)))
    (same-sym (Actual.Actual.up-run n (Θ.model n ⊞ hs hz))))

floor-tail : ∀ n k → Value (num n) (floor n) (chain (coordinate n) (suc k))
floor-tail n zero = first-floor n
floor-tail n (suc k) = prefix-rel (floor-tail n k) _

coordinate-mono : ∀ n {a b} → Value (num n) a b →
  Value (num n) (coordinate n a) (coordinate n b)
coordinate-mono n p = compare (suc n) n {B = num (suc n)} {B′ = num (suc n)}
  (legal-num (suc n)) (legal-num (suc n)) hself hself (hsuc hself) (hsuc hself)
  (add-rel (up-value (num n) (model-value n)) (up-value (num n) p))

coordinate-self : ∀ n k → Value (num n) (chain (coordinate n) k) (chain (coordinate n) k)
coordinate-self n zero = vs vz
coordinate-self n (suc k) = add-rel (coordinate-self n k) (coordinate-mono n (coordinate-self n k))
```

first-floor、floor-tail、coordinate-self全部实例化原最高反馈，且源层
随n变化；不是只对base U的模板。仍未声称Old的每层动态世界已被模拟。
