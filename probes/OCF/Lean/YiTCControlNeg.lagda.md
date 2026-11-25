# 实际对照对象不满足旧 Can 字段
不读记号；编译否定：原第 2 站实际孩子上的 Ω 树不满足 `YiVRRel.Can`。
只排除直接调用旧保持接口所需的这个字段；不否定 `ChildLow₁`，也不把旧 `YiRWFold` 的接口当作主线 `YiTBRow` 的接口。
来源：`YiVRRel.β-not` 的机制；原结论只对 `tw 1`，此处实填原第 2 站的实际孩子函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTCControlNeg where
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Ωt; Up; down; stop)
open import OCF.Lean.YiRWPath using (ink; self)
import OCF.Lean.YiSLStart as S
import OCF.Lean.YiVRRel as R

-- 来源：YiVRRel.β-not；同一机制，参数h抽出以免在巨项上with。
private
  different : (h : Tr zero → L) → R.Le (nd (sΩ zero) h)
    (up zero zero (proj₁ (Ωt (h zero))) (proj₂ (Ωt (h zero))))
    (up zero (suc zero) (proj₁ (Ωt (h (suc zero)))) (proj₂ (Ωt (h (suc zero))))) → ⊥
  different h (R.≼u ())

  forbid : (h : Tr zero → L) → R.Can (nd (sΩ zero) h) (proj₁ (Ωt (nd (sΩ zero) h))) → ⊥
  forbid h (R.≼w (R.≼u ()))
  forbid h (R.w≼w f) = different h (f zero (suc zero) R.z≼)

  H : Tr zero → L
  H z = tw 1 ⊕ ↑ (tw 1) (proj₁ (Up (zero ⊕ ↑ zero z) (down stop z)
    (S.baseᴱ 2 (tw 1) (ink self)) (proj₁ (Ωt (zero ⊕ ↑ zero z)))))

no-sourceCan : R.Can (S.Step.child 1 (S.Step.chain 1 1))
  (proj₁ (Ωt (S.Step.child 1 (S.Step.chain 1 1)))) → ⊥
no-sourceCan = forbid H
```
