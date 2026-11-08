# 外层极限的有证分量捕获接口

只比较原逐点观察器，不修改原Γ。每个被比较的分量都带在某个
实际目标分量中的位置，故公共界就是该目标分量自身；不要求两棵
完整极限另有公共界。它不假定任意右累计项是原位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableOuterCaptureIf where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

point-root : (B : Cd) → LgB B → Cd
point-root B lB = point-observe B lB hz (z⊲ᴮ B) (pointFloor B)

record OuterPositionCapture : Set₁ where
  field
    capture : ∀ (f g : ℕ → Cd) (lf : LgB (hl f)) (lg : LgB (hl g)) →
      (∀ n → Σ ℕ (λ m → f n ⊲ g m)) → point-root (hl f) lf ≤ᵛ point-root (hl g) lg
```

接口尚未实例化。非有限检验应覆盖标准ω的全部分量到其完成的
三角数列，而不是只检查几个数值。即便此字段实填，也不自动给
后继层反馈比较或整个输入完成律。
