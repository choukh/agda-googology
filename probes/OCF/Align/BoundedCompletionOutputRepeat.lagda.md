# 真实末段折叠的重复共尾下界

末段并非加法同态，但完整ω重复可吸收每个输出和所需的后继补偿。
这里按两个原重复项吸收一个pad步骤，直接得到原Ops.repeat的值下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputRepeat where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure using (add-rel)
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionOutputPadding using (pad; pad-self; padded-add)
import OCF.Align.BoundedNativeTerminalReady as T

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

module Repeat (a : HB U) (self : VRel a a) (positive : VRel (hs hz) a) where
  inputs : ∀ n → VRel (pad (λ _ → a) n)
    (Ops.partial U (λ _ → a) (double n))
  inputs zero = self
  inputs (suc n) = add-rel (add-rel (inputs n) self) positive

  outputs : ∀ b n → mul (T.fold b a) n ≤ᵛ T.fold b (pad (λ _ → a) n)
  outputs b zero = ≤-refl _
  outputs b (suc n) = ≤-trans (add-mono (outputs b n) (≤-refl _))
    (padded-add (pad-self (λ _ → a) (λ _ → self) n) self (≤-refl b) (≤-refl b))

  lower : ∀ b → hl (mul (T.fold b a)) ≤ᵛ T.fold b (Ops.repeat U a)
  lower b = l≤ (λ n → ≤l (double n)
    (≤-trans (outputs b n) (eval (inputs n) (≤-refl b))))

module Example = Repeat (hs hz) (vs vz) (vs vz)
```

Example是实际非零输入实例。一般结论仍明确要求两个VRel证书，不能
由任意raw输入套用，也没有由有限抽样推断整个ω重复。
