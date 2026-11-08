# 同一合法界内的后继准入与严格位置方向

内部观察目标a若带hs a⊲B，另一个秩i也在同一原合法B内，则
严格树形方向可以提升为hs a⊲i。这里H是已有辅助结构测量，不是
输入值或新的最终序数定义；比较始终只在这个字面公共B内进行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableAdmittedOrder where
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableHeightNegOrder using (H; measure-position)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

successor-in-bound : ∀ {a i B : Cd} → LgB B → hs a ⊲ B → i ⊲ B →
  hs (H a) ≤ᵛ H i → hs a ⊲ i
successor-in-bound {a} lB pa pi strict with cmpB pa pi tt lB
... | inj₂ q = q
... | inj₁ hself = hself
... | inj₁ (hsuc q) = ⊥-elim (¬s≤ᵛ (H a)
  (≤-trans strict (position-value (measure-position q))))

finite-instance : hs hz ⊲ hs hz
finite-instance = successor-in-bound tt hself hself (≤-refl _)
omega-instance : hs hz ⊲ omega
omega-instance = successor-in-bound omega-legal (hsuc (hlim 1 hself))
  (hsuc hself) (s≤s z≤)
```

omega-instance的原公共B为hs omega，所有前提实际满足。此结果
不适用于只给a⊲B的任意根目标：hs a的准入证据是关键字段，不能
从普通位置自动补出。旧typed层比较仍须由该实际路径单独翻译。
