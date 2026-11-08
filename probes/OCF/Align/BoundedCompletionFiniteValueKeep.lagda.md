# 全保留实际决定的点态计算接口

这里只要求实际keep坐标逐点等于原坐标，不要求两个函数相等。
该接口由沿有限classify重建的证明填入；不是任意折叠假设。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteValueKeep where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)

data Keeps {B n} (κ : K (Native (num n))) :
  Decision B (num n) (E (Native (num n)) κ) → Set where
  retained : ∀ fr → (∀ e → fr e ≡ e) → Keeps κ (keep κ fr)

record SelfKeep : Set where
  field
    self-keep : ∀ n κ → Keeps {n = n} κ
      (decide {B = num n} {t = num n} hself (legal-num n)
        (raise hself (classify (num n) κ)))
```
