# 原Γ在共同合法界内的值单调性检验接口

后继严格增长只比较c与hs c，不能直接推出此处的律。这里要求
输入a、b都在同一个字面合法B下，且各自合法；比较的是已知值界，
没有对两棵裸树作判定。构造与否定共用此冻结接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableGammaOrderIf where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)

record BoundedValueMonotone : Set where
  field
    monotone : ∀ {B a b : Cd} → LgB B → LgB a → LgB b →
      a ⊲ B → b ⊲ B → a ≤ᵛ b → Γ a ≤ᵛ Γ b

-- 同一合法零值高度中的两个实际输入，所有前提同时可满足。
empty-limit : Cd
empty-limit = hl (λ _ → hz)
empty-legal : LgB empty-limit
empty-legal = (λ _ → hself) , (λ _ → tt)
empty≤zero : empty-limit ≤ᵛ hz
empty≤zero = l≤ (λ _ → z≤)
zero≤empty : hz ≤ᵛ empty-limit
zero≤empty = z≤
empty-in-common : empty-limit ⊲ empty-limit
empty-in-common = hself
zero-in-common : hz ⊲ empty-limit
zero-in-common = hlim 0 hself
```

这只命名待检验的律及实际零值输入；未在接口本身声称该律成立
或不成立。原Γ和地板均不修改，检验结果必须由另篇值定理给出。
