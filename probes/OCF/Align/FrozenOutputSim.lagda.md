# 带世界回灌的结构模拟工具

比较两条真正的 Col 回灌，坐标与输出用逐构造子 Same，世界关系可另选。
更新律使用初始世界（与 Col 定义一致），不误写成逐步更新当前世界。
本工具不假定输出折叠对值序单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputSim where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Align.FrozenInnerOuter using (same-add)
import OCF.Lean.Fold1Fold as F

module Sim {A B : Set} {S T : KS}
  (Rel : A → B → Set)
  (wa : A) (wb : B) (rw : Rel wa wb)
  (a b : HB S) (rab : Same a b)
  (ua : A → HB S → A) (ub : B → HB S → B)
  (up : ∀ {w v x y} → Rel w v → Same x y → Rel (ua w x) (ub v y))
  (fx : A → HB S → HB S) (gx : B → HB S → HB S)
  (ft : A → HB S → HB T) (gt : B → HB S → HB T)
  (sx : ∀ {w v x y} → Rel w v → Same x y → Same (fx w x) (gx v y))
  (st : ∀ {w v x y} → Rel w v → Same x y → Same (ft w x) (gt v y)) where

  module L = F.Col _⊞_ _⊞_ wa a ua fx ft
  module R = F.Col _⊞_ _⊞_ wb b ub gx gt

  coordinates : ∀ n → Same (L.ce n) (R.ce n)
  worlds : ∀ n → Rel (L.cw n) (R.cw n)
  coordinates zero = rab
  coordinates (suc n) = same-add (coordinates n) (sx (worlds n) (coordinates n))
  worlds zero = rw
  worlds (suc n) = up rw (coordinates (suc n))

  outputs : ∀ n → Same (L.oo n) (R.oo n)
  outputs n = st (worlds n) (coordinates n)
  sums : ∀ n → Same (L.oO n) (R.oO n)
  sums zero = outputs zero
  sums (suc n) = same-add (sums n) (outputs (suc n))
```

冻结实现自己的 Col 与原实现有不同的递归定义名，不能靠 refl 合并。
以下对左侧冻结 Col 重做同一归纳。

```agda
import OCF.Lean.SupCollapseFrozen as N
module SimN {A B : Set} {S T : KS}
  (Rel : A → B → Set)
  (wa : A) (wb : B) (rw : Rel wa wb)
  (a b : HB S) (rab : Same a b)
  (ua : A → HB S → A) (ub : B → HB S → B)
  (up : ∀ {w v x y} → Rel w v → Same x y → Rel (ua w x) (ub v y))
  (fx : A → HB S → HB S) (gx : B → HB S → HB S)
  (ft : A → HB S → HB T) (gt : B → HB S → HB T)
  (sx : ∀ {w v x y} → Rel w v → Same x y → Same (fx w x) (gx v y))
  (st : ∀ {w v x y} → Rel w v → Same x y → Same (ft w x) (gt v y)) where

  module L = N.Col _⊞_ _⊞_ wa a ua fx ft
  module R = F.Col _⊞_ _⊞_ wb b ub gx gt

  coordinates : ∀ n → Same (L.ce n) (R.ce n)
  worlds : ∀ n → Rel (L.cw n) (R.cw n)
  coordinates zero = rab
  coordinates (suc n) = same-add (coordinates n) (sx (worlds n) (coordinates n))
  worlds zero = rw
  worlds (suc n) = up rw (coordinates (suc n))

  outputs : ∀ n → Same (L.oo n) (R.oo n)
  outputs n = st (worlds n) (coordinates n)
  sums : ∀ n → Same (L.oO n) (R.oO n)
  sums zero = outputs zero
  sums (suc n) = same-add (sums n) (outputs (suc n))
```
