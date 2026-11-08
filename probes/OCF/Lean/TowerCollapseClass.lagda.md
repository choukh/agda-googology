# Stage 降一层的坐标方向更正

保留旧种类时目标坐标到源坐标为恒等；只有最高新种类由回灌消去。
上轮概称跨 step 必须回缩 HB(step S) 到 HB S，范围过宽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerCollapseClass where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerWorldStage

module _ (S : KS) (w : Wd S) (B : HB S) where
  module Low = Stage S w
  module High = Stage (step S) (w , B)
  same-coordinate : ∀ k → Low.E′ k ≡ High.E′ (inj₁ k)
  same-coordinate (inj₁ k) = refl
  same-coordinate (inj₂ _) = refl
  keep-coordinate : ∀ k → Low.E′ k → High.E′ (inj₁ k)
  keep-coordinate (inj₁ k) c = c
  keep-coordinate (inj₂ _) c = c
```

此定理不提供世界可入的拉回，也不提供 next 的搬运。
它排除的是错误的“先找所有坐标回缩”任务，而不是已有壁垒。
