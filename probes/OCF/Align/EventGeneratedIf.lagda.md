# 原事件地板的动态层节点：生成合同

原 Ωd 在历史 H 读取原 rp H κ，再进入 g(rp H κ) 层的 ni。
本合同不要求这两个动态层字面相等，不要求任意 g 保持关系。
分支域及回调均是原 EvFold 的对象；每侧的位置都在同一原源层中。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedIf where
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EventReturnCodeIf using (Shape)

Coord : Kᵉ → Set
Coord κ = HB (Lev (proj₁ κ))

ReplayAt : Kᵉ → Hist → Hist → Set
ReplayAt κ H J = Shape (rp H (proj₁ κ) (proj₂ κ)) (rp J (proj₁ κ) (proj₂ κ))

module At (κ : Kᵉ) (g : Coord κ → Ht) where
  source : Ht
  source = hΩ (inj₂ κ) g
  rank : Hist → Ht
  rank H = g (rp H (proj₁ κ) (proj₂ κ))
  position : ∀ a H → rank H ⊲[ a , H ] source
  position a H = hLim hself hself
  node : ∀ a H → D source (a , H)
  node a H = ni (sL hself hself) (λ _ _ _ → n1)

  -- 原 Ωd 的整个事件句；没有把历史读取改成常量或预给 floor。
  generated : ∀ {W} → D source W
  generated = n1 ⨾ nε κ (zEΩ κ) (λ {W′} _ _ → node (proj₁ W′) (proj₂ W′))
  generated-exact : ∀ {W} → generated {W} ≡ Ωd source {W}
  generated-exact = refl

  record Pair (a : A) (H J : Hist) : Set where
    field
      layers : Shape (rank H) (rank J)
      left-bound : rank H ⊲[ a , H ] source
      right-bound : rank J ⊲[ a , J ] source

  record Generated : Set₁ where
    field
      legal-source : LgB source
      branch : ∀ {x y} → Shape x y → Shape (g x) (g y)
      pair : ∀ a H J → ReplayAt κ H J → Pair a H J
```

`Pair.layers` 仅是实际动态层的结构证据，不是 D(rank H) 与
D(rank J) 的数据关系，也不推出 Run/BNi/Chn 保持。下一关系若消费
异型低坐标，必须显式携带这里的层对应，不能假定所有 raw 坐标自相关。
