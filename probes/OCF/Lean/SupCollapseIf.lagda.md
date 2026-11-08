# sup 折叠中的更新义务：先区分接口与强度

接口定稿 2026-11-06。已检查 `NegFold1Sup`：只降一级与双向分量相容
不可行，而 `Fold1` 已覆盖可数层号的 sup。本轮不重复这一站。

检查真正的 `Fold1Fold.Vw.co` 后发现，更新只须保持世界合法；没有
要求更新后读到新坐标。因此 `liftL` 中的 `updAt` 不是这个弱接口的
必要字段。把它换成不更新，类型与合法性义务仍成立；但值可能变小。
这不解决 Ω-sup 的位置与 ext，只把真正未写的强度义务从类型障碍中分离。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SupCollapseIf where

open import Data.Product using (Σ; _×_)
open import OCF.Lean.CRwBase

-- 分量族可由任意类型 I 编号，未假设 I 可判等。
record WeakUpdate (I : Set) (F : I → KS)
                  (Legal : ((i : I) → Wd (F i)) → Set) : Set₁ where
  field
    update : (i : I) → ((j : I) → Wd (F j)) → Wd (F i) → ((j : I) → Wd (F j))
    preserves : ∀ i W v → Legal W → LgW (F i) v → Legal (update i W v)

-- 额外的真实读回义务单列：弱接口不包含它。
record Readback (I : Set) (F : I → KS)
                (Legal : ((i : I) → Wd (F i)) → Set)
                (R : WeakUpdate I F Legal) : Set₁ where
  open WeakUpdate R
  field
    receives : ∀ i W v → Legal W → LgW (F i) v →
      _≤w_ (F i) v (update i W v i)
```

`receives` 不比较裸序数下标；它在同一分量内给出请求世界到返回世界
的显式关系。它不要求别处不变，也不宣称是终点强度的充分规格。
