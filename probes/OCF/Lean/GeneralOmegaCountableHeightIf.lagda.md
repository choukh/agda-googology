# 输入高度模拟与可保留的前沿路径

研究接口只比较同一合法字面W内的两个高度，合法证从同一W诱导。
即使已知Sim(leg a)(leg b)，仍不能凭此捏造这两个完成高度的公共W。
下方Leading只记hself、后继及极限第0分量，提供一个能实际运输
完成的非有限域；它不替代一般hlim n路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableHeightIf where
open import Data.Unit using (tt)
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableRegularCompareIf using (Sim)
open import OCF.Lean.GeneralOmegaCountableRegularCompareCanonical using (collapse)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

record BoundedHeightSimulation : Set where
  field
    capture : ∀ {W a b : Cd} (lW : LgB W) (pa : a ⊲ W) (pb : b ⊲ W) →
      Sim hz a b → collapse a (lgB⊲ pa tt lW) ≤ᵛ collapse b (lgB⊲ pb tt lW)

data Leading : Cd → Cd → Set where
  here : ∀ {a} → Leading a a
  next : ∀ {a B} → Leading a B → Leading a (hs B)
  first : ∀ {a f} → Leading a (f 0) → Leading a (hl f)
path : ∀ {a B} → Leading a B → a ⊲ B
path here = hself
path (next p) = hsuc (path p)
path (first p) = hlim 0 (path p)

record LeadingCompletion : Set where
  field
    keep-completed : ∀ {a B} → Leading a B → Leading
      (OCF.Lean.CRw.leg a) (OCF.Lean.CRw.leg B)
```

BoundedHeightSimulation尚待完整构造或否定。LeadingCompletion将
实填原leg，并据此对原Γ证明全部左高度加法吸收；不以这部分
实例冒充一般有向高度比较。
