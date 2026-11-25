# YiXVReadNodeGrowthInput
> 验收文件。档位：编译定理。参照节点的 SC 与分支合法性投影，含规范一层节点完整实例。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadNodeGrowthInput where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadAffineNodeModels as M
module D = A.Layer (L.suc L.zero) A.Gd< A.Le<
law-of : ∀ {κ i} {q : i L.<ᴵ κ} {f} → A.Gd (L.limᵢ q f) → A.Layer.SC κ A.Gd< A.Le< q f
law-of (A.Layer.gn ex law gb) = law
body-of : ∀ {κ i} {q : i L.<ᴵ κ} {f} → A.Gd (L.limᵢ q f) →
  ∀ X → A.Layer.GU κ A.Gd< A.Le< q X → A.Layer.Floor κ A.Gd< A.Le< q X →
  A.Gd (f (L.into (L.<→◃ q) X))
body-of (A.Layer.gn ex law gb) = gb
law : D.SC L.zero M.f
law = law-of M.good
body : ∀ Y → D.GU L.zero Y → D.Floor L.zero Y → A.Gd (M.f Y)
body = body-of M.good
```
