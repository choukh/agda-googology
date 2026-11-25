# YiXVCountableChainInput
> 验收文件。档位：编译定理。带 Ω 地板的迭代接口；常 Ω 映射给所有层的完整实例。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableChainInput where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
record Input {κ} (P : L.Ordᶜ κ → L.Ordᶜ κ) : Set where
  field
    good : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Gd (P X)
    floor : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Le (L.Ω κ) (P X)
model : ∀ κ → Input (λ (_ : L.Ordᶜ κ) → L.Ω κ)
Input.good (model κ) X gx o = proj₁ (O.model κ)
Input.floor (model κ) X gx o = A.Layer.rfl κ A.Gd< A.Le< (proj₁ (O.model κ))
```
