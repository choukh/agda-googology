# YiXVCountableFoldBound
> 验收文件。档位：编译定理。从 Ω 起点的折叠上界接口，含后继零与原一层 Ω 的完整实例。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldBound where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableGroundFold as G
record Bound {κ i} (q : i L.<ᴵ κ) (X : L.Ordᶜ κ) (g : L.U i (L.<→◃ q) → L.Ordᶜ κ) : Set₁ where
  field
    at : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) →
      A.Le (L.ψ p σ X) (L.ψ p′ τ (g (L.into (L.<→◃ q) (L.Ω i))))
model : Bound (L.zero {a = L.zero}) (L.suc L.zero) (L.up L.zero)
Bound.at model {ν} sa sb p p′ σ τ = A.Layer.rfl ν A.Gd< A.Le< (G.good p′ (λ q → τ (L.suc q)) (L.suc L.zero))
```
