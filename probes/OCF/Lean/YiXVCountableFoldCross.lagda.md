# YiXVCountableFoldCross
> 验收文件。档位：编译定理。两节点体的混合比较接口，含原一层 Ω 的完整实例。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldCross where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableGroundFold as G
open import OCF.Lean.YiXVLvlSteps using (Strong)
record Cross {κ i} (q r : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ)
  (g : L.U i (L.<→◃ r) → L.Ordᶜ κ) : Set₁ where
  field
    mono : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) → ∀ X Y →
      A.Gd X → A.Gd Y → A.Le (L.Ω i) X → A.Le X Y →
      A.Le (L.ψ p σ (f (L.into (L.<→◃ q) X))) (L.ψ p′ τ (g (L.into (L.<→◃ r) Y)))
model : Cross (L.zero {a = L.zero}) L.zero (L.up L.zero) (L.up L.zero)
Cross.mono model sa sb p p′ σ τ X Y gx gy o t = G.M.mono _ p p′ (λ q → σ (L.suc q)) (λ q → τ (L.suc q)) t
```
