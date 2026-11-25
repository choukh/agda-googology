# YiXVCountableFoldBody
> 验收文件。档位：编译定理。节点体的折叠接口及原一层 Ω 节点的完整实例。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldBody where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableGroundFold as G
record Body {κ i} (q : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) : Set₁ where
  field
    good : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) →
      ∀ X → A.Gd X → A.Le (L.Ω i) X → A.Gd (L.ψ p σ (f (L.into (L.<→◃ q) X)))
    mono : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) → ∀ X Y →
      A.Gd X → A.Gd Y → A.Le (L.Ω i) X → A.Le X Y →
      A.Le (L.ψ p σ (f (L.into (L.<→◃ q) X))) (L.ψ p′ τ (f (L.into (L.<→◃ q) Y)))
    step : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) →
      ∀ X → A.Gd X → A.Le (L.Ω i) X →
      A.Le (L.ψ p σ (L.suc (f (L.into (L.<→◃ q) X)))) (L.ψ p σ (f (L.into (L.<→◃ q) (L.suc X))))
model : Body (L.zero {a = L.zero}) (L.up L.zero)
Body.good model sa p σ X gx o = G.good p (λ q → σ (L.suc q)) X
Body.mono model sa sb p p′ σ τ X Y gx gy o t = G.M.mono _ p p′ (λ q → σ (L.suc q)) (λ q → τ (L.suc q)) t
Body.step model {ν} sa p σ X gx o = A.Layer.rfl ν A.Gd< A.Le< (G.good p (λ q → σ (L.suc q)) (L.suc X))
```
