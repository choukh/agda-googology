# YiXVCountableFoldInput
> 验收文件。档位：编译定理。折叠接口只在带 Strong 公共上界的域中量化。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldInput where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
open import OCF.Lean.YiXVLvlSteps using (Strong)
record Ops (κ : L.Ordᴵ) : Set₁ where
  field
    good : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) → ∀ {X} →
      A.Gd X → A.Gd (L.ψ p σ X)
    mono : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) → ∀ {X Y} →
      A.Le X Y → A.Le (L.ψ p σ X) (L.ψ p′ τ Y)
```
