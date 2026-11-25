# YiXVCountableFoldOmega
> 验收文件。档位：编译定理。原 Ω 的折叠不小于两份目标 Ω；通过一不大于 Ω 推出。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldOmega where
open import Data.Product using (proj₁; proj₂)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableAdd as Add
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVCountableIter as I
two : ∀ {κ ν a} → Strong κ → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) →
  A.Le (L.Ω ν L.+ L.Ω ν) (L.ψ p σ (L.Ω κ))
two {κ} {ν} sκ sa p σ = D.trans first (Q.Ops.mono (F.ops κ sκ) sa sa p p σ σ (proj₂ (O.model κ)))
  where
  module D = A.Layer ν A.Gd< A.Le<
  gΩ = proj₁ (O.model ν)
  g2 = Add.good {σ = λ q → q} gΩ gΩ
  first : A.Le (L.Ω ν L.+ L.Ω ν) (L.ψ p σ (L.suc (L.zero {ℓ = κ})))
  first = D.pack g2 (D.gl (I.good (L.Ω ν) gΩ)) (D.lr 2 (D.rfl g2))
actual : A.Le (L.Ω L.ωᴵ L.+ L.Ω L.ωᴵ) (L.ψ (L.zero {a = L.ωᴵ}) (λ q → L.suc q) (L.Ω L.ωᴵ))
actual = two F.ω-strong F.ω-strong L.zero (λ q → L.suc q)
```
