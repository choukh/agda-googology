# YiXVCountableFoldNodeAA
> 验收文件。档位：编译定理。Ω 起点的上界传到整节点；保留分支回搬地板，对角分支取第零项。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldNodeAA where
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRetain as R
import OCF.Lean.YiXVCountableFoldBody as H
import OCF.Lean.YiXVCountableFoldBound as Q
import OCF.Lean.YiXVCountableFoldNodeGood as G
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVLiteralTri as T
module Node {κ i} (sκ : Strong κ) (q : i L.<ᴵ κ) (X : L.Ordᶜ κ)
  (g : L.U i (L.<→◃ q) → L.Ordᶜ κ) (ex : L.limᵢ q g L.≅ L.limᵢ q g)
  (body : H.Body q g) (bound : Q.Bound q X g) where
  module B = G.Node sκ q g ex body
  module Run {ν a b} (sa : Strong a) (sb : Strong b) (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
    (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) where
    module D = A.Layer ν A.Gd< A.Le<
    step : D.Step (L.ψ p σ X) (L.ψ p′ τ (L.limᵢ q g))
    step with L.<ᴵ-dec (τ q) p′ | T.tri sb (τ q) p′
    ... | injᵃ (L.via {a′ = j} e r) | same = D.aa
      (subst (D.Le (L.ψ p σ X)) (sym (cong (λ u → L.ψ p′ τ (g u)) (V.Pull.input pull (L.Ω j))))
        (D.trans (Q.Bound.at bound sa sb p p′ σ τ)
          (H.Body.mono body sb sb p′ p′ τ τ (L.Ω i) (V.Pull.back pull (L.Ω j))
            (proj₁ (O.model i)) (V.Pull.good pull (proj₁ (O.model j)))
            (A.Layer.rfl i A.Gd< A.Le< (proj₁ (O.model i)))
            (V.Pull.floor pull (A.Layer.rfl j A.Gd< A.Le< (proj₁ (O.model j)))))))
      where pull = R.pull q r e same
    ... | injᵇ w | same = D.lr 0 (Q.Bound.at bound sa sb p p′ σ τ)
    ... | injᶜ e | same = D.lr 0 (Q.Bound.at bound sa sb p p′ σ τ)
    result : A.Gd (L.ψ p σ X) → A.Le (L.ψ p σ X) (L.ψ p′ τ (L.limᵢ q g))
    result gx = D.pack gx (B.result sb p′ τ) step

import OCF.Lean.YiXVCountableGroundFold as Ground
open import Data.Unit using (tt)
module Model = Node tt L.zero (L.suc L.zero) (L.up L.zero)
  (L.Ω-≅ (L.s≅ L.z≅)) H.model Q.model
actual : A.Le (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.suc (L.zero {ℓ = L.suc L.zero})))
  (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = Model.Run.result tt tt L.zero L.zero (λ q → L.suc q) (λ q → L.suc q)
  (Ground.good L.zero (λ ()) (L.suc L.zero))
```
