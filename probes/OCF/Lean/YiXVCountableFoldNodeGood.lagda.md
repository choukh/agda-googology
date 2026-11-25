# YiXVCountableFoldNodeGood
> 验收文件。档位：编译定理。节点体接口推出原节点折叠辅助合法性；保留与对角两种计算分别验收。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldNodeGood where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; subst₂)
open import Data.Product using (proj₁; proj₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRetain as Retain
import OCF.Lean.YiXVCountableFoldBody as H
import OCF.Lean.YiXVCountableChainInput as CI
import OCF.Lean.YiXVCountableChain as Ch
import OCF.Lean.YiXVCountableFloor as Floor
import OCF.Lean.YiXVCountableIter as Iter
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVLiteralTri as Tri

module Node {κ i} (sκ : Strong κ) (q : i L.<ᴵ κ)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) (ex : L.limᵢ q f L.≅ L.limᵢ q f) (body : H.Body q f) where
  raw : L.Ordᶜ i → L.Ordᶜ κ
  raw X = f (L.into (L.<→◃ q) X)
  P : L.Ordᶜ i → L.Ordᶜ i
  P X = L.ψ q (λ r → r) (raw X)
  input : CI.Input P
  CI.Input.good input = H.Body.good body sκ q (λ r → r)
  CI.Input.floor input X gx o = Floor.floor q (λ r → r) (raw X) (H.Body.good body sκ q (λ r → r) X gx o)
  module Chain = Ch.Chain P input
  diagonal : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) →
    A.Gd (L.lim (λ n → L.ψ p σ (raw (Chain.d n))))
  diagonal sa p σ = A.Layer.gl (λ n → H.Body.good body sa p σ (Chain.d n) (Chain.good n) (Chain.floor n))

  module Keep {ν a j} (sa : Strong a) (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a)
    (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) (same : i ≡ j) where
    module D = A.Layer ν A.Gd< A.Le<
    pull = Retain.pull q r e same
    h : L.U j (L.<→◃ r) → L.Ordᶜ ν
    h u = L.ψ p σ (f (V.Pull.raw pull u))
    back = V.Pull.back pull
    at : ∀ X → h (L.into (L.<→◃ r) X) ≡ L.ψ p σ (raw (back X))
    at X = cong (λ u → L.ψ p σ (f u)) (V.Pull.input pull X)
    gback : ∀ X → D.GU r X → A.Gd (back X)
    gback X gx = V.Pull.good pull (A.good-out (L.<→◃ r) gx)
    fback : ∀ X → D.Floor r X → A.Le (L.Ω i) (back X)
    fback X o = V.Pull.floor pull (A.le-out (L.<→◃ r) o)
    mback : ∀ X Y → D.RU r X Y → A.Le (back X) (back Y)
    mback X Y t = V.Pull.mono pull (A.le-out (L.<→◃ r) t)
    good : ∀ X → D.GU r X → D.Floor r X → A.Gd (h (L.into (L.<→◃ r) X))
    good X gx o = subst A.Gd (sym (at X)) (H.Body.good body sa p σ (back X) (gback X gx) (fback X o))
    law : D.SC r h
    D.SC.mo law X Y gx gy o t = subst₂ A.Le (sym (at X)) (sym (at Y))
      (H.Body.mono body sa sa p p σ σ (back X) (back Y) (gback X gx) (gback Y gy) (fback X o) (mback X Y t))
    D.SC.db law X gx o = D.trans
      (Iter.strict p σ (f (V.Pull.raw pull (L.into (L.<→◃ r) X))) (good X gx o))
      (subst₂ A.Le (sym (cong (λ u → L.ψ p σ (L.suc (f u))) (V.Pull.input pull X)))
        (sym (at (L.suc X)))
        (subst (λ Y → A.Le (L.ψ p σ (L.suc (raw (back X)))) (L.ψ p σ (raw Y)))
          (sym (V.Pull.suc pull X))
          (H.Body.step body sa p σ (back X) (gback X gx) (fback X o))))
    D.SC.po law = D.trans (proj₂ (O.model ν))
      (Floor.floor p σ (f (V.Pull.raw pull (L.into (L.<→◃ r) (L.Ω j))))
        (good (L.Ω j) (A.good-in (L.<→◃ r) (proj₁ (O.model j)))
          (A.le-in (L.<→◃ r) (A.Layer.rfl j A.Gd< A.Le< (proj₁ (O.model j))))))
    result : L.limᵢ r h L.≅ L.limᵢ r h → A.Gd (L.limᵢ r h)
    result ex′ = D.gn ex′ law good

  keep-shape : ∀ {ν a j} (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a)
    (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) →
    L.<ᴵ-dec (σ q) p ≡ injᵃ (L.via e r) →
    L.ψ p σ (L.limᵢ q f) ≡ L.limᵢ r (λ u → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) u)))))
  keep-shape p σ r e eq with L.<ᴵ-dec (σ q) p
  ... | injᵃ v with eq
  ... | refl = refl
  keep-shape p σ r e eq | injᵇ w with eq
  ... | ()
  keep-shape p σ r e eq | injᶜ h with eq
  ... | ()

  result : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) → A.Gd (L.ψ p σ (L.limᵢ q f))
  result {ν} sa p σ with L.<ᴵ-dec (σ q) p in eq | Tri.tri sa (σ q) p
  ... | injᵃ (L.via e r) | same = Keep.result sa p σ r e same (subst₂ L._≅_ sh sh
      (L.ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (L.≅ᴵ-refl ν) ex))
    where sh = keep-shape p σ r e eq
  ... | injᵇ w | same = diagonal sa p σ
  ... | injᶜ e | same = diagonal sa p σ

import OCF.Lean.YiXVCountableFoldBody as Model
open import Data.Unit using (tt)
actual : A.Gd (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = Node.result tt L.zero (L.up L.zero) (L.Ω-≅ (L.s≅ L.z≅)) Model.model tt L.zero (λ q → L.suc q)
```
