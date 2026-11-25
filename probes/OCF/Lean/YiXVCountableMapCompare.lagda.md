# YiXVCountableMapCompare
> 验收文件。档位：编译定理。两节点有同一原下标时，接口把节点比较送到同一目标。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableMapCompare where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst₂)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableMapNode as Model

module Map {κ ν} (φ χ : L.Ordᶜ κ → L.Ordᶜ ν) where
  module S = A.Layer κ A.Gd< A.Le<
  module D = A.Layer ν A.Gd< A.Le<

  compare : ∀ {i} (q r : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) (g : L.U i (L.<→◃ r) → L.Ordᶜ κ) →
    (∀ X Y → S.GU q X → S.GU r Y → S.Floor q X → S.RU q X Y →
      A.Le (φ (f (L.into (L.<→◃ q) X))) (χ (g (L.into (L.<→◃ r) Y)))) →
    (p : V.Pull {κ} {ν} q) (p′ : V.Pull {κ} {ν} r) →
    D.Step (L.limᵢ (V.Pull.bound p) (λ u → φ (f (V.Pull.raw p u))))
      (L.limᵢ (V.Pull.bound p′) (λ u → χ (g (V.Pull.raw p′ u))))
  compare {i} q r f g h
    (V.pull j q′ eqQ rawQ backQ inQ goodQ monoQ floorQ sucQ trQ)
    (V.pull k r′ eqR rawR backR inR goodR monoR floorR sucR trR) with trans (sym eqQ) eqR
  ... | refl = D.nn (λ X Y gx gy o t → subst₂ (A.Le {κ = ν})
    (sym (cong (λ u → φ (f u)) (inQ X))) (sym (cong (λ u → χ (g u)) (inR Y)))
    (h (backQ X) (backR Y)
      (A.good-in (L.<→◃ q) (goodQ (A.good-out (L.<→◃ q′) gx)))
      (A.good-in (L.<→◃ r) (goodR (A.good-out (L.<→◃ r′) gy)))
      (A.le-in (L.<→◃ q) (floorQ (A.le-out (L.<→◃ q′) o)))
      (A.le-in (L.<→◃ q) (A.Layer.trans i A.Gd< A.Le< (monoQ (A.le-out (L.<→◃ q′) t))
        (A.Layer.pack (goodQ (A.good-out (L.<→◃ r′) gy)) (goodR (A.good-out (L.<→◃ r′) gy))
          (A.Layer.ce (L.≅-trans (trQ (A.good-out (L.<→◃ r′) gy)) (L.≅-sym (trR (A.good-out (L.<→◃ r′) gy))))))))))

  result : (view : V.View κ ν φ) (view′ : V.View κ ν χ) → ∀ {i} (q r : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) (g : L.U i (L.<→◃ r) → L.Ordᶜ κ) →
    (∀ X Y → S.GU q X → S.GU r Y → S.Floor q X → S.RU q X Y →
      A.Le (φ (f (L.into (L.<→◃ q) X))) (χ (g (L.into (L.<→◃ r) Y)))) →
    D.Step (φ (L.limᵢ q f)) (χ (L.limᵢ r g))
  result view view′ q r f g h = subst₂ D.Step
    (sym (V.View.node-shape view q f)) (sym (V.View.node-shape view′ r g))
    (compare q r f g h (V.View.node view q) (V.View.node view′ r))

module Actual = Map (λ (X : L.Ordᶜ (L.suc L.zero)) → X) (λ X → X)
actual : A.Layer.Step (L.suc L.zero) A.Gd< A.Le< (L.Ω (L.suc L.zero)) (L.Ω (L.suc L.zero))
actual = Actual.result (V.identity (L.suc L.zero)) (V.identity (L.suc L.zero)) L.zero L.zero (L.up L.zero) (L.up L.zero) (Model.Model.D.SC.mo Model.Model.law)
```
