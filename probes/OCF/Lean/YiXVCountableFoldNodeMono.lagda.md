# YiXVCountableFoldNodeMono
> 验收文件。档位：编译定理。原节点折叠的混合单调性；保留分支复用公共映射比较。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldNodeMono where
open import Data.Empty using (⊥-elim)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapCompare as C
import OCF.Lean.YiXVCountableRetain as R
import OCF.Lean.YiXVCountableFoldBody as H
import OCF.Lean.YiXVCountableFoldCross as X
import OCF.Lean.YiXVCountableFoldNodeGood as G
import OCF.Lean.YiXVCountableChain as Ch
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVLiteralTri as T

module Node {κ i} (sκ : Strong κ) (q r : i L.<ᴵ κ)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) (g : L.U i (L.<→◃ r) → L.Ordᶜ κ)
  (ef : L.limᵢ q f L.≅ L.limᵢ q f) (eg : L.limᵢ r g L.≅ L.limᵢ r g)
  (bf : H.Body q f) (bg : H.Body r g) (h : X.Cross q r f g) where
  module F = G.Node sκ q f ef bf
  module B = G.Node sκ r g eg bg
  module Chain = Ch.Compare F.P B.P F.input B.input
    (X.Cross.mono h sκ sκ q r (λ t → t) (λ t → t))
  module Run {ν a b} (sa : Strong a) (sb : Strong b) (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
    (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) where
    module D = A.Layer ν A.Gd< A.Le<
    module Out = Chain.Lim (λ X → L.ψ p σ (F.raw X)) (λ X → L.ψ p′ τ (B.raw X))
      (H.Body.good bf sa p σ) (H.Body.good bg sb p′ τ)
      (X.Cross.mono h sa sb p p′ σ τ)
    proof : ∀ {Y Z} → D.Le Y Z → D.Step Y Z
    proof (D.pack gy hz t) = t
    step : D.Step (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ r g))
    step with L.<ᴵ-dec (σ q) p | L.<ᴵ-dec (τ r) p′ | T.tri sa (σ q) p | T.tri sb (τ r) p′
    ... | injᵃ (L.via e s) | injᵃ (L.via e′ t) | same | same′ =
      C.Map.compare (L.ψ p σ) (L.ψ p′ τ) q r f g
        (λ X Y gx gy o xy → X.Cross.mono h sa sb p p′ σ τ X Y
          (A.good-out (L.<→◃ q) gx) (A.good-out (L.<→◃ r) gy)
          (A.le-out (L.<→◃ q) o) (A.le-out (L.<→◃ q) xy))
        (R.pull q s e same) (R.pull r t e′ same′)
    ... | injᵃ v | injᵇ w | hv | hw = ⊥-elim (L.clash₁ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν) v w)
    ... | injᵃ v | injᶜ e | hv | he = ⊥-elim (L.clash₂ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν) v e)
    ... | injᵇ v | injᵃ w | hv | hw = ⊥-elim (L.clash₁ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν) w v)
    ... | injᶜ e | injᵃ w | he | hw = ⊥-elim (L.clash₂ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν) w e)
    ... | injᵇ v | injᵇ w | hv | hw = proof Out.result
    ... | injᵇ v | injᶜ e | hv | he = proof Out.result
    ... | injᶜ e | injᵇ w | he | hw = proof Out.result
    ... | injᶜ e | injᶜ e′ | he | he′ = proof Out.result
    result : A.Le (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ r g))
    result = D.pack (F.result sa p σ) (B.result sb p′ τ) step

open import Data.Unit using (tt)
module Model = Node tt L.zero L.zero (L.up L.zero) (L.up L.zero)
  (L.Ω-≅ (L.s≅ L.z≅)) (L.Ω-≅ (L.s≅ L.z≅)) H.model H.model X.model
actual : A.Le (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
  (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = Model.Run.result tt tt L.zero L.zero (λ q → L.suc q) (λ q → L.suc q)
```
