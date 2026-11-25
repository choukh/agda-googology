# YiXVReadGrowthInput
> 验收文件。档位：编译定理。增长、输出与源回灌接口，复用 CountableChainInput，含非零输出完整模型。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadGrowthInput where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableGamma as Gamma
import OCF.Lean.YiXVCountableIter as It
import OCF.Lean.YiXVCountableFloor as Floor
import OCF.Lean.YiXVCountableChainInput as CI
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
open import OCF.Lean.YiXVLvlSteps using (read-strong)
ω : ∀ {κ} → L.Ordᶜ κ → L.Ordᶜ κ
ω X = L.lim (iter (X L.+_) L.zero)
record Growth {κ} (P : L.Ordᶜ κ → L.Ordᶜ κ) : Set where
  field
    input : CI.Input P
  open CI.Input input public
  field
    mono : ∀ X Y → A.Gd X → A.Gd Y → A.Le (L.Ω κ) X → A.Le X Y → A.Le (P X) (P Y)
    db : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Le (ω (P X)) (P (L.suc X))
    initial : A.Le (L.suc (L.Ω κ)) (P (L.Ω κ))
record Output {κ ν} (η : L.Ordᶜ κ → L.Ordᶜ ν) : Set where
  field
    good : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Gd (η X)
    mono : ∀ X Y → A.Gd X → A.Gd Y → A.Le (L.Ω κ) X → A.Le X Y → A.Le (η X) (η Y)
    db : ∀ X → A.Gd X → A.Le (L.Ω κ) X → A.Le (ω (η X)) (η (L.suc X))
record SourceStep (r : S.Tr S.zero) (P : L.Ordᶜ (T.lvl r) → L.Ordᶜ (T.lvl r))
  (g : S.Tr (J.ℓ r) → S.Tr (J.ℓ r)) : Set where
  field
    step : ∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl r)) Y →
      U.UR r a X → A.Le (L.suc X) Y → U.UR r (g a) (P Y)
record Orbit (r : S.Tr S.zero) (g : S.Tr (J.ℓ r) → S.Tr (J.ℓ r)) : Set where
  field
    points : ℕ → S.Tr (J.ℓ r)
    start : points zero ≡ S.zero
    next : ∀ n → points (suc n) ≡ g (points n)
iter-orbit : ∀ r g → Orbit r g
Orbit.points (iter-orbit r g) = O.iter g S.zero
Orbit.start (iter-orbit r g) = refl
Orbit.next (iter-orbit r g) n = refl

module Model (r : S.Tr S.zero) where
  κ = T.lvl r
  module D = A.Layer κ A.Gd< A.Le<
  module Γ = Gamma.At κ (read-strong r)
  P : L.Ordᶜ κ → L.Ordᶜ κ
  P X = Γ.Ψ (L.Ω κ L.+ X)
  gp : ∀ X → A.Gd X → A.Gd (P X)
  gp X gx = Γ.ψ-good (Add.good {σ = λ q → q} (proj₁ (Ω.model κ)) gx)
  mp : ∀ {X Y} → A.Le X Y → A.Le (P X) (P Y)
  mp t = Γ.ψ-mono (Add.mono {σ = λ q → q} (proj₁ (Ω.model κ)) t)
  growth : Growth P
  CI.Input.good (Growth.input growth) X gx o = gp X gx
  CI.Input.floor (Growth.input growth) X gx o = Floor.floor L.zero (λ q → L.suc q) (L.Ω κ L.+ X) (gp X gx)
  Growth.mono growth X Y gx gy o t = mp t
  Growth.db growth X gx o = D.rfl (D.gl (It.good (P X) (gp X gx)))
  Growth.initial growth = D.trans Γ.inv-Ω (Γ.ψ-mono
    (Add.right {σ = λ q → q} (proj₁ (Ω.model κ)) (proj₁ (Ω.model κ))))
  output : Output P
  Output.good output = Growth.good growth
  Output.mono output = Growth.mono growth
  Output.db output = Growth.db growth
  g : S.Tr (J.ℓ r) → S.Tr (J.ℓ r)
  g a = S.zero
  source : SourceStep r P g
  SourceStep.step source a X Y gx gy o ha t = B.weak r (B.zero r) (Growth.floor growth Y gy o)
  orbit : Orbit r g
  orbit = iter-orbit r g
  F : ℕ → S.Tr (J.ℓ r)
  F n = S.suc S.zero
  nz : ∀ n → J.ℓ r S.⊢ S.zero ◃ F n
  nz n = S.◃s
  row : ∀ n a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω κ) Y →
    U.UR r a X → A.Le (L.suc X) Y → U.UR r (F n) (P Y)
  row n a X Y gx gy o ha t = B.weak r (B.sucU r (B.zero r))
    (D.trans (Growth.initial growth)
      (Growth.mono growth (L.Ω κ) Y (proj₁ (Ω.model κ)) gy
        (D.rfl (proj₁ (Ω.model κ))) o))
```
