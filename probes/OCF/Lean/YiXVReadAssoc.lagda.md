# YiXVReadAssoc
> 验收文件。档位：编译定理。任意层上参照加法的结合律，按 PER 递归；给出辅助比较的包装。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAssoc where
open import Relation.Binary.PropositionalEquality using (sym; trans; subst₂)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVNeutral as N

Ω = L.Ω (L.suc L.zero)
model-node : L.add (L.add L.zero (λ q → q) L.zero) (λ q → q) Ω L.≅
  L.add L.zero (λ q → q) (L.add L.zero (λ q → q) Ω)
model-node = L.≅-trans (N.neutral L.z≅ (L.Ω-≅ (L.s≅ L.z≅)))
  (L.≅-sym (N.neutral L.z≅ (N.neutral L.z≅ (L.Ω-≅ (L.s≅ L.z≅)))))
model-successor : L.add (L.add Ω (λ q → q) Ω) (λ ()) (L.suc (L.zero {ℓ = L.zero})) L.≅
  L.add Ω (λ q → q) (L.add Ω (λ ()) (L.suc (L.zero {ℓ = L.zero})))
model-successor = L.s≅ (A.self (Add.good {σ = λ q → q} A.oneΩ A.oneΩ))

assoc : ∀ {ν κ ι ι′} {X : L.Ordᶜ ν} {Y : L.Ordᶜ κ}
  {Z : L.Ordᶜ ι} {Z′ : L.Ordᶜ ι′} {σ : L.Simᴵ κ ν}
  {τ : L.Simᴵ ι κ} {τ′ : L.Simᴵ ι′ κ} →
  X L.≅ X → Y L.≅ Y → Z L.≅ Z′ →
  L.add (L.add X σ Y) (λ q → σ (τ q)) Z L.≅ L.add X σ (L.add Y τ′ Z′)
assoc ex ey L.z≅ = L.add-≅ ex ey
assoc ex ey (L.s≅ e) = L.s≅ (assoc ex ey e)
assoc ex ey (L.l≅ h) = L.l≅ (λ n → assoc ex ey (h n))
assoc {σ = σ} {τ = τ} ex ey (L.upˡ {r = L.zero} h) =
  assoc {σ = σ} {τ = λ q → τ (L.suc q)} ex ey h
assoc {σ = σ} {τ = τ} ex ey (L.upˡ {r = L.self n} h) =
  assoc {σ = σ} {τ = λ q → τ (L.lim n q)} ex ey h
assoc {τ′ = τ′} ex ey (L.upʳ {r = L.zero} h) =
  assoc {τ′ = λ q → τ′ (L.suc q)} ex ey h
assoc {τ′ = τ′} ex ey (L.upʳ {r = L.self n} h) =
  assoc {τ′ = λ q → τ′ (L.lim n q)} ex ey h
assoc {X = X} {Y = Y} {σ = σ} {τ = τ} {τ′ = τ′} ex ey
  (L.lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = L.lᵢ≅ e λ u v d →
  subst₂ (λ a b → L.add (L.add X σ Y) (λ r → σ (τ r)) (f (L.into (L.<→◃ q) a))
    L.≅ L.add X σ (L.add Y τ′ (g (L.into (L.<→◃ q′) b))))
    (sym (L.out-into (L.<→◃ (σ (τ q))) u))
    (sym (trans (L.out-into (L.<→◃ (τ′ q′))
      (L.out (L.<→◃ (σ (τ′ q′))) (L.into (L.<→◃ (σ (τ′ q′))) v)))
      (L.out-into (L.<→◃ (σ (τ′ q′))) v)))
    (assoc ex ey (h u v (L.R-conv (L.<→◃ (σ (τ q))) (L.<→◃ q) d)))

bound : ∀ {ν κ ι} {X : L.Ordᶜ ν} {Y : L.Ordᶜ κ} {Z : L.Ordᶜ ι}
  {σ : L.Simᴵ κ ν} {τ : L.Simᴵ ι κ} → A.Gd X → A.Gd Y → A.Gd Z →
  A.Le (L.add (L.add X σ Y) (λ q → σ (τ q)) Z) (L.add X σ (L.add Y τ Z))
bound {σ = σ} {τ = τ} gx gy gZ = A.Layer.pack
  (Add.good (Add.good {σ = σ} gx gy) gZ) (Add.good gx (Add.good {σ = τ} gy gZ))
  (A.Layer.ce (assoc (A.self gx) (A.self gy) (A.self gZ)))
```
