# YiXVCountableAdd
> 验收文件。档位：编译定理。所有原层号上，加法保持辅助合法性与右变量比较，前缀不大于加法结果。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableAdd where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableMap as Map

pull : ∀ {κ ν i} (σ : L.Simᴵ κ ν) (q : i L.<ᴵ κ) → V.Pull {κ} {ν} q
pull {i = i} σ q = record
  { index = i ; bound = σ q ; same = refl
  ; raw = L.coe (L.<→◃ (σ q)) (L.<→◃ q)
  ; back = λ X → X
  ; input = λ X → cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ (σ q)) X)
  ; good = λ gx → gx ; mono = λ t → t ; floor = λ t → t
  ; suc = λ X → refl ; transparent = A.self }

mutual
  view : ∀ {κ ν} (Z : L.Ordᶜ ν) (σ : L.Simᴵ κ ν) → A.Gd Z → V.View κ ν (L.add Z σ)
  view Z σ hZ = record
    { zero = hZ ; suc = λ X → refl ; lim = λ f → refl
    ; node = pull σ ; node-shape = λ q f → refl
    ; up = child Z σ hZ ; up-shape = shape Z σ hZ
    ; cong = L.add-≅ (A.self hZ) }

  child : ∀ {κ ν i} (Z : L.Ordᶜ ν) (σ : L.Simᴵ κ ν) (hZ : A.Gd Z)
    (r : i L.◃₁ κ) → V.Child {κ} {ν} r Z
  child Z σ hZ L.zero = record
    { map = L.add Z (λ q → σ (L.suc q))
    ; good = Map.Map.good (L.add Z (λ q → σ (L.suc q))) (view Z (λ q → σ (L.suc q)) hZ)
    ; mono = Map.Map.mono (L.add Z (λ q → σ (L.suc q))) (view Z (λ q → σ (L.suc q)) hZ)
    ; right = Map.Map.right (L.add Z (λ q → σ (L.suc q))) (view Z (λ q → σ (L.suc q)) hZ) }
  child Z σ hZ (L.self n) = record
    { map = L.add Z (λ q → σ (L.lim n q))
    ; good = Map.Map.good (L.add Z (λ q → σ (L.lim n q))) (view Z (λ q → σ (L.lim n q)) hZ)
    ; mono = Map.Map.mono (L.add Z (λ q → σ (L.lim n q))) (view Z (λ q → σ (L.lim n q)) hZ)
    ; right = Map.Map.right (L.add Z (λ q → σ (L.lim n q))) (view Z (λ q → σ (L.lim n q)) hZ) }

  shape : ∀ {κ ν i} (Z : L.Ordᶜ ν) (σ : L.Simᴵ κ ν) (hZ : A.Gd Z)
    (r : i L.◃₁ κ) X → L.add Z σ (A.Up r X) ≡ V.Child.map (child Z σ hZ r) X
  shape Z σ hZ L.zero X = refl
  shape Z σ hZ (L.self n) X = refl

good : ∀ {κ ν} {Z : L.Ordᶜ ν} {σ : L.Simᴵ κ ν} {X} → A.Gd Z → A.Gd X → A.Gd (L.add Z σ X)
good {Z = Z} {σ} hZ = Map.Map.good (L.add Z σ) (view Z σ hZ)
mono : ∀ {κ ν} {Z : L.Ordᶜ ν} {σ : L.Simᴵ κ ν} {X Y} → A.Gd Z → A.Le X Y → A.Le (L.add Z σ X) (L.add Z σ Y)
mono {Z = Z} {σ} hZ = Map.Map.mono (L.add Z σ) (view Z σ hZ)
right : ∀ {κ ν} {Z : L.Ordᶜ ν} {σ : L.Simᴵ κ ν} {X} → A.Gd Z → A.Gd X → A.Le Z (L.add Z σ X)
right {Z = Z} {σ} hZ = Map.Map.right (L.add Z σ) (view Z σ hZ)

actual : A.Gd (L.Ω L.ωᴵ L.+ L.Ω L.ωᴵ)
actual = good A.omegaΩ A.omegaΩ
```
