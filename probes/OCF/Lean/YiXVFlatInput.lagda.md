# YiXVFlatInput
> 验收文件。档位：编译定理。flat 仅为原 ψ 的特定参数；接口在两个 Strong 目标层的显式字面界内比较。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFlatInput where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableFold as Fold
import OCF.Lean.YiXVCountableFoldInput as F
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVRefLift as E
empty : ∀ ν → L.Simᴵ L.zero ν
empty ν ()
insert : ∀ {κ ν} → L.Simᴵ κ ν → L.Simᴵ κ (L.suc ν)
insert σ q = L.suc (σ q)
flat : ∀ {κ} (ν : L.Ordᴵ) → L.Simᴵ κ ν → L.Ordᶜ κ → L.Ordᶜ ν
flat ν σ X = L.ψ (L.zero {a = ν}) (insert σ) X
good : ∀ {κ ν} → Strong κ → Strong ν → (σ : L.Simᴵ κ ν) → ∀ {X} → A.Gd X → A.Gd (flat ν σ X)
good {κ} {ν} sκ sν σ = F.Ops.good (Fold.ops κ sκ) {ν = ν} {a = L.suc ν} sν L.zero (λ q → L.suc (σ q))
record Ops (κ : L.Ordᴵ) : Set₁ where
  field
    compare : ∀ {a b} → Strong a → Strong b → (r : a L.<ᴵ b)
      (ρ : L.Simᴵ a b) (ξ : L.Simᴵ κ a) (ζ : L.Simᴵ κ b) → ∀ {X} → A.Gd X →
      A.Le (E.embedded ρ (flat a ξ X)) (flat b ζ X)

mono : ∀ {κ ν} → Strong κ → Strong ν → (ξ ζ : L.Simᴵ κ ν) → ∀ {X Y} →
  A.Le X Y → A.Le (flat ν ξ X) (flat ν ζ Y)
mono {κ} {ν} sκ sν ξ ζ = F.Ops.mono (Fold.ops κ sκ) {ν = ν} {a = L.suc ν} {b = L.suc ν}
  sν sν L.zero L.zero (λ q → L.suc (ξ q)) (λ q → L.suc (ζ q))
```
