# YiXVReadWorldInput
> 验收文件。档位：编译定理。世界接口按同一实际全局根量化源坐标，槽位带任意有类型的原层间路径；零层、一层 B₀ 所有字段先实填。
> 保留原 h₁、lvl、B₀ 与折叠；初始化参照取 read(root) 的零前缀嵌入。未交原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadWorldInput where
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; 1≼ψ⁰; ≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableFoldInput as FQ
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVFlatInput as Flat
import OCF.Lean.YiXVRefLift as E
import OCF.Lean.YiXVRefAlgebra as R
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVLvlLiteral as Literal
import OCF.Lean.YiXVReadPaths as P
pc : ∀ {root y} → y P.≤ᵀ root → T.lvl y L.<ᴵ L.suc (T.lvl root)
pc P.here = L.zero
pc (P.below p) = L.suc (Literal.step (P.raw p))
φ : ∀ {root y} → y P.≤ᵀ root → L.Ordᶜ (T.lvl root) → L.Ordᶜ (T.lvl y)
φ p Z = L.ψ (pc p) (λ q → L.suc q) Z
φ-good : ∀ {root y} (p : y P.≤ᵀ root) {Z} → A.Gd Z → A.Gd (φ p Z)
φ-good {root} {y} p = FQ.Ops.good (F.ops (T.lvl root) (read-strong root))
  {ν = T.lvl y} {a = L.suc (T.lvl root)} (read-strong root) (pc p) (λ q → L.suc q)
seed : ∀ root → L.Ordᶜ (T.lvl root)
seed root = E.embedded (Flat.empty (T.lvl root)) (Read.read root)
seed-good : ∀ root → A.Gd (seed root)
seed-good root = E.embedded-good (G.good (Read.read root))
record World (root x : S.Tr S.zero) (within : x P.≤ᵀ root)
  (B : Fold.Base (J.ℓ x)) (Z : L.Ordᶜ (T.lvl root)) : Set where
  field
    good : A.Gd Z
    bot : Read.read (Fold.b⊥ B) ≼ L.ψ⁰ Z
    slots : ∀ y (p : y P.≤ᵀ root) (v : J.ℓ y Path.≤ J.ℓ x) →
      U.UR y (Fold.bs B (J.ℓ y) v) (φ p Z)

model₀ : World S.zero S.zero P.here (Fold.B₀ (J.ℓ S.zero)) (seed S.zero)
World.good model₀ = seed-good S.zero
World.bot model₀ = 1≼ψ⁰ (seed S.zero)
World.slots model₀ .S.zero P.here v = ≼-refl _
World.slots model₀ y (P.below ()) v
model₁ : World (S.suc S.zero) (S.suc S.zero) P.here
  (Fold.B₀ (J.ℓ (S.suc S.zero))) (seed (S.suc S.zero))
World.good model₁ = seed-good (S.suc S.zero)
World.bot model₁ = 1≼ψ⁰ (seed (S.suc S.zero))
World.slots model₁ .(S.suc S.zero) P.here v =
  B.weak (S.suc S.zero) (B.Ωsuc S.zero)
    (R.sum-ω (A.Layer.rfl (L.suc L.zero) A.Gd< A.Le< A.oneΩ)
      (A.Layer.rfl (L.suc L.zero) A.Gd< A.Le< A.oneΩ))
World.slots model₁ .S.zero (P.below P.root) v = 1≼ψ⁰ (seed (S.suc S.zero))
World.slots model₁ y (P.below (P.under-suc ())) v

model₁₀ : World (S.suc S.zero) S.zero (P.below P.root)
  (Fold.B₀ (J.ℓ S.zero)) (seed (S.suc S.zero))
World.good model₁₀ = World.good model₁
World.bot model₁₀ = World.bot model₁
World.slots model₁₀ y p v = World.slots model₁ y p (Path.ins v)
```
