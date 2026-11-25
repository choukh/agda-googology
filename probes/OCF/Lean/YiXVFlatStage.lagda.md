# YiXVFlatStage
> 验收文件。档位：编译定理。固定源层，复用公共节点比较，给两个有界目标层的比较阶段。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFlatStage where
open import Relation.Binary.PropositionalEquality using (subst₂; sym)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapCompare as C
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVRefLift as E
import OCF.Lean.YiXVRefAlgebra as R
import OCF.Lean.YiXVFlatInput as Q
import OCF.Lean.YiXVFlatShape as Shape
import OCF.Lean.YiXVFlatGround as G
module Stage (κ : L.Ordᴵ) (sκ : Strong κ) (lower : ∀ {i} → i L.◃₁ κ → Q.Ops i) where
  module S = A.Layer κ A.Gd< A.Le<
  mutual
    compare : ∀ {a b} → Strong a → Strong b → (r : a L.<ᴵ b)
      (ρ : L.Simᴵ a b) (ξ : L.Simᴵ κ a) (ζ : L.Simᴵ κ b) → ∀ {X} → S.Gd X →
      A.Le (E.embedded ρ (Q.flat a ξ X)) (Q.flat b ζ X)
    compare sa sb r ρ ξ ζ S.gz = E.embedded-Ω (L.<→◃ r) ρ
    compare sa sb r ρ ξ ζ (S.gs {X} gx) = R.lim-mono
      (R.map-iter ρ (Q.good sκ sa ξ gx) (compare sa sb r ρ ξ ζ gx))
    compare sa sb r ρ ξ ζ (S.gl gf) = R.lim-mono (λ n → compare sa sb r ρ ξ ζ (gf n))
    compare {a} {b} sa sb r ρ ξ ζ h@(S.gn {q = q} {f = f} ex (S.sc mo db po) gb) =
      A.Layer.pack (E.embedded-good (Q.good sκ sa ξ h)) (Q.good sκ sb ζ h)
        (subst₂ (A.Layer.Step b A.Gd< A.Le<) (sym (Shape.node-left q ρ ξ f)) (sym (Shape.node-right q ζ f))
          (C.Map.compare (λ X → E.embedded ρ (Q.flat a ξ X)) (Q.flat b ζ) q q f f
            (λ X Y gx gy o t → mixed sa sb r ρ ξ ζ (mo X Y gx gy o t))
            (Shape.left q ρ ξ) (Shape.right q ζ)))
    compare sa sb r ρ ξ ζ (S.gu L.zero gx) =
      Q.Ops.compare (lower L.zero) sa sb r ρ (λ q → ξ (L.suc q)) (λ q → ζ (L.suc q)) gx
    compare sa sb r ρ ξ ζ (S.gu (L.self n) gx) =
      Q.Ops.compare (lower (L.self n)) sa sb r ρ (λ q → ξ (L.lim n q)) (λ q → ζ (L.lim n q)) gx
    mixed : ∀ {a b} → Strong a → Strong b → (r : a L.<ᴵ b)
      (ρ : L.Simᴵ a b) (ξ : L.Simᴵ κ a) (ζ : L.Simᴵ κ b) → ∀ {X Y} → S.Le X Y →
      A.Le (E.embedded ρ (Q.flat a ξ X)) (Q.flat b ζ Y)
    mixed {b = b} sa sb r ρ ξ ζ t@(S.pack gx gy p) = A.Layer.trans b A.Gd< A.Le<
      (E.embedded-mono {σ = ρ} (Q.mono sκ sa ξ ξ t)) (compare sa sb r ρ ξ ζ gy)
  result : Q.Ops κ
  Q.Ops.compare result = compare
open import Data.Unit using (tt)
module Model = Stage (L.suc L.zero) tt (λ { L.zero → G.ops })
actual : A.Le (E.embedded (λ q → L.suc q) (Q.flat (L.suc L.zero) (λ q → q) (L.Ω (L.suc L.zero))))
  (Q.flat (L.suc (L.suc L.zero)) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = Q.Ops.compare Model.result tt tt L.zero (λ q → L.suc q) (λ q → q) (λ q → L.suc q) A.oneΩ
```
