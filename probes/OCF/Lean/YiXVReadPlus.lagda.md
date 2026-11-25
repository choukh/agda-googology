# YiXVReadPlus
> 验收文件。档位：编译定理。实际源层上的加法模拟保持；节点输入沿原 into/out 逐点归一。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadPlus where
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiCeilRead using (plus≼)
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as Frame
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadAssoc as Assoc

model-zero : U.UR (S.suc S.zero) (O._+_ S.zero S.zero)
  (L.Ω (L.suc L.zero) L.+ L.Ω (L.suc L.zero))
model-zero = B.weak (S.suc S.zero) (B.zero (S.suc S.zero))
  (Add.right A.oneΩ A.oneΩ)
model-suc : U.UR (S.suc S.zero)
  (O._+_ (O.Ωt (J.ℓ (S.suc S.zero))) (S.suc S.zero))
  ((L.Ω (L.suc L.zero) L.+ L.Ω (L.suc L.zero)) L.+ L.suc L.zero)
model-suc = B.sucU (S.suc S.zero) B.actual

module Stage (r : S.Tr S.zero) where
  module D = U.Layer r (U.Fam r)
  module R = A.Layer (T.lvl r) A.Gd< A.Le<
  plus : ∀ {x X y Y} → A.Gd X → D.U x X → A.Gd Y → D.U y Y →
    D.U (O._+_ x y) (X L.+ Y)
  plus {X = X} gx hx gy D.uz = D.uw hx (Add.right gx gy)
  plus gx hx (R.gs gy) (D.us hy) = D.us (plus gx hx gy hy)
  plus {X = X} gx hx gy (D.uw hy t) = D.uw (plus gx hx (R.left t) hy)
    (Frame.mixed (R.rfl gx) t)
  plus gx hx gy (D.ul h) = D.ul (λ n → plus gx hx gy (h n))
  plus {x} {X} gx hx (R.gn ex law gb) (D.un p {g} {f} h) = D.un p
    (λ a V Y gv gy o ha t → subst (D.U (O._+_ x (g a)))
      (sym (cong (λ u → X L.+ f u)
        (cong (L.into (L.<→◃ (J.q r p))) (L.out-into (L.<→◃ (J.q r p)) Y))))
      (plus gx hx (gb Y (A.good-in (L.<→◃ (J.q r p)) gy)
        (A.le-in (L.<→◃ (J.q r p)) o)) (h a V Y gv gy o ha t)))
  plus {X = X} gx hx gy (D.uu c {X = Y} {Y = Z} gy₀ hy gZ hZ) = D.uw
    (D.uu c (Add.good gx gy₀) (plus gx hx gy₀ hy) gZ hZ)
    (Assoc.bound {σ = λ q → q} {τ = J.σchild r c} gx gy₀ gZ)

plus : ∀ r {x X y Y} → A.Gd X → U.UR r x X → A.Gd Y → U.UR r y Y →
  U.UR r (O._+_ x y) (X L.+ Y)
plus S.zero {x} {y = y} gx hx gy hy = plus≼ x y hx hy
plus (S.suc r) = Stage.plus (S.suc r)
plus (S.lim f d) = Stage.plus (S.lim f d)
plus (S.Ω () g)
plus (S.up r () y e)
```
