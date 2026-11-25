# YiXVSourcePlus
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourcePlus where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiCeilRead using (plus≼)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteCanonicalInputs as N
import OCF.Lean.YiXVFiniteCompose as Assoc
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB

module Stage (n : ℕ) where
  module D = U.Layer n (U.UR n)
  module R = A.Layer n (A.GoFam n) (A.LeFam n)
  plus : ∀ {x X y Y} → A.Gd (suc n) X → D.U x X → A.Gd (suc n) Y → D.U y Y → D.U (O._+_ x y) (X L.+ Y)
  plus {X = X} gx hx gy D.uz = D.uw hx
    (Add.plus (suc n) {X = X} {X′ = X} {Y = L.zero} {Y′ = L.Ω (L.natᴵ (suc n))}
      (R.refl gx) (R.z≤ (proj₁ (B.Ω-model (suc n) F.zero))))
  plus gx hx (R.gs gy) (D.us hy) = D.us (plus gx hx gy hy)
  plus {X = X} gx hx gy (D.uw {X = Y} {Y = Y′} hy t) = D.uw (plus gx hx (R.left t) hy)
    (Add.plus (suc n) {X = X} {X′ = X} {Y = Y} {Y′ = Y′} (R.refl gx) t)
  plus gx hx gy (D.ul h) = D.ul (λ k → plus gx hx gy (h k))
  plus {x} {X} gx hx (R.gn law gb) (D.un i {g} {f} h) = D.un i (λ a V Y gv gy o ha t →
    subst (D.U (O._+_ x (g (J.inB n i a))))
      (sym (cong (λ u → X L.+ f u) (C.coe-id (J.q n i) (L.into (L.<→◃ (J.q n i)) Y))))
      (plus gx hx (gb (L.into (L.<→◃ (J.q n i)) Y)
        (N.At.good-in n (I.rank n i) (J.q n i) Y gy) (N.At.floor-in n (I.rank n i) (J.q n i) Y o))
        (h a V Y gv gy o ha t)))
  plus {X = X} gx hx gy (D.uu {X = Y} {Y = Z} gy₀ hy gz hz) = D.uw
    (D.uu (Add.plus-good (suc n) {X = X} {Y = Y} gx gy₀) (plus gx hx gy₀ hy) gz hz)
    (Assoc.assoc (suc n) n X Y (λ q → L.suc q) Z gx gy₀ gz)

plus : ∀ n {x X y Y} → A.Gd n X → U.U n x X → A.Gd n Y → U.U n y Y → U.U n (O._+_ x y) (X L.+ Y)
plus zero {x} {y = y} gx hx gy hy = plus≼ x y hx hy
plus (suc n) = Stage.plus n
```
