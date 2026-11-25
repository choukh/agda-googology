# YiXVReadAffineNode
> 验收文件。档位：编译定理。公共下降路径上的仿射节点模拟；保持节点的任意源映射共享同一接口。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineNode where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRetain as Retain
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadSlots as Slots
import OCF.Lean.YiXVReadKeepAt as Keep
import OCF.Lean.YiXVReadAffineNodeModels as Model

module Node {root top cur} (within : top P.≤ᵀ root) (d : Down.Down top cur)
  (p : S.Pos (J.ℓ cur)) (x : S.Tr (J.ℓ top)) (nx : J.ℓ top S.⊢ S.zero ◃ x)
  (X : L.Ordᶜ (T.lvl root)) (σ : L.Simᴵ (T.lvl cur) (T.lvl root)) (gx : A.Gd X)
  (g : S.Br (J.ℓ cur) p → S.Tr (J.ℓ cur))
  (f : L.U (T.lvl (J.slot cur p)) (L.<→◃ (J.q cur p)) → L.Ordᶜ (T.lvl cur))
  (gnode : A.Gd (L.limᵢ (J.q cur p) f)) where
  module C = Phi.Frame within
  pos = O.mv (Down.src d) p
  q = J.q cur p
  qr = σ q
  qt = J.q top pos
  same-slot = Down.slot d p
  same : T.lvl (J.slot cur p) ≡ T.lvl (J.slot top pos)
  same = sym (cong T.lvl same-slot)
  eq : T.lvl (J.slot cur p) L.≅ᴵ T.lvl (J.slot top pos)
  eq = subst (λ j → T.lvl (J.slot cur p) L.≅ᴵ j) same (L.≅ᴵ-refl (T.lvl (J.slot cur p)))
  pull = Retain.pull qr qt eq same
  back = V.Pull.back pull
  fref : L.U (T.lvl (J.slot cur p)) (L.<→◃ qr) → L.Ordᶜ (T.lvl root)
  fref u = L.add X σ (f (L.coe (L.<→◃ qr) (L.<→◃ q) u))
  gref : A.Gd (L.limᵢ qr fref)
  gref = Add.good {σ = σ} gx gnode
  module K = Keep.At {κ = T.lvl root} {ν = T.lvl top} {a = L.suc (T.lvl root)}
    (read-strong root) (read-strong root) (W.pc within) (λ q → L.suc q) qr fref
  at : ∀ Y → K.act qt eq (L.into (L.<→◃ qt) Y) ≡
    C.φ (L.add X σ (f (L.into (L.<→◃ q) (back Y))))
  at Y = cong (λ u → C.φ (L.add X σ (f u))) (trans
    (cong (L.coe (L.<→◃ qr) (L.<→◃ q)) (V.Pull.input pull Y))
    (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ qr) (back Y))))
  fam-back : ∀ a V → A.Gd V → U.Fam top pos a V →
    U.Fam cur p (O.mvBr (Down.src d) p a) (back V)
  fam-back a V gv ha = Slots.fam-weak cur p (O.mvBr (Down.src d) p a)
    (Down.pull d p a V ha)
    (A.Layer.pack (Slots.cast-good same-slot gv) (V.Pull.good pull gv)
      (A.Layer.ce (L.≅-trans (Slots.cast-self same-slot gv) (L.≅-sym (V.Pull.transparent pull gv)))))
  margin : ∀ V Y → A.Le (L.suc V) Y → A.Le (L.suc (back V)) (back Y)
  margin V Y t = subst (λ Z → A.Le Z (back Y)) (V.Pull.suc pull V) (V.Pull.mono pull t)
  module General (χ : S.Tr (J.ℓ cur) → S.Tr (J.ℓ top))
    (shape : χ (S.Ω p g) ≡ S.Ω pos (λ a → χ (g (O.mvBr (Down.src d) p a))))
    (IH : ∀ a V Y → A.Gd V → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot cur p))) Y →
      U.Fam cur p a V → A.Le (L.suc V) Y →
      U.UR top (χ (g a))
        (C.φ (L.add X σ (f (L.into (L.<→◃ q) Y))))) where
    row : ∀ a V Y → A.Gd V → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot top pos))) Y →
      U.Fam top pos a V → A.Le (L.suc V) Y →
      U.UR top (χ (g (O.mvBr (Down.src d) p a)))
        (K.act qt eq (L.into (L.<→◃ qt) Y))
    row a V Y gv gy o ha t = subst (U.UR top (χ (g (O.mvBr (Down.src d) p a))))
      (sym (at Y)) (IH (O.mvBr (Down.src d) p a) (back V) (back Y)
        (V.Pull.good pull gv) (V.Pull.good pull gy) (V.Pull.floor pull o) (fam-back a V gv ha) (margin V Y t))
    result : U.UR top (χ (S.Ω p g))
      (C.φ (L.add X σ (L.limᵢ q f)))
    result = subst (λ a → U.UR top a (C.φ (L.add X σ (L.limᵢ q f)))) (sym shape)
      (B.weak top (Slots.node top pos row) (K.bound qt eq same gref))
  module Run
    (IH : ∀ a V Y → A.Gd V → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot cur p))) Y →
      U.Fam cur p a V → A.Le (L.suc V) Y →
      U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx (g a))
        (C.φ (L.add X σ (f (L.into (L.<→◃ q) Y))))) where
    result = General.result (O.Up (J.ℓ cur) (Down.src d) x nx) refl IH

module Actual = Node {root = Model.r} {top = Model.r} {cur = Model.r}
  P.here Down.here (inj₁ tt) Model.x Model.nx Model.X (λ q → q) Model.gx Model.g Model.f Model.good
actual : U.UR Model.r (O.Up (J.ℓ Model.r) O.stop Model.x Model.nx (S.Ω (inj₁ tt) Model.g))
  (W.φ P.here (L.add Model.X (λ q → q) (L.limᵢ L.zero Model.f)))
actual = Actual.Run.result Model.IH
```
