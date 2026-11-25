# YiXVReadRouteNodeKeep
> 验收文件。档位：编译定理。节点保留分支的读回模拟，使用实际槽位等式，含规范闭实例。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteNodeKeep where
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)
import Data.Sum
import OCF.Lean.YiLegPath
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRetain as Retain
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadSlots as Slots
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadKeepAt as Keep
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteWorldInput as W
open import OCF.Lean.YiXVLvlSteps using (read-strong)
open import OCF.Lean.YiXVReadKeepLinkInput using (Link)
import OCF.Lean.YiXVReadRouteNodeModels as Models

module Node {root cur} (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (w : W.World root cur within SrcB Z)
  (p : S.Pos (J.ℓ cur)) (g : S.Br (J.ℓ cur) p → S.Tr (J.ℓ cur))
  (f : L.U (T.lvl (J.slot cur p)) (L.<→◃ (J.q cur p)) → L.Ordᶜ (T.lvl cur))
  (gnode : A.Gd (L.limᵢ (J.q cur p) f))
  (body : ∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot cur p))) Y →
    U.Fam cur p a X → A.Le (L.suc X) Y →
    W.Out root cur within SrcB Z (g a) (f (L.into (L.<→◃ (J.q cur p)) Y))) where
  q = J.q cur p
  qr = O.σ within q
  fref : L.U (T.lvl (J.slot cur p)) (L.<→◃ qr) → L.Ordᶜ (T.lvl root)
  fref u = O.cap within Z (f (L.coe (L.<→◃ qr) (L.<→◃ q) u))
  gref : A.Gd (L.limᵢ qr fref)
  gref = Add.good {σ = O.σ within} (W.World.good w) gnode
  module Target {y} (py : y P.≤ᵀ root) (v : J.ℓ y OCF.Lean.YiLegPath.≤ J.ℓ cur)
    (rv : R.Route cur y v) (pt : S.Pos (J.ℓ y))
    (cv : S.Br (J.ℓ y) pt → S.Br (J.ℓ cur) p) (link : Link cur (Data.Sum.inj₂ p) y pt cv) where
    qt = J.q y pt
    same : T.lvl (J.slot cur p) ≡ T.lvl (J.slot y pt)
    same = sym (cong T.lvl (Link.same link))
    eq : T.lvl (J.slot cur p) L.≅ᴵ T.lvl (J.slot y pt)
    eq = subst (λ j → T.lvl (J.slot cur p) L.≅ᴵ j) same (L.≅ᴵ-refl (T.lvl (J.slot cur p)))
    pull = Retain.pull qr qt eq same
    back = V.Pull.back pull
    module K = Keep.At {κ = T.lvl root} {ν = T.lvl y} {a = L.suc (T.lvl root)}
      (read-strong root) (read-strong root) (Old.pc py) (λ q → L.suc q) qr fref
    Φ = Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ y) v
      (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v)
    at : ∀ Y → K.act qt eq (L.into (L.<→◃ qt) Y) ≡
      Old.φ py (O.cap within Z (f (L.into (L.<→◃ q) (back Y))))
    at Y = cong (λ u → Old.φ py (O.cap within Z (f u))) (trans
      (cong (L.coe (L.<→◃ qr) (L.<→◃ q)) (V.Pull.input pull Y))
      (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ qr) (back Y))))
    fam-back : ∀ a X → A.Gd X → U.Fam y pt a X → U.Fam cur p (cv a) (back X)
    fam-back a X gx ha = Slots.fam-weak cur p (cv a) (Link.pull link a X ha)
      (A.Layer.pack (Slots.cast-good (Link.same link) gx) (V.Pull.good pull gx)
        (A.Layer.ce (L.≅-trans (Slots.cast-self (Link.same link) gx) (L.≅-sym (V.Pull.transparent pull gx)))))
    margin : ∀ X Y → A.Le (L.suc X) Y → A.Le (L.suc (back X)) (back Y)
    margin X Y t = subst (λ Z → A.Le Z (back Y)) (V.Pull.suc pull X) (V.Pull.mono pull t)
    row : ∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot y pt))) Y →
      U.Fam y pt a X → A.Le (L.suc X) Y →
      U.UR y (Φ (g (cv a))) (K.act qt eq (L.into (L.<→◃ qt) Y))
    row a X Y gx gy o ha t = subst (U.UR y (Φ (g (cv a)))) (sym (at Y))
      (W.Out.slots {cur = cur}
        (body (cv a) (back X) (back Y) (V.Pull.good pull gx) (V.Pull.good pull gy)
          (V.Pull.floor pull o) (fam-back a X gx ha) (margin X Y t)) y py v rv)
    result : U.UR y (S.Ω pt (λ a → Φ (g (cv a))))
      (Old.φ py (O.cap within Z (L.limᵢ q f)))
    result = B.weak y (Slots.node y pt row) (K.bound qt eq same gref)

open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiXVReadAffineNodeModels as N
open import OCF.Lean.YiXVReadKeepLinkInput using (model-keep)
module Actual = Node P.here Models.SrcB Models.Z W.model₁ (inj₁ tt) N.g N.f N.good Models.body
actual : U.UR Models.r
  (S.Ω (inj₁ tt) (λ a → Actual.Target.Φ P.here Path.self R.here (inj₁ tt) (λ z → z) model-keep (N.g a)))
  (Old.φ P.here (O.cap P.here Models.Z (L.limᵢ L.zero N.f)))
actual = Actual.Target.result P.here Path.self R.here (inj₁ tt) (λ z → z) model-keep
```
