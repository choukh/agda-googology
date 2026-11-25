# YiXVReadRouteNodeDiag
> 验收文件。档位：编译定理。节点对角分支的底部值界与槽位模拟，包含原回灌轨道与部分和。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteNodeDiag where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst; subst₂)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableFoldInput as FQ
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadCoordinates as C
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadEnv as RootEnv
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRouteFeed as Feed
import OCF.Lean.YiXVReadRouteWorldInput as W
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadGrowthInput as GI
import OCF.Lean.YiXVReadGrowth as Growth
import OCF.Lean.YiXVReadNodeGrowthInput as NI
import OCF.Lean.YiXVReadNodeGrowth as Native
import OCF.Lean.YiXVReadNodeEnvelope as Envelope
import OCF.Lean.YiXVReadNodeOrbit as Orbit
import OCF.Lean.YiXVReadRouteNodeKeep as Keep

module Node {root cur} (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (w : W.World root cur within SrcB Z)
  (p : S.Pos (J.ℓ cur)) (g : S.Br (J.ℓ cur) p → S.Tr (J.ℓ cur))
  (f : L.U (T.lvl (J.slot cur p)) (L.<→◃ (J.q cur p)) → L.Ordᶜ (T.lvl cur))
  (gnode : A.Gd (L.limᵢ (J.q cur p) f))
  (body : ∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot cur p))) Y →
    U.Fam cur p a X → A.Le (L.suc X) Y →
    W.Out root cur within SrcB Z (g a) (f (L.into (L.<→◃ (J.q cur p)) Y))) where
  i = J.slot cur p
  pi : i P.≤ᵀ root
  pi = C.inside (P.normal (J.below cur p)) within
  module K = Keep.Node within SrcB Z w p g f gnode body
  open K using (q; qr; fref; gref)
  module Env = Envelope.Node i qr fref
  module Ref = Native.Frame (read-strong root) qr fref (NI.law-of gref) (NI.body-of gref)
  module Orb = Orbit.Orbit cur p SrcB g
  module Ops = FQ.Ops (F.ops (T.lvl root) (read-strong root))
  at : ∀ Y → Env.high Y ≡ Out.cap within Z (f (L.into (L.<→◃ q) Y))
  at Y = cong (λ u → Out.cap within Z (f u))
    (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ qr) Y))
  high-good : ∀ Y → A.Gd Y → A.Le (L.Ω (T.lvl i)) Y →
    A.Gd (Out.cap within Z (f (L.into (L.<→◃ q) Y)))
  high-good Y gy o = subst A.Gd (at Y) (Ref.good Y gy o)
  low : ∀ a X → U.UR i a X → U.Fam cur p (J.inB cur p a) X
  low a X h = subst (λ R → R) (sym (B.stable cur p (J.inB cur p a) X))
    (subst (λ b → U.UR i b X) (sym (J.out-in cur p a)) h)
  step : GI.SourceStep i Env.P Orb.step
  GI.SourceStep.step step a X Y gx gy o ha t =
    subst (U.UR i (Orb.step a)) (sym (cong (L.ψ qr (λ r → r)) (at Y)))
      (B.weak i
        (W.Out.slots {cur = cur} (body (J.inB cur p a) X Y gx gy o (low a X ha) t)
          i pi Orb.v (Feed.route cur p))
        (Ops.mono {ν = T.lvl i} {a = L.suc (T.lvl root)} {b = T.lvl root}
          (read-strong root) (read-strong root) (Old.pc pi) qr (λ q → L.suc q) (λ r → r)
          (A.Layer.rfl (T.lvl root) A.Gd< A.Le< (high-good Y gy o))))
  module Chain = Growth.Source i Env.P Ref.growth Orb.step step Orb.orbit
  Φ₀ = Fold.ψ⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB
  F₀ : ℕ → S.Tr S.zero
  F₀ n = Φ₀ (g (Orb.br n))
  row₀ : ∀ n X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl i)) Y →
    U.UR i (Orb.c n) X → A.Le (L.suc X) Y → U.UR S.zero (F₀ n) (Env.η₀ Y)
  row₀ n X Y gx gy o ha t = subst₂ (U.UR S.zero) (Orb.row Φ₀ n) (sym (cong L.ψ⁰ (at Y)))
    (W.Out.bot {cur = cur} (body (J.inB cur p (Orb.c n)) X Y gx gy o (low (Orb.c n) X ha) t))
  module Bottom = Chain.Slot S.zero Env.η₀
    (Ref.Bot.output {a = L.suc (T.lvl root)} (read-strong root) (RootEnv.zero-bound root) (λ q → L.suc q)) F₀ row₀
  bot : Read.read (Fold.ψ⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (S.Ω p g)) ≼
    L.ψ⁰ (Out.cap within Z (L.limᵢ q f))
  bot = subst (U.UR S.zero (O.limc F₀ (λ n → Fold.nz⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (g (Orb.br n)))))
    (sym Env.bot-shape)
    (Bottom.result (λ n → Fold.nz⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (g (Orb.br n))))
  module Target {y} (py : y P.≤ᵀ root) (v : J.ℓ y Path.≤ J.ℓ cur) (rv : R.Route cur y v) where
    module E = Env.Target (Old.pc py) (λ q → L.suc q)
    Φ = Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ y) v
      (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v)
    F : ℕ → S.Tr (J.ℓ y)
    F n = Φ (g (Orb.br n))
    row : ∀ n X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl i)) Y →
      U.UR i (Orb.c n) X → A.Le (L.suc X) Y → U.UR y (F n) (E.η Y)
    row n X Y gx gy o ha t = subst₂ (U.UR y) (Orb.row Φ n)
      (sym (cong (L.ψ (Old.pc py) (λ q → L.suc q)) (at Y)))
      (W.Out.slots {cur = cur} (body (J.inB cur p (Orb.c n)) X Y gx gy o (low (Orb.c n) X ha) t) y py v rv)
    module Column = Chain.Slot y E.η
      (Ref.Target.output {a = L.suc (T.lvl root)} (read-strong root) (Old.pc py) (λ q → L.suc q)) F row
    nz : ∀ n → J.ℓ y S.⊢ S.zero ◃ F n
    nz n = Fold.nzs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ y) v
      (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v) (g (Orb.br n))
    default = O.limc F nz
    result : y P.≤ᵀ i → U.UR y default (Old.φ py (Out.cap within Z (L.limᵢ q f)))
    result d = subst (U.UR y default) (sym (E.diagonal d)) (Column.result nz)
```
