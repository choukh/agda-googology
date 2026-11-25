# YiXVSourceNodeKeep
> 验收文件。档位：编译定理。节点保留分支的世界槽位界；标准实例已填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeKeep where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceNodeEnvelope as E
import OCF.Lean.YiXVSourceGuard as Bridge
import OCF.Lean.YiXVSourceNodeBody as Body

module Keep {n H j} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (source : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n source) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n source)) (L.<→◃ (J.q n source)) → I.T (suc n))
  (body : Body.Node.Body p SrcB Z world source g f) (s : Sbᶠ (suc n) (suc j))
  (target : F.Fin (suc j)) (cv : S.Br (J.nat (suc j)) (J.slot j target) → S.Br (J.nat (suc n)) (J.slot n source))
  (e : I.rank j target ≡ I.rank n source)
  (br : ∀ a → cv (J.inB j target a) ≡ J.inB n source (subst J.Tr e a)) where
  module D = U.Layer j (U.UR j)
  module G = Bridge.Bridge n j source target e
  module Env = E.Node (suc n) (I.rank n source) H (J.q n source) (P.σ p) Z f
  module Native = Env.Target (suc j) (W.pc p s) (λ r → L.suc r)
  module Ref = Native.Canonical (I.rank j target) e (J.q j target)
  Φ : J.Tr (suc n) → J.Tr (suc j)
  Φ x = Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat (suc j)) (Slots.pth s)
    (Fold.bs SrcB (J.nat (suc j)) (Slots.pth s)) (Fold.ns SrcB (J.nat (suc j)) (Slots.pth s)) x
  row : ∀ a X Y → A.Gd (I.rank j target) X → A.Gd (I.rank j target) Y →
    A.Le (I.rank j target) (L.Ω (L.natᴵ (I.rank j target))) Y → U.UR j target a X → A.Le (I.rank j target) (L.suc X) Y →
    D.U (Φ (g (cv (J.inB j target a)))) (Ref.F′ (L.into (L.<→◃ (J.q j target)) Y))
  row a X Y gx gy o ha t = subst₂ (U.U (suc j))
    (sym (cong (λ z → Φ (g z)) (br a)))
    (sym (cong (λ z → W.φ p s (L.add Z (P.σ p) (f z))) (Ref.input Y)))
    (W.Out.slots {n = suc n}
      (Body.Node.Body.out body (G.pullS a) (G.pullR X) (T.τ T.bwd (I.rank n source) (G.pullR Y))
        (G.good X gx) (G.τ-good Y gy) (G.τ-floor Y o) (G.rel a X ha) (G.τ-margin X Y gy t)) (suc j) s)
  result : U.U (suc j) (S.Ω (J.slot j target) (λ z → Φ (g (cv z))))
    (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n source) f)))
  result = subst (U.U (suc j) (S.Ω (J.slot j target) (λ z → Φ (g (cv z))))) (sym Ref.ref-shape) (D.un target row)

module Model = Keep Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z Body.Model₀.world F.zero Body.Model₀.g Body.Model₀.Native.f
  Body.Model₀.body s0 F.zero (λ z → z) refl (λ a → refl)
actual : U.U 1 (S.Ω (J.slot 0 F.zero) (λ a → Model.Φ (Body.Model₀.g a)))
  (W.φ Body.Model₀.p s0 (L.add Body.Model₀.Z (P.σ Body.Model₀.p) (L.Ω (L.natᴵ 1) L.+ L.Ω (L.natᴵ 1))))
actual = Model.result
```
