# YiXVSourceColumnNode
> 验收文件。档位：编译定理。节点在显式目标种子下的保留／对角输出界；回灌复用原世界语义。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceColumnNode where
open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst; subst₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
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
import OCF.Lean.YiXVSourceGuard as Bridge
import OCF.Lean.YiXVSourceNodeBody as Body
import OCF.Lean.YiXVSourceNodeDiag as Diag

module Node {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (i : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n i)) (L.<→◃ (J.q n i)) → I.T (suc n))
  (law : A.Layer.SC n (A.GoFam n) (A.LeFam n) (J.q n i) f)
  (gb : ∀ u → A.Layer.GU n (A.GoFam n) (A.LeFam n) (J.q n i) u →
    A.Layer.Floor n (A.GoFam n) (A.LeFam n) (J.q n i) u → A.Gd (suc n) (f u))
  (body : Body.Node.Body p SrcB Z world i g f)
  (j : ℕ) (s : Sbᶠ (suc n) j) (β : J.Tr j) (nβ : J.nat j S.⊢ S.zero ◃ β)
  (ih : ∀ a X Y → A.Gd (I.rank n i) X → A.Gd (I.rank n i) Y → A.Le (I.rank n i) (L.Ω (L.natᴵ (I.rank n i))) Y →
    U.UR n i a X → A.Le (I.rank n i) (L.suc X) Y →
    U.U j (Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s) β nβ (g (J.inB n i a)))
      (W.φ p s (L.add Z (P.σ p) (f (L.into (L.<→◃ (J.q n i)) Y))))) where
  module D = Diag.Node p SrcB Z world i g f law gb body
  module Native = D.Env.Target j (W.pc p s) (λ q → L.suc q)
  Φ : J.Tr (suc n) → J.Tr j
  Φ = Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s) β nβ
  F : ℕ → J.Tr j
  F k = Φ (g (D.Orb.br k))
  row : ∀ k X Y → A.Gd D.m X → A.Gd D.m Y → A.Le D.m (L.Ω (L.natᴵ D.m)) Y →
    U.U D.m (D.Chain.c k) X → A.Le D.m (L.suc X) Y → U.U j (F k) (Native.ν Y)
  row k X Y gx gy o ha t = subst₂ (U.U j) (D.Orb.row j Φ k)
    (sym (cong (λ z → W.φ p s (L.add Z (P.σ p) (f z))) (D.Ref.ca-eq Y)))
    (ih (D.Orb.c k) X Y gx gy o (D.low _ X ha) t)
  module Column = D.Chain.Slot j Native.ν (D.Ref.output j (W.pc p s) (λ q → L.suc q)) F row
  nz : ∀ k → J.nat j S.⊢ S.zero ◃ F k
  nz k = Fold.nzs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s) β nβ (g (D.Orb.br k))
  default = O.limc F nz
  drop : j Data.Nat.≤ D.m → U.U j default (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))
  drop le = subst (U.U j default) (sym (Native.diagonal le)) (Column.result nz)

  keep : ∀ {k} (eq : j ≡ suc k) (target : F.Fin (suc k))
    (cv : S.Br (J.nat (suc k)) (J.slot k target) → S.Br (J.nat (suc n)) (J.slot n i))
    (e : I.rank k target ≡ I.rank n i) (br : ∀ a → cv (J.inB k target a) ≡ J.inB n i (subst J.Tr e a)) →
    U.U j (subst J.Tr (sym eq) (S.Ω (J.slot k target) (λ z → subst J.Tr eq (Φ (g (cv z))))))
      (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))
  keep {k} Relation.Binary.PropositionalEquality.refl target cv e br = subst
    (U.U (suc k) (S.Ω (J.slot k target) (λ z → Φ (g (cv z))))) (sym Ref.ref-shape) (Src.un target kr)
    where
    module G = Bridge.Bridge n k i target e
    module Ref = Native.Canonical (I.rank k target) e (J.q k target)
    module Src = U.Layer k (U.UR k)
    kr : ∀ a X Y → A.Gd (I.rank k target) X → A.Gd (I.rank k target) Y →
      A.Le (I.rank k target) (L.Ω (L.natᴵ (I.rank k target))) Y → U.UR k target a X → A.Le (I.rank k target) (L.suc X) Y →
      U.U (suc k) (Φ (g (cv (J.inB k target a)))) (Ref.F′ (L.into (L.<→◃ (J.q k target)) Y))
    kr a X Y gx gy o ha t = subst₂ (U.U (suc k)) (sym (cong (λ z → Φ (g z)) (br a)))
      (sym (cong (λ z → W.φ p s (L.add Z (P.σ p) (f z))) (Ref.input Y)))
      (ih (G.pullS a) (G.pullR X) (T.τ T.bwd (I.rank n i) (G.pullR Y))
        (G.good X gx) (G.τ-good Y gy) (G.τ-floor Y o) (G.rel a X ha) (G.τ-margin X Y gy t))

result : ∀ {n H} (p : P.Path H (suc n)) (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H)
  (world : W.World (suc n) H p SrcB Z) (i : F.Fin (suc n))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n))
  (f : L.U (L.natᴵ (I.rank n i)) (L.<→◃ (J.q n i)) → I.T (suc n))
  (law : A.Layer.SC n (A.GoFam n) (A.LeFam n) (J.q n i) f)
  (gb : ∀ u → A.Layer.GU n (A.GoFam n) (A.LeFam n) (J.q n i) u →
    A.Layer.Floor n (A.GoFam n) (A.LeFam n) (J.q n i) u → A.Gd (suc n) (f u))
  (body : Body.Node.Body p SrcB Z world i g f)
  (j : ℕ) (s : Sbᶠ (suc n) j) (β : J.Tr j) (nβ : J.nat j S.⊢ S.zero ◃ β)
  (ih : ∀ a X Y → A.Gd (I.rank n i) X → A.Gd (I.rank n i) Y → A.Le (I.rank n i) (L.Ω (L.natᴵ (I.rank n i))) Y →
    U.UR n i a X → A.Le (I.rank n i) (L.suc X) Y →
    U.U j (Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s) β nβ (g (J.inB n i a)))
      (W.φ p s (L.add Z (P.σ p) (f (L.into (L.<→◃ (J.q n i)) Y))))) →
  U.U j (Fold.ψs (J.nat (suc n)) (Default.ev (suc n)) (Default.rt (suc n)) SrcB (J.nat j) (Slots.pth s) β nβ (S.Ω (J.slot n i) g))
    (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))
result {n} p SrcB Z world i g f law gb body zero s β nβ ih = Slots.kcase₀ s i (Default.ev (suc n)) (Default.rt (suc n))
  (λ x → U.U 0 x (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))) (N.drop z≤n)
  where module N = Node p SrcB Z world i g f law gb body 0 s β nβ ih
result {n} p SrcB Z world i g f law gb body (suc k) s β nβ ih = Slots.kcase₊ s i (Default.ev (suc n)) (Default.rt (suc n))
  (λ x → U.U (suc k) x (W.φ p s (L.add Z (P.σ p) (L.limᵢ (J.q n i) f)))) N.drop
  (λ target cv e br → N.keep Relation.Binary.PropositionalEquality.refl target cv e br)
  where module N = Node p SrcB Z world i g f law gb body (suc k) s β nβ ih

module Model = Node Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z Body.Model₀.world F.zero Body.Model₀.g Body.Model₀.Native.f
  Body.Model₀.Native.law Body.Model₀.Native.body Body.Model₀.body 0 (ss s0)
  (Fold.bs Body.Model₀.SrcB (J.nat 0) (Slots.pth (ss s0))) (Fold.ns Body.Model₀.SrcB (J.nat 0) (Slots.pth (ss s0)))
  (λ a X Y gx gy o ha t → W.Out.slots {n = 1} (Body.Node.Body.out Body.Model₀.body a X Y gx gy o ha t) 0 (ss s0))
actual = result Body.Model₀.p Body.Model₀.SrcB Body.Model₀.Z Body.Model₀.world F.zero Body.Model₀.g Body.Model₀.Native.f
  Body.Model₀.Native.law Body.Model₀.Native.body Body.Model₀.body 0 (ss s0) _ _
  (λ a X Y gx gy o ha t → W.Out.slots {n = 1} (Body.Node.Body.out Body.Model₀.body a X Y gx gy o ha t) 0 (ss s0))
```
