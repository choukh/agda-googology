# YiXV: 二层模拟的三个输出上界
> 验收文件。档位：编译定理。由 YiXVSim.upper 推广；带实际底分量前提，两个目标 0 输出有值界，目标 1 输出带模拟和字面起点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Sem where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock hiding (P)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (next≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; 1≼ψ⁰)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as RA
import OCF.Lean.YiXVSim as OldS
import OCF.Lean.YiXVPlus as OldP
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVNum as N
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2One as I
import OCF.Lean.YiXVCan2Zero as Z
import OCF.Lean.YiXVCan2Rel as S
import OCF.Lean.YiXVCan2Affine as Aff
import OCF.Lean.YiXVCan2SlotOne as Slot1
import OCF.Lean.YiXVCan2NodeOne as Node1

module Value (Comp : Base (suc zero)) (B : Base (suc (suc zero))) where
  module Low = OldS.Sim Comp
  module HC = H.Anchor Comp
  β₀ = bs B zero (ins (ins self))
  nβ₀ = ns B zero (ins (ins self))
  β₁ = bs B (suc zero) (ins self)
  nβ₁ = ns B (suc zero) (ins self)
  slot₀ = ψs (suc (suc zero)) tt tt B zero (ins (ins self)) β₀ nβ₀
  slot₁ = ψs (suc (suc zero)) tt tt B (suc zero) (ins self) β₁ nβ₁
  bot = ψ⊥ (suc (suc zero)) tt tt B
  record Out (x : Tr (suc (suc zero))) (X : F.T₂) : Set where
    constructor out
    field
      bot≤ : read (bot x) ≼ L.ψ⁰ X
      slot₀≤ : read (slot₀ x) ≼ L.ψ⁰ X
      slot₁≤ : Σ (Low.U (slot₁ x) (F.ψ₁ X)) HC.Closed

module At₀ (Comp : Base (suc zero)) (B : Base (suc (suc zero)))
  (g : Tr zero → Tr (suc (suc zero))) (f : R.T₀ → F.T₂) (sc : C.SC₀ f)
  (gb : ∀ y → R.𝟙 ≼ y → C.Gd (f y))
  (IH : ∀ a y → R.𝟙 ≼ y → L.suc (read a) ≼ y → Value.Out Comp B (g a) (f y)) where
  open Value Comp B
  P ν : R.T₀ → R.T₀
  P y = L.ψ (L.suc L.zero) (λ q → q) (f y)
  ν y = L.ψ⁰ (f y)
  norm : N.Norm P ν
  N.Norm.same norm y = F.ψ₀≈ (f y)
  N.Norm.pos norm y = ≼-trans (1≼ψ⁰ (f y)) (proj₂ (F.ψ₀≈ (f y)))
  N.Norm.mo norm x y o q = Z.mono₀ (C.SC₀.mo₀ sc x y o q)
  N.Norm.db norm y o = Z.mono₀ (C.SC₀.db₀ sc y o)
  N.Norm.two norm = ≼-trans (≼l 2 (≼-refl _)) (≼-trans (Z.mono₀ (C.SC₀.po₀ sc)) (proj₂ (F.ψ₀≈ (f R.𝟙))))
  module Bot = N.Node P ν norm (λ a → bot (g a)) (λ a → slot₀ (g a))
    (λ a y o q → Out.bot≤ (IH a y o q)) (λ a y o q → Out.slot₀≤ (IH a y o q))
  module Sl₀ = N.Node P ν norm (λ a → slot₀ (g a)) (λ a → slot₀ (g a))
    (λ a y o q → Out.slot₀≤ (IH a y o q)) (λ a y o q → Out.slot₀≤ (IH a y o q))
  both : Out (Ω (inj₂ (inj₁ tt)) g) (L.limᵢ (L.suc L.zero) f)
  both = out (Bot.result (λ n → nz⊥ (suc (suc zero)) tt tt B (g (Bot.c n))))
    (Sl₀.result (λ n → nzs (suc (suc zero)) tt tt B zero (ins (ins self)) β₀ nβ₀ (g (Sl₀.c n))))
    (Low.un (λ a y q → let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
      in proj₁ (Out.slot₁≤ (IH a y′ (O.s→1 q′) q′))) ,
      λ a y q → let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
      in proj₂ (Out.slot₁≤ (IH a y′ (O.s→1 q′) q′)))

module At₁ (Comp : Base (suc zero)) (B : Base (suc (suc zero)))
  (g : Tr (suc zero) → Tr (suc (suc zero))) (f : R.T₁ → F.T₂) (sc : C.SC₁ f)
  (gb : ∀ Y → O.Gd Y → O.Ω₁ R.≤ₚ Y → C.Gd (f Y))
  (zeroU : OldS.Sim.U Comp zero O.Ω₁) (zeroC : H.Anchor.Closed Comp zeroU)
  (IH : ∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y → (h : OldS.Sim.U Comp a X) → H.Anchor.Closed Comp h →
    L.suc X R.≤ₚ Y → Value.Out Comp B (g a) (f Y)) where
  open Value Comp B
  Hk : ∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y → (h : Low.U a X) → HC.Closed h → L.suc X R.≤ₚ Y →
    Σ (Low.U (slot₁ (g a)) (F.ψ₁ (f Y))) HC.Closed
  Hk a X Y gx gy o h c q = Out.slot₁≤ (IH a X Y gx gy o h c q)
  module Ref = Node1.Chain Comp f sc gb (λ a → slot₁ (g a)) zeroU zeroC Hk
  module Bot = Ref.Ground (λ a → bot (g a)) (λ a X Y gx gy o h c q → Out.bot≤ (IH a X Y gx gy o h c q))
  module Sl₀ = Ref.Ground (λ a → slot₀ (g a)) (λ a X Y gx gy o h c q → Out.slot₀≤ (IH a X Y gx gy o h c q))
  module Sl₁ = Ref.Slot (λ a → slot₁ (g a)) Hk
  both : Out (Ω (inj₁ tt) g) (L.limᵢ L.zero f)
  both = out (Bot.result (λ n → nz⊥ (suc (suc zero)) tt tt B (g (Ref.c n))))
    (Sl₀.result (λ n → nzs (suc (suc zero)) tt tt B zero (ins (ins self)) β₀ nβ₀ (g (Ref.c n))))
    (Sl₁.result (λ n → nzs (suc (suc zero)) tt tt B (suc zero) (ins self) β₁ nβ₁ (g (Ref.c n))))

module Sem (Comp : Base (suc zero)) (B : Base (suc (suc zero)))
  (b : read (b⊥ B) ≼ L.ψ⁰ F.Ω₂) (s : read (bs B zero (ins (ins self))) ≼ L.ψ⁰ F.Ω₂)
  (seed : Σ (OldS.Sim.U Comp (bs B (suc zero) (ins self)) (F.ψ₁ F.Ω₂)) (H.Anchor.Closed Comp))
  (zeroU : OldS.Sim.U Comp zero O.Ω₁) (zeroC : H.Anchor.Closed Comp zeroU) where
  module U = S.Rel Comp
  open Value Comp B
  module Cl = OldP.Closure Comp
  upper : ∀ {x X} → C.Gd X → U.U x X → Out x X
  upper gx U.uz = out b s seed
  upper (C.gs gx) (U.us {x = x} h) = out
    (next≼ (bot x) (nz⊥ (suc (suc zero)) tt tt B x) (Out.bot≤ (upper gx h)))
    (next≼ (slot₀ x) (nzs (suc (suc zero)) tt tt B zero (ins (ins self)) β₀ nβ₀ x) (Out.slot₀≤ (upper gx h)))
    (Cl.next-comp (nzs (suc (suc zero)) tt tt B (suc zero) (ins self) β₁ nβ₁ x) (I.good₁ gx) (proj₁ (Out.slot₁≤ (upper gx h))) ,
      HC.next-closed (nzs (suc (suc zero)) tt tt B (suc zero) (ins self) β₁ nβ₁ x) (I.good₁ gx)
        (proj₁ (Out.slot₁≤ (upper gx h))) (proj₂ (Out.slot₁≤ (upper gx h))))
  upper gx (U.uw h q) = out
    (≼-trans (Out.bot≤ (upper (C.left q) h)) (Z.mono₀ q))
    (≼-trans (Out.slot₀≤ (upper (C.left q) h)) (Z.mono₀ q))
    (Low.uw (I.good₁ (C.left q)) (proj₁ (Out.slot₁≤ (upper (C.left q) h))) (I.mono₁ q) , proj₂ (Out.slot₁≤ (upper (C.left q) h)))
  upper gx (U.ul h) = out (l≼ (λ n → Out.bot≤ (upper gx (h n)))) (l≼ (λ n → Out.slot₀≤ (upper gx (h n))))
    (Low.ul (λ n → proj₁ (Out.slot₁≤ (upper gx (h n)))) , λ n → proj₂ (Out.slot₁≤ (upper gx (h n))))
  upper (C.gn₀ {f = f} law gb) (U.un₀ {g = g} h) = At₀.both Comp B g f law gb (λ a y o q → upper (gb y o) (h a y q))
  upper (C.gn₁ {f = f} law gb) (U.un₁ {g = g} h) = At₁.both Comp B g f law gb zeroU zeroC
    (λ a X Y gx gy o ha ca q → upper (gb Y gy o) (h a X Y gx gy o ha ca q))
  upper gx (U.uu {x = x} {y = y} {ny = ny} {X = X} {Y = Y} gx₀ h gy hy cy) = upcase
    where
    rec = upper gx₀ h
    module A = Aff.Affine Comp (dS (suc zero) tt tt B x) X gx₀ (Out.bot≤ rec) (Out.slot₀≤ rec)
    module F₁ = Slot1.Fold Comp (dS (suc zero) tt tt B x) X gx₀ (slot₁ x)
      (nzs (suc (suc zero)) tt tt B (suc zero) (ins self) β₁ nβ₁ x) (proj₁ (Out.slot₁≤ rec)) (proj₂ (Out.slot₁≤ rec))
    upcase : Out (up x tt y ny) (L.add X RA.σ₁ Y)
    upcase = out (proj₁ (A.upper gy hy cy)) (proj₂ (A.upper gy hy cy)) (F₁.result gy hy cy)
```
