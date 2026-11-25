# 同一实际反馈里反复保存 D 与所询正坐标

第四层。第三塔的有限迭代窗里，每一轮均可从所有零槽已达 D 的环境重新建立 ψ₁(P) 的正输入，并支付去掉 Ω₂ 前缀的零层返回。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadReturnState where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import W4Block
open import W4Ops
open import W4Fold
open import WVOne using (T₀; 𝟏; read)
open import WVTwo using (◃→≼)
open import WKShape using (lvl3)
open import YiLAB7Orbit using (lvl1; lvl2; ok₂; p₁)
open import WKGen using (Ω₁t)
open import YiLAB11Orbit using (push)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import B11OuterCore as C
import B12Terminal as T
import B12ActualSlots as Cov
import B12Orbit as Window
import B13OrbitFeed as O
import B13Orbit as Orb
import B13SeedOuter as Site
import B14OrbitReal as Real
import B15OrbitModel as M
import B18OrbitWorld as W
import B18OrbitLevels as All
import B18RefDepth as H
import B18OrbitRows as Old
import B21RowDynamics as I
import B22RowPrefix as Label
import B22RowLive as Live
import B22RowWhole as Initial
import B23ABlocks as Blocks
import B23AFinite as Fin
import B24AFirst as First
import B24ROrbit as D
import B24NBridge as Bridge
import B24AWhole as Geometry
import B24NProduct as Prod
import B24NKid as Kid
import B24NStore as Store
import B24NScalar as S
import Survey.W4LeadReturnPositive as Pos

module At (r : T.Run lvl3) (cv : Cov.Covered r) where
  open First.At r cv using (Q₁; Q₂)
  open Site.At r using (c⁺; st1; w2; v₁; outer)
  states = λ n → itS Q₂ n st1
  present : ∀ n → Live.Present Label.empty (states n)
  present ℕ.zero = First.At.input r cv
  present (ℕ.suc n) = Live.present
    (λ w → ≼-trans (Live.lower (present n) w) (◃→≼ (inc′ zero w)))
    (Real.carry {e = Label.e Label.empty} {R = states n} {S = states (ℕ.suc n)}
      (inc′ lvl1 C.slot) (Live.struct (present n)))
    (λ d → W.rise (All.world d) (states n lvl1 C.slot) (states (ℕ.suc n) lvl1 C.slot)
      (inc′ lvl1 C.slot) (Label.v Label.empty d) (Live.index (present n) d))
    where inc′ = λ i w → inf Q₂ (states n) i w (states n i w)
  floor : ∀ n w → D.D ≼ read (proj₁ (states (ℕ.suc n) zero w))
  floor n w = First.inside Q₁ (First.At.law r cv) (states n) (present n) c⁺ (Blocks.Site.cp r cv)
    w (states n zero w) (Live.lower (present n) w)

  module Call (n : ℕ) (w : zero ≤ lvl2) (b : Tr⁺ zero) (hb : 𝟏 ≼ read (proj₁ b)) where
    state = states (ℕ.suc n)
    h = present (ℕ.suc n)
    cov = C.st (Live.struct h)
    module G = Geometry.Geometry Q₁ state cov w b
    tree = Ω⁺ p₁ (λ z → E ok₂ O.D₁ (O.g₁ z) G.K G.S lvl1 G.high G.c₀)
    vi : I.Index G.c₀ H.initial
    vi = W.start Prod.world G.c₀ cov
    v : ∀ z x → x ≼ read (suc z) → I.Index (E ok₂ O.D₁ (O.g₁ z) G.K G.S lvl1 G.high G.c₀) (Kid.coef x H.initial)
    v z x below = Kid.At.queried r cv x z below G.S H.initial cov vi G.c₀ vi
    selected : I.Index tree Store.Sem.target
    selected = W.retain Prod.world _ (proj₂ tree) Store.Sem.f Store.Sem.r Store.Sem.q (λ x z low → v z x low)

    module Bnd = G.Row 0 S.weak
    weak : Bnd.Test
    weak j le = part G.at₀ (G.S zero G.at₀) (Live.lower h (proj₂ G.at₀)) , part G.own b hb
      where
      x = Bnd.src j
      z = Bnd.z j
      tr = E ok₂ O.D₁ (O.g₁ z) G.K G.S lvl1 G.high G.c₀
      part = Bridge.At.part G.K (S.At.base r cv) G.S h (Live.lower h (proj₂ Old.Out.ip)) tr
        (Kid.Native.kid 1 x) (Kid.Native.regular 1 (L.≅-refl⁰ x)) (Kid.coef x H.initial) (Kid.kid x) (v z x le)
    paid : Pos.zero-return ≼ read (proj₁ (run Q₂ state zero w b))
    paid = ≼-trans {b = S.bound} (≅→≼ Pos.same) (Bnd.Has.picked weak c⁺ (Blocks.Site.cp r cv))

  values = λ n → itV Q₂ n st1 zero w2 v₁
  base : ∀ n → 𝟏 ≼ read (proj₁ (values n))
  base ℕ.zero = First.At.seed r cv
  base (ℕ.suc n) = ≼-trans (base n) (◃→≼ (inf Q₂ (states n) zero w2 (values n)))
  paid : ∀ n → Pos.zero-return ≼ read (proj₁ (values (ℕ.suc (ℕ.suc n))))
  paid n = Call.paid n w2 (values (ℕ.suc n)) (base (ℕ.suc n))
  into : ∀ n → read (proj₁ (values (ℕ.suc n))) ≼ read (T.value r)
  into n = ≼-trans (◃→≼ inside) (≼-trans (◃→≼ (Fin.At.inside r cv 3 st1 zero w2 v₁)) (outer 0))
    where
    Q₃ = Orb.block c⁺ Q₂
    inside : zero ⊢ proj₁ (values (ℕ.suc n)) ◃ proj₁ (run Q₃ st1 zero w2 v₁)
    inside = subst (λ a → zero ⊢ proj₁ a ◃ proj₁ (run Q₃ st1 zero w2 v₁))
      (Window.Window.project-value Q₂ (ℕ.suc n) st1 zero w2 v₁)
      (◃t (Window.Window.in-child Q₂ n st1 zero w2 v₁) (Orb.contains c⁺ (Blocks.Site.cp r cv) Q₂ st1 zero w2 v₁))
```
