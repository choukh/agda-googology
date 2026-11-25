# 实际反馈叠加第二份 P 所要求的前缀证书

第四层。把第二份 P 的零层值写成同一运算的有限迭代极限。给定前缀状态，原来的输入状态在所有额外槽位上也可任取。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadReturnRow where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import W4Block
open import W4Ops
open import W4Fold
open import WVOne using (𝟏; read; T₀)
open import WKGen using (Ω₁t; node-ge)
open import YiLAB7Orbit using (lvl1; lvl2; ok₂; p₁)
open import YiLAB7Replay using (Ω₂ᴸ)
open import WSLevel using (Ω₁ᴸ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼-suc; l≼; ≅→≼)
import B12Omega3Ref as R
import B13OrbitFeed as O
import B13Target as P
import B15OrbitModel as M
import B19RowPair as Pair
import B22RowPrefix as B
import B22RowLive as V
import B22RowRule as Rule
import B24AFrame as F
import B24RKernel as K
import B24RRows as Row
import Survey.W4LeadReturnPositive as Z

import B12LimitSrc as Src
module RowAt (p : Src.Lev₂) (rp : p L.≅ p) where
  q = λ x → p L.+ K.q x
  rq : ∀ {x y} → x L.≅ y → q x L.≅ q y
  rq d = L.add-≅ {σ = R.idσ} {σ′ = R.idσ} rp (K.regular d)
  one : Z.anchor L.≅ L.limᵢ (L.suc L.zero) K.q
  one = L.lᵢ≅ L.z≅ (λ x y e → P.pass-pres (L.add-≅ {σ = λ t → L.suc (L.suc t)} {σ′ = λ ()}
    (L.Ω-refl _) (L.tr⁻-≅ L.z≅ e)))
  normal : (p L.+ Z.anchor) L.≅ L.limᵢ (L.suc L.zero) q
  normal = L.≅-trans (L.add-≅ {σ = R.idσ} {σ′ = R.idσ} rp one) (L.lᵢ≅ L.z≅ (λ x y d → rq d))
  g = λ x → L.ψ⁰ (q x)
  xs = R.S.iter g 𝟏
  raw = L.ψ⁰ (p L.+ Z.anchor)
  chain : raw L.≅ L.lim (λ n → xs (ℕ.suc n))
  chain = L.≅-trans (L.ψ⁰-≅ normal) (L.≅-sym (proj₁ (Pair.Small.value (λ x → B.project (q x)) q rq
    (λ x → B.self (rq (L.≅-refl⁰ x))))))

  module At (Q : Op {lvl2} nil) (law : Rule.Rule Q Ω₂ᴸ) (S : St M.X₁) (l : B.Label p) (h : V.Present l (M.pull S)) (slot : L.ψ⁰ (B.q l) ≼ read (proj₁ (S zero M.down-t))) where
    K₁ = enterO O.m₁ Q
    K₀ = enterO O.m₂ K₁
    S₀ : St M.X₀
    S₀ i t = S i (proj₂ t)
    module Count = F.Deep.Count K₀ Ω₂ᴸ (F.enter-rule {Q = Q} {x = Ω₂ᴸ} law)
    dz = M.down-t
    step = λ z → proj₁ (E ok₂ O.D₁ (O.g₁ z) K₁ S zero dz (S zero dz))
    module Point (y : T₀) (z : Tr zero) (low : y ≼ read (suc z)) where
      local = Count.eval (suc z) {y} low
      updated = F.Deep.advance local l
      part : ∀ t b → L.ψ⁰ (B.q l) ≼ read (proj₁ b) → g y ≼ read (proj₁ (E ok₂ O.D₁ (O.g₁ z) K₁ S zero t b))
      part t b hb = ≼-trans (≅→≼ (L.≅-sym (proj₁ (B.link updated)))) (F.Deep.value local l S₀ h (σ O.m₂ t) b hb)
    clock = iter step zero
    follow : ∀ n → xs n ≼ read (suc (clock n))
    follow ℕ.zero = ≼-refl _
    follow (ℕ.suc n) = ≼-suc (Point.part (xs n) (clock n) (follow n) dz (S zero dz) slot)
    pay : ∀ t b → L.ψ⁰ (B.q l) ≼ read (proj₁ b) → raw ≼ read (proj₁ (E ok₂ O.D₁ Ω₁t K₁ S zero t b))
    pay t b hb = ≼-trans (≅→≼ chain) (l≼ (λ n → ≼-trans (Point.part (xs n) (clock n) (follow n) t b hb)
      (node-ge (kpT (fr O.D₁) ok₂ p₁ (tv O.D₁ t)) (λ z → E ok₂ O.D₁ (O.g₁ z) K₁ S zero t b) step n)))

import B12Terminal as T
import B12ActualSlots as Cv
import B13SeedOuter as Start
import B24AFirst as First
open import WKShape using (lvl3)
open import YiLAB11Orbit using (push)

module Empty (r : T.Run lvl3) (cv : Cv.Covered r) where
  open Start.At r using (st1; w2; v₁)
  open First.At r cv using (Q₁; law; input; seed)
  module E = RowAt L.zero L.z≅
  module Use = E.At Q₁ law (push st1) B.empty input (V.lower input (proj₂ M.down-t))
  paid : E.raw ≼ read (proj₁ (E ok₂ O.D₁ Ω₁t (enterO O.m₁ Q₁) (push st1) zero (σ O.m₁ w2) v₁))
  paid = Use.pay (σ O.m₁ w2) v₁ seed

module Double = RowAt Z.anchor (Row.respects (L.Ω-refl _))
```
