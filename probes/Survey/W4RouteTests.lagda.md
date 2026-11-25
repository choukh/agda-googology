# 用实际第零反馈列检验有限理论上界

第四层，无条件。每座正塔取第零反馈值。整列逐项可在某个有限层取得严格上界，等价于整树不超过 ψ₀(Ω_ω)。原 EBO 下界要求同一列中至少有一项越过整条有限理论阶梯。[整列共尾](Reports-2026-11-18/attachments/B17CellNext.agda.txt) · [有限理论校准](W4PTOFinite.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4RouteTests where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import WVOne using (T₀; read)
open import W4Fold using (EBOᶜ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; l≼; ≼l; s≼s; ≼-refl; ≼-suc; ≼-trans; ≼lim⁻; ≅→≼)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Align.EboLeanTree using (EBO-tree′)
import B12BtboCut as Cut
import B12EboRows as Rows
import B12Omega3Ref as Original
import B13Target as Target
import B14Goal as Goal
import B17Calibration as Cal
import B17CellPrefix as Cells
import B17CellNext as Next
import B22MovingIndex as Eps
import B23NFirst as Asked
import B23RShare as First
import B24AQueries as Q
import B25AOrbit as Orbit
import B29SFirst as Tower
import B29SCases as Cases
import B31NReal as Input
import Survey.W4PTOClock as Clock
import Survey.W4PTOFirstQuery as Query

Y : T₀
Y = read EBOᶜ
c : ℕ → T₀
c m = Cells.cell m 0

proper : ∀ m → L.suc (c m) ≼ Y
proper m = ≼-trans {b = L.suc (Rows.child (suc m))}
  (s≼s (Cells.At.S.lift-value m 0))
  (≼-trans {b = c (suc m)} (Next.strict (suc m) 0) (Next.actual (suc m) 0))

module Scale (a : ℕ → T₀) where
  B : T₀
  B = L.lim a
  Bounded : Set
  Bounded = ∀ m → Σ ℕ (λ k → L.suc (c m) ≼ a k)

  upper : Bounded → Y ≼ B
  upper h = ≼-trans {b = L.lim c} (proj₁ Next.zero-chain) (l≼ λ m →
    ≼l {f = a} (proj₁ (h m)) (≼-trans {b = L.suc (c m)}
      (≼-suc (≼-refl (c m))) (proj₂ (h m))))

  recover : Y ≼ B → Bounded
  recover h m = ≼lim⁻ {a = c m} {f = a} (≼-trans {b = Y} (proper m) h)

cross : ∀ (q : T₀) → L.suc q ≼ Y → Σ ℕ (λ m → L.suc q ≼ c m)
cross q h = ≼lim⁻ {a = q} {f = c} (≼-trans {b = Y} h (proj₁ Next.zero-chain))

cross-back : ∀ (q : T₀) → Σ ℕ (λ m → q ≼ c m) → L.suc q ≼ Y
cross-back q (m , p) = ≼-trans {b = L.suc (c m)} (s≼s p) (proper m)

module Finite = Scale Cut.finite
finite-upper : Finite.Bounded → Y ≼ Cut.omega-cut
finite-upper = Finite.upper
finite-recover : Y ≼ Cut.omega-cut → Finite.Bounded
finite-recover = Finite.recover

needed : Goal.Goal → Σ ℕ (λ m → L.suc Cut.omega-cut ≼ c m)
needed h = cross Cut.omega-cut (≼-trans {b = Rows.row 2} Cal.finite-cut
  (≼-trans {b = toL EBO-tree′} (Goal.row-in 2) h))

at-zero : c 0 ≈ᵛ Input.square
at-zero = ≼-trans {b = Tower.x 1} (proj₁ (Cases.full 0)) (proj₁ Input.input) ,
          ≼-trans {b = Tower.x 1} (proj₂ Input.input) (proj₂ (Cases.full 0))

at-one : L.suc Tower.S ≼ c 1
at-one = ≼-trans {b = L.suc (Rows.child 1)}
  (s≼s (proj₂ Cases.exact-tower)) (Next.strict 1 0)
```

固定份数的参照值记为 aₙ。对角每步至少增加一，故时钟本身由迭代值界住。将时钟取到 ε 端点给出下式。

```agda
clock-below : ∀ x t → t ≼ Clock.run x t
clock-below x L.zero = z≼
clock-below x (L.suc t) = ≼-trans {b = L.suc (Clock.run x t)}
  (s≼s (clock-below x t)) (Orbit.strict-step (Clock.run x t))
clock-below x (L.lim f) = l≼ (λ n → ≼l n (clock-below x (f n)))

epsilon-step : ∀ n → Eps.above (Q.recorded n) ≼ Q.recorded (suc n)
epsilon-step n = ≼-trans {b = Clock.run a (Eps.above a)}
  (clock-below a (Eps.above a)) (Query.Part.endpoint n a (≼-refl a))
  where a = Q.recorded n

room-to-query : ∀ n → L.suc (Eps.above (Q.recorded n)) ≼ First.oneStep
room-to-query n = ≼-trans {b = L.suc (Q.recorded (suc n))}
  (s≼s (epsilon-step n)) (Query.Part.margin (suc n))

PrefixHits : Set
PrefixHits = ∀ n → Σ ℕ (λ m → L.suc (Q.recorded n) ≼ c m)

query-necessary : First.oneStep ≼ Y → PrefixHits
query-necessary h n = cross (Q.recorded n)
  (≼-trans {b = First.oneStep} (Query.Part.margin n) h)

query-sufficient : PrefixHits → First.oneStep ≼ Y
query-sufficient hits = l≼ part
  where
  part : ∀ n → First.parts n ≼ Y
  part zero = Rows.into Asked.zero-in
  part (suc n) with hits n
  ... | m , h = ≼-trans {b = Q.recorded n}
    (≅→≼ (L.ψ⁰-≅ (Target.pass-pres (Original.matches n))))
    (≼-trans {b = L.suc (Q.recorded n)} (≼-suc (≼-refl (Q.recorded n)))
      (≼-trans {b = c m} h (Next.actual m 0)))
```
