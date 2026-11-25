# 实际的第 4 座塔容纳一列更高的不动点

第四层。将三份前缀的实际询问放回编号 4 的标准塔，比较其第零个返回和上一轮全部有限迭代的上确界。[同址反馈与投影](W4ThreeReturn.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ThreeTower where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼lim⁻; ≼l; l≼; s≼s; ≅→≼)
open import WVOne using (T₀; 𝟏; read)
open import WKShape using (lvl3)
open import W4Block using (tw; iter)
open import W4Path using (Ok-tw)
open import Relation.Binary.PropositionalEquality using (_≡_)
import B12ActualSlots as Cover
import B20Room as Room
import B12Terminal as T
import B20StandardInside as Std
import B20UnitSecond as Unit
import B21TowerGrowth as Tower
import B21StandardShape as Shape
import B22MovingIndex
import B22TowerCut as Cut
import B24RKernel as Kernel
import B24ROrbit as Seed
import B25AOrbit as OldTower
import Survey.W4PTOSeededQuery as Restart
import Survey.W4ThreeCopies as Ref
open import Survey.W4ThreeReturn using (module Actual; series)

record Site (seed bound : T₀) : Set where
  field
    run : T.Run lvl3
    covered : Cover.Covered run
    slots : Room.Room run (L.suc seed)
    below : read (T.value run) ≼ bound

module Middle (r : T.Run (tw 2)) (eq : T.Run.ok r ≡ Ok-tw 2) (cv : Cover.Covered r)
              (q : T₀) (high : Room.Room r q) where
  module U = Unit.At.Three r eq cv q high
  opaque
    site : Site q (read (T.value r))
    site = record { run = U.run ; covered = U.covered ; slots = U.all ; below = U.value }

widen : ∀ {q a b} → Site q a → a ≼ b → Site q b
widen {a = a} s h = record { run = Site.run s ; covered = Site.covered s ; slots = Site.slots s
  ; below = ≼-trans {b = a} (Site.below s) h }

opaque
  find : ∀ m → Site (Std.std (Tower.At.k m)) (Std.std (Tower.At.top m))
  find m = widen {a = read (T.value R.s)} (Middle.site R.s R.cert R.cv (Std.std (Tower.At.k m)) R.high) R.below
    where module R = Tower.At.Standard m

module InTower (m : ℕ) where
  place = find m
  module Query = Actual (Site.run place) (Site.covered place)
  top = Tower.At.top m
  held : ∀ n → Query.sample n ≼ Std.std top
  held n = ≼-trans {b = read (T.value (Site.run place))} (Query.upper n) (Site.below place)
  first : ∀ x → x ≼ L.suc (Std.std (Tower.At.k m)) → series x ≼ Query.sample 0
  first x h = Query.funded x (λ w → ≼-trans {b = L.suc (Std.std (Tower.At.k m))} h (Site.slots place w))
  finite-first : ∀ x → x ≼ L.suc (Std.std (Tower.At.k m)) → Restart.next x ≼ Query.outcomes 0
  finite-first x h = Query.finite-funded x
    (λ w → ≼-trans {b = L.suc (Std.std (Tower.At.k m))} h (Site.slots place w)) 0
  finite-bound : ∀ j → Query.outcomes j ≼ Std.std top
  finite-bound j = ≼-trans {b = Query.sample 0}
    (≼-trans {b = L.lim Query.outcomes} (≼l j (≼-refl _)) (≅→≼ (L.≅-sym Query.first-value))) (held 0)
  benchmark : (∀ n → Ref.test n ≼ Query.sample n) → L.suc (B22MovingIndex.above Ref.target) ≼ Cut.cut
  benchmark covers = Ref.benchmark top (λ n → ≼-trans {b = Query.sample n} (covers n) (held n))
  strict-first : ∀ x → x ≼ L.suc (Std.std (Tower.At.k m)) → L.suc (series x) ≼ Std.std top
  strict-first x h = ≼-trans {b = L.suc (Query.sample 0)} (s≼s (first x h))
    (≼-trans {b = Query.sample 1} (Query.rise 0) (held 1))

module Four = InTower 0
physical : series Seed.D ≼ Four.Query.sample 0
physical = Four.first Seed.D (≼-suc (OldTower.point 0))

first-outcome : Restart.next Seed.D ≼ Four.Query.outcomes 0
first-outcome = Four.finite-first Seed.D (≼-suc (OldTower.point 0))

strict-in-four : L.suc (series Seed.D) ≼ Std.std 4
strict-in-four = Four.strict-first Seed.D (≼-suc (OldTower.point 0))
```

这个第零次实际返回与旧见证可作严格比较。任意起点上方第一个 $H$ 不动点，已经严格高过该起点上方第一个 ε 枚举不动点。

```agda
import B13Target as P
import B18Product as Product
import B19IdealArithmetic as Ar
import B27UEpsilon as Inside
import Survey.W4ClockCeiling as Cap
import Survey.W4ClockClosure as Stage
import Survey.W4RouteTests as Test

module One = Cap.At 0
same : ∀ x → Kernel.H x L.≅ One.v x
same x = L.ψ⁰-≅ (P.pass-pres (L.add-≅ {σ = λ ()} {σ′ = λ r → L.suc (L.suc r)}
  (L.Ω-refl _) (L.≅-refl⁰ x)))

jump-step : ∀ u x → x ≼ Kernel.H u → Stage.jump x ≼ Kernel.H (L.suc u)
jump-step u x h = ≼-trans {b = One.v (L.suc u)}
  (One.Step.update u x (≼-trans {b = Kernel.H u} h (≅→≼ (same u))))
  (≅→≼ (L.≅-sym (same (L.suc u))))

module Gap (x : T₀) where
  module H = Inside.At x
  omega-in : H.In L.ωᶜ
  omega-in = H.down {L.ωᶜ} {Ar.norm 𝟏} (Product.one-left L.ωᶜ)
    (H.expC {𝟏} (H.sucC {L.zero} (H.down {L.zero} {x} OCF.Align.Value.z≼ H.seed)))
  tail : L.suc (x L.+ L.ωᶜ) ≼ Kernel.H (L.suc x)
  tail = ≼-trans {b = B22MovingIndex.above x} (H.finite {x L.+ L.ωᶜ} (H.sumC {x} {L.ωᶜ} H.seed omega-in))
    (≼-trans {b = Stage.jump x} (Test.clock-below x (B22MovingIndex.above x)) (jump-step x x (Restart.inflation x)))
  front : Stage.hull x ≼ Kernel.H (x L.+ L.ωᶜ)
  front = l≼ λ n → ≼l n (part n)
    where
    part : ∀ n → Stage.stages-from x n ≼ Kernel.H (x L.+ L.natᶜ n)
    part zero = Restart.inflation x
    part (suc n) = jump-step (x L.+ L.natᶜ n) (Stage.stages-from x n) (part n)
  strict : L.suc (Stage.hull x) ≼ Restart.next x
  strict = ≼-trans {b = L.suc (Kernel.H (x L.+ L.ωᶜ))} (s≼s front)
    (≼-trans {b = Kernel.H (L.suc (x L.+ L.ωᶜ))} (Kernel.grow (x L.+ L.ωᶜ))
      (≼-trans {b = Kernel.H (Kernel.H (L.suc x))}
        (Kernel.monotone {L.suc (x L.+ L.ωᶜ)} {Kernel.H (L.suc x)} tail) (≼l 1 (≼-refl _))))

next-in-series : ∀ x → L.suc (Restart.next x) ≼ series x
next-in-series x = ≼l 1 (Restart.above (Restart.next x))

fixed-series : ∀ x → Kernel.H (series x) ≈ᵛ series x
fixed-series x = (l≼ λ n → ≼l n (proj₁ (Restart.fixed (iter Restart.next x n)))) , Restart.inflation (series x)
```

一次三级运行容纳整列不动点，因此独立塔上确界的严格初段对这次取上确界也封闭。

```agda
slots-above : ∀ m (x : T₀) → x ≼ Std.std m → x ≼ L.suc (Std.std (Tower.At.k m))
slots-above m x h = ≼-suc (≼-trans {b = Std.std (suc m)}
  (≼-trans {b = Std.std m} h (≼-trans (≼-suc (≼-refl _)) (Shape.rise m)))
  (≼-trans (≼-suc (≼-refl _)) (Shape.rise (suc m))))

bounded : ∀ m x → x ≼ Std.std m → L.suc (series x) ≼ Std.std (Tower.At.top m)
bounded m x h = InTower.strict-first m x (slots-above m x h)

closed : ∀ x → L.suc x ≼ Cut.cut → L.suc (series x) ≼ Cut.cut
closed x h with ≼lim⁻ {a = x} {f = Std.std} h
... | m , p = ≼l (Tower.At.top m) (bounded m x (≼-trans (≼-suc (≼-refl x)) p))
```

允许提高塔号时，每座塔只取一次有限返回就对 $K$ 共尾。三份参照的所有行仍须共用一个塔号。

```agda
single = λ m → InTower.Query.outcomes m 0
capture : ∀ m (x : T₀) → x ≼ Std.std m → L.suc x ≼ single m
capture m x h = ≼-trans {b = Restart.next x} (Restart.above x) (InTower.finite-first m x (slots-above m x h))

cofinal : Cut.cut ≈ᵛ L.lim single
cofinal = (l≼ λ m → ≼l m (≼-trans (≼-suc (≼-refl _)) (capture m (Std.std m) (≼-refl _)))) ,
  (l≼ λ m → ≼l (Tower.At.top m) (InTower.finite-bound m 0))

Witness : Set
Witness = Σ ℕ (λ m → ∀ n → Ref.test n ≼ single m)

to-witness : L.suc (B22MovingIndex.above Ref.target) ≼ Cut.cut → Witness
to-witness h with ≼lim⁻ {a = B22MovingIndex.above Ref.target} {f = Std.std} h
... | m , p = m , λ n → ≼-trans {b = Std.std m} (Ref.from-tower m enough n)
  (≼-trans {b = L.suc (Std.std m)} (≼-suc (≼-refl _)) (capture m (Std.std m) (≼-refl _)))
  where
  enough : Ref.target ≼ Std.std m
  enough = ≼-trans {b = L.suc (B22MovingIndex.above Ref.target)}
    (≼-suc (≼-trans {b = L.suc Ref.target} (≼-suc (≼-refl _)) (B22MovingIndex.strict Ref.target))) p

from-witness : Witness → L.suc (B22MovingIndex.above Ref.target) ≼ Cut.cut
from-witness (m , h) = Ref.benchmark (Tower.At.top m) λ n →
  ≼-trans {b = single m} (h n) (InTower.finite-bound m 0)

first-required : ∀ m → (∀ n → Ref.test n ≼ single m) → L.suc Ref.two ≼ single m
first-required m h = ≼-trans {b = Ref.test 0} Ref.two-in-first (h 0)
```
