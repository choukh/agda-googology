# W4 第四层一次转入三级反馈的可迭代值下界

第四层，无条件。三级计算在每条零路径上都能从共同底 x 严格超过 B(x)。四级的实际轨道从 D 出发同时更新各个零槽与返回值，因而一次四级运行就包含这个更强变换的所有有限次迭代。D 与 B 的定义见[标定](W4ThreeTower.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FourthLift where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; s≼s; ≼l; l≼; ≅→≼)
open import W4Block using (iter; sS; _≤_; inc)
import W4Block as W
import W4Ops as Op
import W4Fold as F
open import W4Path using (z≤)
open import WVOne using (T₀; read; 𝟏)
open import WVTwo using (lvl2; ◃→≼)
open import WKShape using (lvl3)
import B12Terminal as T
import B12ActualSlots as Cov
import B14Tower as View
import B19PathShape as Sh
import B20Room as Room
import B20OldStage as St
import B24AFirst as Seed
import B24ROrbit as O
import Survey.W4ThreeReturn as R
import Survey.W4FixedDepth as Site
import Survey.W4FourthLiftPaths as Path

gain : T₀ → T₀
gain x = L.suc (R.series x)

route : ∀ (r : T.Run lvl3) w → read (T.value r) ≼ View.valueAt r w
route r w = ≅→≼ (Sh.read-shape (Path.change 3 (T.Run.ok r) (T.Run.bs r) (z≤ lvl3) w (T.Run.β r) (proj₁ (Op.Ωt lvl3))))

third-step : ∀ (r : T.Run lvl3) → Cov.Covered r → ∀ x → Room.Room r x → ∀ w → gain x ≼ View.valueAt r w
third-step r cv x high w = ≼-trans {b = L.suc (A.sample 0)} (s≼s (A.funded x high))
  (≼-trans {b = A.sample 1} (A.rise 0) (≼-trans {b = read (T.value r)} (A.upper 1) (route r w)))
  where module A = R.Actual r cv

third-floor : ∀ (r : T.Run lvl3) → Cov.Covered r → ∀ w → O.D ≼ View.valueAt r w
third-floor r cv w = ≼-trans {b = read (T.value r)} (Seed.At.physical r cv) (route r w)

module Fourth (r : T.Run (Path.level 4)) (cv : Cov.Covered r) where
  module A = St.At sS (λ _ → lvl2) r cv
  w = z≤ lvl3
  a = T.Run.β r
  stage = A.setup w a (T.Run.oneβ r)
  started : Room.Room (stage 0) O.D × O.D ≼ read (proj₁ (T.Run.β (stage 0)))
  started = (λ u → ≼-trans (third-floor (View.reset A.r₀ (T.Run.bs A.r₀ W.zero u) (T.Run.oneB A.r₀ u)) A.sub-covered u)
                       (A.weaken _ u _)) ,
            ≼-trans (third-floor A.r₀ A.sub-covered w) (A.weaken _ w _)

  walk : ∀ n → Room.Room (stage n) (iter gain O.D n) × iter gain O.D n ≼ read (proj₁ (T.Run.β (stage n)))
  walk zero = started
  walk (suc n) = (λ u → ≼-trans (third-step (View.reset s (T.Run.bs s W.zero u) (T.Run.oneB s u)) (A.cover n) x room u)
                         (A.weaken _ u _)) ,
                 ≼-trans (third-step s (A.cover n) x room w) (A.weaken _ w _)
    where
    s = stage n
    x = iter gain O.D n
    room = proj₁ (walk n)

  inside : ∀ n → iter gain O.D (suc n) ≼ read (T.value r)
  inside n = ≼-trans {b = read (proj₁ (T.Run.β (stage (suc n))))} (proj₂ (walk (suc n))) (A.send (A.every refl) a n)

  full : L.lim (λ n → iter gain O.D (suc n)) ≼ read (T.value r)
  full = l≼ inside

limit₄ : T₀
limit₄ = L.lim (λ n → iter gain O.D (suc n))

old-below : L.suc (R.series O.D) ≼ limit₄
old-below = ≼l 0 (≼-refl _)

fourth-sub : limit₄ ≼ read (T.value Site.Fourth.sub)
fourth-sub = Fourth.full Site.Fourth.sub Site.Fourth.covered

import Survey.W4LegacyFeedback as Live
coordinate : L.suc limit₄ ≼ Live.Live.leaf 4 1
coordinate = ≼-trans {b = L.suc (read (T.value Site.Fourth.sub))} (s≼s fourth-sub) Site.fourth-return
```
