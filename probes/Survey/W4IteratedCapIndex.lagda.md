# 新 g 刻度在统一参照的严格初段内

第四层。下标的加、乘、幂由 ε₀ 的严格初段容纳，遂能把两轮真实下界都放入同一正层原参照的严格初段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapIndex where

open import WVOne using (𝟏)
open import Data.Product using (proj₁)
open import OCF.Lean.YiRefTw2 using (Rt)
import B23RShare as Query
import Survey.EboPTOFinite as B
import Survey.W4PTOFinite as Actual
import Survey.W4RoomDerivative as G
import Survey.W4IteratedCapOrbit as Orbit
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l; s≼s; ≼-refl)
open import OCF.Align.BTBOValBase using (tr₀)
import B19IdealPowers as Pow
import B18Product as M
import B27UEpsilon as Hull
import Survey.W4ThreeTower as Gap
import Survey.W4NextLiftValue as Scale
import B19IdealProduct as Ar
import Survey.W4IteratedCapCube as Cube
open import Survey.W4IteratedCapDiagonal using (small)

depth-two : L.suc (Rt (B.tower-h 2 2)) ≼ G.g L.zero
depth-two = ≼-trans {b = L.suc (Query.parts 1)} (s≼s (proj₁ (Actual.id₂-branch 1))) Orbit.single-below

module Small = Hull.At L.zero
omega = L.ωᶜ
square = omega M.· omega
current : L.suc Scale.bound ≼ tr₀ Cube.source
current = small (Scale.exponent L.+ square) (Small.finite {Scale.exponent L.+ square}
  (Small.sumC {Scale.exponent} {square} (Small.powC {omega} {omega} Pow.omega-pos o o) (Small.mulC {omega} {omega} o o)))
  where o = Gap.Gap.omega-in L.zero

width = Ar.power Scale.exponent omega
latest : L.suc (G.g (width M.· omega)) ≼ tr₀ Cube.source
latest = small (width M.· omega) (Small.finite {width M.· omega} (Small.mulC {width} {omega}
  (Small.powC {Scale.exponent} {omega} (Pow.positive Pow.omega-pos omega) (Small.powC {omega} {omega} Pow.omega-pos o o) o) o))
  where o = Gap.Gap.omega-in L.zero
```
