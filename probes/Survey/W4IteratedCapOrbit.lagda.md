# 与原询问的有限份数前缀比较

第四层。统一上界是正层参照函数 V 的首个正不动点。比较原询问的第 m 个前缀，只需验证该前缀对 V 封闭。已能在单份 Ω₂ 前缀上证明相反的严格不等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapOrbit where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁; proj₂; _,_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼l; ≅→≼; 1≼ψ⁰)
open import OCF.Align.BTBOValBase using (tr₀)
open import WVOne using (T₀; 𝟏)
import B12Omega3Cuts as Cut
import B13Target as P
import B17RefAllSource as Src
import B23RKernel as Copy
import B23RShare as Query
import B24RFixed as F
import B24RKernel as Ref
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapCube as Cube
open import Survey.W4IteratedCapShape using (value; wall; bridge)
open import Survey.W4RoomDerivative using (g)
import Survey.W4NextLiftValue as Scale
import Survey.W4RoomDiagonal as H
import Survey.W4FourthLiftValue as Index
import Survey.W4RoomDerivative as G

monotone : ∀ {x y} → x ≼ y → value x ≼ value y
monotone {x} {y} d = Cut.sandwich {s = Src.pass (Cube.native (Copy.copy x))}
  (Src.pass-down 1 (Cube.dn x (Copy.copy x) (≅→≼ (L.≅-sym (Copy.copied x)))))
  (Src.pass-up 1 (Cube.up (Copy.copy x) y (≼-trans {b = x} (≅→≼ (Copy.copied x)) d)))
  (P.pass-pres (C.Base.regular (C.ready x))) (P.pass-pres (C.Base.regular (C.ready y)))

open import Relation.Binary.PropositionalEquality using (refl)
module Orbit = F.Iteration value (λ {x} {y} d → monotone {x} {y} d) (λ f → refl)
  (1≼ψ⁰ (P.pass (C.family 𝟏))) wall (L.≅-refl⁰ wall)

self : value (tr₀ Cube.source) ≈ᵛ tr₀ Cube.source
self = ≼-trans {b = value wall} (monotone {tr₀ Cube.source} {wall} (proj₁ bridge))
         (≼-trans {b = wall} (proj₁ Orbit.fixed) (proj₂ bridge)) ,
       ≼-trans {b = wall} (proj₁ bridge) (≼-trans {b = value wall} (proj₂ Orbit.fixed)
         (monotone {wall} {tr₀ Cube.source} (proj₂ bridge)))

least : ∀ y → 𝟏 ≼ y → value y ≼ y → tr₀ Cube.source ≼ y
least y seed hit = ≼-trans {b = wall} (proj₁ bridge) (Orbit.least {v = y} seed hit)

prefix : ∀ m → value (Query.parts m) ≼ Query.parts m → tr₀ Cube.source ≼ Query.oneStep
prefix m hit = ≼-trans {b = Query.parts m} (least (Query.parts m) (1≼ψ⁰ _) hit) (≼l m (≼-refl (Query.parts m)))

single-below : L.suc (Query.parts 1) ≼ g L.zero
single-below = ≼-trans {b = Ref.H 𝟏} (Ref.grow L.zero)
  (≼-trans {b = Index.h L.zero} (≼l 0 (≼-refl (Ref.H 𝟏)))
    (≼-trans {b = Index.h (g L.zero)} (H.monotone {L.zero} {g L.zero} OCF.Align.Value.z≼)
      (proj₁ (G.enumerated L.zero))))

single : L.suc (Query.parts 1) ≼ value (Query.parts 1)
single = ≼-trans {b = g L.zero} single-below (≼-trans {b = g (Query.parts 1)}
  (Scale.start (Query.parts 1)) (C.indexed (Query.parts 1)))
```
