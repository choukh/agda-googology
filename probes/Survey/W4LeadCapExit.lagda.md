# g 的统一参照严格低于 a₂ 的第 1 枝

第四层。原 src 二层闭项 ψ₀ψ₂(C) 落在原 EBO 项 a₂[1] 的第一次回灌之内。该回灌严格低于整枝。于是对每个 ξ<ε₀，已有的 g(ξ) 均在此原分枝以下。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapExit where

open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Empty using (⊥)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import Data.Product using (proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≅→≼; ≼-refl; ≼l; s≼s)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Lean.YiRefTw2 using (Rt)
open import WVOne using (𝟏; T₀)
open import YiLAB7Replay using (Ω₂ᴸ)
import B12LimitSrc as M
import B12Omega3Cuts as Cut
import B13Target as P
import B17RefAllSource as Src
import B22MovingIndex as E
import B24RRows as Q
import Survey.W4PTOFinite as Named
import Survey.W4OriginalIteratedBound as Old
import Survey.W4OriginalVeblenRows as Row
import Survey.W4IteratedCapShape as Wall
import Survey.W4RoomDerivative as G
import Survey.W4NextLiftValue as Scale
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapCube as Cube
import Survey.W4IteratedCapDiagonal as Known
import Survey.W4LeadCapBranch as Z
import Survey.W4LeadCapPositive as Target
import Survey.W4LeadCapPrograms as J
import Survey.W4LeadCapMeaning as Shape

upper : C.value Cube.level ≼ Target.fold (Target.stage 2)
upper = ≼-trans {b = C.value (J.roof J.base Ω₂ᴸ)}
  (Cut.sandwich {s = Src.pass Cube.cube} (Src.pass-down 1 (M.Aligned.dn Cube.aligned)) (Src.pass-up 1 J.cube)
    (P.pass-pres (M.Aligned.regular Cube.aligned)) (P.pass-pres (P.refl-left Shape.roof)))
  (≅→≼ (L.ψ⁰-≅ (P.pass-pres Shape.roof)))

zero-branch : Z.v 1 ≈ᵛ Q.gain 1 𝟏
zero-branch = Named.branch-value Old.next-h refl (L.lim (λ n → Q.iterate 1 (suc n))) (L.≅-trans Target.branch (Q.shape 1)) 0 (Z.branch 0) (Z.cert 1)

first : tr₀ Cube.source ≼ Z.v 1
first = ≼-trans {b = C.value Cube.level} (proj₁ Cube.exact)
  (≼-trans {b = Target.fold (Target.stage 2)} upper
    (≼-trans {b = Q.gain 1 𝟏} (Target.stages 1) (proj₂ zero-branch)))

floor : L.suc (Rt Row.d-h) ≼ tr₀ Cube.source
floor = ≼-trans {b = G.g L.zero} Row.base-strict
  (≼-trans {b = Wall.wall} Known.first (proj₂ Wall.bridge))

strict : L.suc (tr₀ Cube.source) ≼ Rt Old.next-h
strict = ≼-trans {b = L.suc (Z.v 1)} (s≼s first) (≼-trans {b = Z.v 2} (Z.climb 1)
  (≼-trans (≼l 1 (≼-refl (Z.v 2))) (proj₂ Z.exact)))

calibrated : ∀ (x : T₀) → x ≼ tr₀ Cube.source → G.g x ≼ Z.v 1
calibrated x h = ≼-trans {b = G.g (tr₀ Cube.source)} (Scale.monotone {x} {tr₀ Cube.source} h)
  (≼-trans {b = tr₀ Cube.source} (proj₁ Known.source-fixed) first)

excludes : ∀ (x : T₀) → x ≼ tr₀ Cube.source → Rt Old.next-h ≼ G.g x → ⊥
excludes x lo high = s≼-irrefl (Z.v 1) (≼-trans {b = Z.v 2} (Z.climb 1)
  (≼-trans {b = Rt Old.next-h} (≼-trans (≼l 1 (≼-refl (Z.v 2))) (proj₂ Z.exact))
    (≼-trans {b = G.g x} high (calibrated x lo))))

small : ∀ (x : T₀) → L.suc x ≼ E.above L.zero → L.suc (G.g x) ≼ Z.v 1
small x e = ≼-trans {b = tr₀ Cube.source} (Known.small x e) first
```
