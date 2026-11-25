# 在 a₂[1] 首次回灌里保留一份额外的 Ω₁

第四层。正层再取一次原程序中实际存在的有限迭代，使统一上界 c 的后继也落在 a₂[1][0] 内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapStrict where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.BTBOValUp as U
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; s≼s; ≅→≼)
open import WVOne using (𝟏)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import B12LimitSrc as M
import B12Omega3Ref as R
import B12Omega3Cuts as Cut
import B13Target as P
import B15RefAlgebra as A
import B17RefAllSource as Src
import B17RefExp as E
import B19OldSource as Sync
import B24RRows as Q
import Survey.W4FourthLiftCeiling as Old
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapCube as Cube
import Survey.W4LeadCapPrograms as J
import Survey.W4LeadCapPositive as Cap
import Survey.W4LeadCapMeaning as Shape
import Survey.W4LeadCapExit as Exit
import Survey.W4LeadCapBranch as Z

room : C.Base Cube.level
room = C.base (M.Aligned.regular Cube.aligned)
  (U.Mir (λ y _ → C.Base.start (C.ready y)))
  (λ left → ≼l 0 (C.Base.copies (C.ready 𝟏) left))

levels : ℕ → J.Op
levels zero p = L.add p L.suc (Cap.stage 1)
levels (suc zero) = J.roof J.base
levels (suc (suc n)) p = L.add p L.suc (Cap.stage (suc (suc (suc n))))
bundle : J.Op
bundle p = L.lim (λ n → levels n p)

regular : ∀ n → Cap.stage n L.≅ Cap.stage n
regular = L.iter-R L._≅_ {G = A.E Ω₁ᴸ} {G′ = A.E Ω₁ᴸ} (E.wide (L.Ω-refl _)) (L.Ω-refl _)
tag : ∀ n → Shape.Adds (levels n) (Cap.stage (suc n))
tag zero d = L.add-≅ {σ = L.suc} {σ′ = L.suc} d (regular 1)
tag (suc zero) d = L.lᵢ≅ L.z≅ (λ x y r → Shape.higher r {J.base} {Ω₁ᴸ}
  (λ w → L.add-≅ {σ = L.suc} {σ′ = L.suc} w (L.Ω-refl _)) (L.Ω-refl _) d)
tag (suc (suc n)) d = L.add-≅ {σ = L.suc} {σ′ = L.suc} d (regular (suc (suc (suc n))))
all : Shape.Adds bundle (A.Γ Ω₁ᴸ)
all d = L.l≅ (λ n → tag n d)
module Count = Shape.Count {bundle} {A.Γ Ω₁ᴸ} all (L.l≅ (λ n → regular (suc n)))

cost : J.Cost bundle
cost {p = p} d = U.Mlr 1 (U.Mir λ { .𝟏 (L.s≅ L.z≅) → U.Mlr 1 (J.in-wide J.base 1 {p = p} (J.spend d)) })

model = M.plus Cube.aligned Sync.omega-one
enough : C.value (Old.more Cube.level) ≼ Cap.fold ((A.Γ Ω₁ᴸ) L.+ (A.Γ Ω₁ᴸ))
enough = ≼-trans {b = C.value (bundle (bundle Ω₂ᴸ))}
  (Cut.sandwich {s = Src.pass (Cube.cube Src.S.+ Old.unit)} (Src.pass-down 1 (M.Aligned.dn model))
    (Src.pass-up 1 (cost {p = bundle Ω₂ᴸ} (U.Mlr 1 J.cube)))
    (P.pass-pres (M.Aligned.regular model)) (P.pass-pres (P.refl-left tagged)))
  (≅→≼ (L.ψ⁰-≅ (P.pass-pres tagged)))
  where tagged = Count.eq 2 (L.Ω-refl (L.suc (L.suc L.zero)))

double : Cap.fold ((A.Γ Ω₁ᴸ) L.+ (A.Γ Ω₁ᴸ)) ≼ Cap.fold (A.H 𝟏 Ω₁ᴸ)
double = ≼l 2 (≼l 0 (≼l 0 (≼l 2 (≼-refl _))))

strict : L.suc (tr₀ Cube.source) ≼ Z.v 1
strict = ≼-trans {b = L.suc (C.value Cube.level)} (s≼s (proj₁ Cube.exact))
  (≼-trans {b = C.value (Old.more Cube.level)} (C.rise Cube.level room)
    (≼-trans {b = Cap.fold ((A.Γ Ω₁ᴸ) L.+ (A.Γ Ω₁ᴸ))} enough
      (≼-trans {b = Cap.fold (A.H 𝟏 Ω₁ᴸ)} double (≼-trans {b = Q.gain 1 𝟏} Cap.picked (proj₂ Exit.zero-branch)))))
```
