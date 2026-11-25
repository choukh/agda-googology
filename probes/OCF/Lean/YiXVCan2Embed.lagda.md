# YiXV: 提升树与加法的比较
> 验收文件。档位：编译定理。沿 YiOverOps 的好树证据展开提升；up(Ω₁+Ω₁) 不高于 Ω₂+Ω₂ 的实例已填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Embed where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼-trans; s≼s; z≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Add as CA
import OCF.Lean.YiXVCanTau as T

one-up : Le one (L.up L.zero O.𝟙₁)
one-up = trans (s≤ (z≤ (gu O.gz))) (uS≤ O.gz)

normal : ∀ {f} → O.SC f → (∀ y → R.𝟙 OCF.Align.Value.≼ y → O.Gd (f y)) →
  Gd (L.limᵢ (L.suc L.zero) (λ y → L.up L.zero (f y)))
normal {f} law gb = gn₀ (sc₀
  (λ x y o q → u≤ (gb x o) (gb y (≼-trans o q)) (O.SC.mo law x y o q))
  (λ x o → trans (uS≤ (gb x o)) (u≤ (O.gs (gb x o)) (gb (L.suc x) (s≼s z≼)) (O.SC.db law x o)))
  (trans one-up (u≤ (O.gs O.gz) (gb R.𝟙 (≼-refl _)) (O.SC.po law))))
  (λ y o → gu (gb y o))

ground : ∀ {X} → O.Gd X → (z : R.T₀) → Le (L.up L.zero (L.add X (λ q → L.suc q) z)) (L.add (L.up L.zero X) A.σ₀ z)
ground gx L.zero = refl (gu gx)
ground gx (L.suc z) = trans (pack (gu (O.gs (O.Gd-add⁰ gx z))) (gs (gu (O.Gd-add⁰ gx z))) (uS⁻ (O.Gd-add⁰ gx z)))
  (s≤ (ground gx z))
ground gx (L.lim f) = trans
  (pack (gu (O.gl (λ n → O.Gd-add⁰ gx (f n)))) (gl (λ n → gu (O.Gd-add⁰ gx (f n)))) (uL (λ n → O.Gd-add⁰ gx (f n))))
  (pack (gl (λ n → gu (O.Gd-add⁰ gx (f n)))) (gl (λ n → M.good₀ (gu gx) (f n)))
    (ll (λ n → pack (gu (O.Gd-add⁰ gx (f n))) (gl (λ m → M.good₀ (gu gx) (f m))) (lr n (ground gx (f n))))))
ground gx (L.limᵢ () f)
ground gx (L.up () y)

plus : ∀ {X Y} → O.Gd X → O.Gd Y → Le (L.up L.zero (X L.+ Y)) (L.up L.zero X L.+ L.up L.zero Y)
plus gx O.gz = refl (gu gx)
plus gx (O.gs gy) = trans (pack (gu (O.gs (O.Gd-+ gx gy))) (gs (gu (O.Gd-+ gx gy))) (uS⁻ (O.Gd-+ gx gy))) (s≤ (plus gx gy))
plus gx (O.gl gy) = trans
  (pack (gu (O.gl (λ n → O.Gd-+ gx (gy n)))) (gl (λ n → gu (O.Gd-+ gx (gy n)))) (uL (λ n → O.Gd-+ gx (gy n))))
  (pack (gl (λ n → gu (O.Gd-+ gx (gy n)))) (gl (λ n → M.good₁ (gu gx) (gy n)))
    (ll (λ n → pack (gu (O.Gd-+ gx (gy n))) (gl (λ m → M.good₁ (gu gx) (gy m))) (lr n (plus gx (gy n))))))
plus gx (O.gi {f = f} law gb) = trans
  (pack (gu (O.Gd-+ gx (O.gi law gb))) (normal (O.SC-+ (O.reflₚ gx) law) (λ y o → O.Gd-+ gx (gb y o)))
    (uN (O.Gd-+ gx (O.gi law gb))))
  (pack (normal (O.SC-+ (O.reflₚ gx) law) (λ y o → O.Gd-+ gx (gb y o))) (M.good₁ (gu gx) (O.gi law gb))
    (nn₀ (λ x y o q → trans (plus gx (gb x o))
      (M.tail (refl (gu gx)) (gb x o) (gb y (≼-trans o q)) (O.SC.mo law x y o q)))))
plus gx O.gu = ground gx _

up-Ω : Le (L.up L.zero O.Ω₁) F.Ω₂
up-Ω = pack (gu O.Gd-Ω) Gd-Ω₂ (aa₁ (λ z hz → u≤ O.Gd-Ω (T.start-good hz) (T.start-floor hz)))

sample : Le (L.up L.zero (O.Ω₁ L.+ O.Ω₁)) (F.Ω₂ L.+ F.Ω₂)
sample = trans (plus O.Gd-Ω O.Gd-Ω) (CA.plus up-Ω up-Ω)
```
