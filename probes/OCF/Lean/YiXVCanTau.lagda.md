# YiXV YiXVCanTau
> 验收文件。层 1 的运输保持受限比较、好树与 Ω₁ 地板，字面起点域对运输封闭。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCanTau where
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; u≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O

τ : R.T₁ → R.T₁
τ = L.tr⁻ (L.s≅ L.z≅)

flat : ∀ {X} → R.Flat X → R.Flat (τ X)
flat R.fz = R.fz
flat (R.fs g) = R.fs (flat g)
flat (R.fl g) = R.fl (λ n → flat (g n))
flat R.fu = R.fu

per : ∀ {X} → R.Flat X → X L.≅ X
per R.fz = L.z≅
per (R.fs g) = L.s≅ (per g)
per (R.fl g) = L.l≅ (λ n → per (g n))
per (R.fu {y}) = L.upˡ (L.upʳ (L.≅-refl⁰ y))

τ₀⁺ : R.T₀ → R.T₀
τ₀⁺ = L.tr L.z≅
plus≈ : (y : R.T₀) → (τ₀⁺ y ≼ y) × (y ≼ τ₀⁺ y)
plus≈ y = ≅→≼ (L.tr-≅ L.z≅ (L.≅-refl⁰ y)) , ≅→≼ (L.≅-sym (L.tr-≅ L.z≅ (L.≅-refl⁰ y)))
pos⁺ : ∀ {x : R.T₀} → R.𝟙 ≼ x → R.𝟙 ≼ τ₀⁺ x
pos⁺ {x} p = ≼-trans p (proj₂ (plus≈ x))
mono⁺ : ∀ {x y : R.T₀} → x ≼ y → τ₀⁺ x ≼ τ₀⁺ y
mono⁺ {x} {y} p = ≼-trans (proj₁ (plus≈ x)) (≼-trans p (proj₂ (plus≈ y)))

mono : ∀ {X Y} → X R.≤ₚ Y → τ X R.≤ₚ τ Y
mono R.zz = R.zz
mono (R.ss q) = R.ss (mono q)
mono (R.ws q) = R.ws (mono q)
mono (R.≤l n q) = R.≤l n (mono q)
mono (R.l≤ h) = R.l≤ (λ n → mono (h n))
mono (R.ii h) = R.ii (λ x y o q → mono (h (τ₀⁺ x) (τ₀⁺ y) (pos⁺ o) (mono⁺ q)))
mono (R.i1 q) = R.i1 (mono q)
mono (R.fu {y = y} fx q) = R.fu (flat fx)
  (≼-trans (≅→≼ (L.tr⁻-≅ (L.s≅ L.z≅) (per fx))) (≼-trans q (proj₂ (O.tr⁻≈ y))))

Ωτ : O.Ω₁ R.≤ₚ τ O.Ω₁
Ωτ = R.ii (λ x y o q → R.fu R.fu
  (u≼ (≼-trans q (≼-trans (proj₂ (plus≈ y)) (proj₂ (O.tr⁻≈ (τ₀⁺ y)))))))

floor : ∀ {X} → O.Ω₁ R.≤ₚ X → O.Ω₁ R.≤ₚ τ X
floor q = R.trans Ωτ (mono q)

good : ∀ {X} → O.Gd X → O.Gd (τ X)
good O.gz = O.gz
good (O.gs g) = O.gs (good g)
good (O.gl g) = O.gl (λ n → good (g n))
good (O.gi law gb) = O.gi
  (O.sc (λ x y o q → mono (O.SC.mo law (τ₀⁺ x) (τ₀⁺ y) (pos⁺ o) (mono⁺ q)))
    (λ y o → mono (O.SC.db law (τ₀⁺ y) (pos⁺ o)))
    (mono (O.SC.po law)))
  (λ y o → good (gb (τ₀⁺ y) (pos⁺ o)))
good O.gu = O.gu

data Start : R.T₁ → Set where
  start : Start O.Ω₁
  shift : ∀ {X} → Start X → Start (τ X)
start-good : ∀ {X} → Start X → O.Gd X
start-good start = O.Gd-Ω
start-good (shift h) = good (start-good h)
start-floor : ∀ {X} → Start X → O.Ω₁ R.≤ₚ X
start-floor start = O.Ω≤Ω
start-floor (shift h) = floor (start-floor h)
```
