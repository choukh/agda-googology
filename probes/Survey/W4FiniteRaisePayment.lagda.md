# 小下标反馈何时能接收原名升层

第四层，无条件。对任意有限下标的可数标准项 t，提升其每个正下标所得的值可由某个 ξ≤c 的 g(ξ) 盖住，当且仅当 t<ψ₀ψ₁(Ω₁·2)。整个开初段共用 g(0) 与同一个实际反馈地址。c 为已独立校准的 g 不动点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaisePayment where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; HC; _<ᵀ_; hd<; ar<; tl<; []<)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; ≼-trans; ≼-refl; ≼-suc; s≼s; ≼l; l≼)
open import WVOne using (T₀)
import Survey.EboPTOFinite as B
import Survey.W4FiniteRaiseNames as R
import Survey.W4FiniteRaiseCut as C
import Survey.W4RoomDerivative as G
import Survey.W4RoomDiagonal as First
import Survey.W4RouteTests as Actual
import Survey.W4OriginalVeblenRows as Row
import Survey.W4LeadCapExit as Cap
import Survey.W4IteratedCapCube as Cube
import Survey.W4OriginalIteratedBound as Old
import Survey.W4FixedDepth as Fixed
import Survey.W4PTOFinite as Named
import B12BtboCut as Cut

δ = Rt (C.cert 1)
ceiling = tr₀ Cube.source

paid : L.suc δ ≼ G.g L.zero
paid = ≼-trans {b = L.suc (Rt Row.d-h)} (s≼s (tree-≼ refl (C.cert 1) Row.d-h)) Row.base-strict

same-address : L.suc δ ≼ Actual.c 1
same-address = ≼-trans {b = G.g L.zero} paid (≼-trans {b = First.fixedPoint} (proj₁ G.base)
  (≼-trans {b = L.suc First.fixedPoint} (≼-suc (≼-refl _)) First.strict))

Small : ∀ {t} → HC (R.raise t) → Set
Small h = Σ T₀ (λ x → x ≼ ceiling × Rt h ≼ G.g x)

inside : ∀ {t} (nt : NF t) (ct : Ctbl t) → t <ᵀ C.A 0 → (h : HC (R.raise t)) → Small h
inside nt ct p h = L.zero , z≼ , ≼-trans {b = δ}
  (≼-trans (≼-suc (≼-refl _)) (C.below 0 nt ct p h)) (≼-trans (≼-suc (≼-refl _)) paid)

-- 在端点，提升后的原名恰是旧查询中的两份 Ω₂。
edge : ∀ {n t} → B.Indices n t → NF t → Ctbl t → C.A 0 ≤ᵀ t →
  (h : HC (R.raise t)) → Rt Old.two-h ≼ Rt h
edge ix nt ct (inj₂ refl) h = tree-≼ refl Old.two-h h
edge ix nt ct (inj₁ lt) h = ≼-trans (≼-suc (≼-refl _))
  (mono<ⁿ Old.two-nf (R.normal ix nt) (R.count ct) Old.two-h h (R.strict lt))

outside : ∀ {n t} (ix : B.Indices n t) (nt : NF t) (ct : Ctbl t) (h : HC (R.raise t)) →
  Small h → t <ᵀ C.A 0
outside {t = t} ix nt ct h (x , low , high) with tri t (C.A 0)
... | inj₁ p = p
... | inj₂ sides = ⊥-elim (Cap.excludes x low (≼-trans {b = Rt Old.two-h}
  (≼-trans (≼-suc (≼-refl _)) Old.next<two) (≼-trans {b = Rt h} (edge ix nt ct (flip sides) h) high)))
  where
  flip : ∀ {a b} → (b ≡ a) ⊎ (a <ᵀ b) → a ≤ᵀ b
  flip (inj₁ refl) = inj₂ refl
  flip (inj₂ p) = inj₁ p

-- Aⱼ 自身也在 ψ₀(Ω_ω) 共尾，并且每个 Aⱼ 的下一行都由同一基本列公式给出。
value = λ i → Rt (C.cert i)
above-sample : ∀ i → L.suc (Fixed.sample i) ≼ value i
above-sample i = mono<ⁿ (B.nf-collapsed (suc i) 2) (C.standard i) (c∷ c[])
  (B.tower-h (suc i) 2) (C.cert i) (hd< (ar< (hd< (ar< (tl< []<)))))

below-row : ∀ i → L.suc (value i) ≼ Cut.finite (suc (suc i))
below-row i = ≼-trans {b = Rt (B.row-h (suc i))}
  (mono<ⁿ (C.standard i) (B.nf-row (suc i)) (c∷ c[]) (C.cert i) (B.row-h (suc i)) (C.row< i))
  (proj₁ (Named.scale (suc i)))

cofinal : Cut.omega-cut ≈ᵛ L.lim value
cofinal = ≼-trans {b = L.lim Fixed.sample} (proj₁ Fixed.cofinal)
  (l≼ λ i → ≼l i (≼-trans (≼-suc (≼-refl _)) (above-sample i))) ,
  l≼ λ i → ≼l {f = Cut.finite} (suc (suc i)) (≼-trans (≼-suc (≼-refl _)) (below-row i))
```
