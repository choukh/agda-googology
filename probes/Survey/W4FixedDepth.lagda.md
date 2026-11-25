# 固定两次正下标塌缩检验 W4 的有限层

第四层，无条件。对每个正整数 n 取 bₙ = |D₀Dₙ²0|，则 ψ₀(Ωₙ) < bₙ < ψ₀(Ωₙ₊₁)。整树达到 ψ₀(Ω_ω) 恰当每个 bₙ 都在某座塔的第零次实际反馈之下。n=2 有具体塔号，n=3 的实际见证开放。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FixedDepth where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; s≼s; ≼l; l≼; ⊑→≼)
open import OCF.Align.EboLeanDef using (hd<; ar<)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Lean.YiRefTw2 using (Rt)
open import WVOne using (T₀; read)
import W4Block as W
import B12ActualSlots as Slots
import B12BtboCut as C
import B12Terminal as T
import B17CellNext as Feedback
import B29SFirst as First
import Survey.EboPTOFinite as B
import Survey.W4PTOFinite as P
import Survey.W4PTOGamma as G
import Survey.W4RouteTests as A
import Survey.W4LegacyFeedback as Live

-- 自然数参数 i 代表正下标 n = i + 1。
sample : ℕ → T₀
sample i = Rt (B.tower-h (suc i) 2)

lower : ∀ i → L.suc (C.finite (suc i)) ≼ sample i
lower i = ≼-trans {b = L.suc (Rt (B.row-h i))}
  (s≼s (proj₂ (P.scale i)))
  (mono<ⁿ (B.nf-row i) (B.nf-collapsed (suc i) 2) (c∷ c[]) (B.row-h i) (B.tower-h (suc i) 2)
    (hd< (ar< (B.rise (suc i) 1))))

upper : ∀ i → L.suc (sample i) ≼ C.finite (suc (suc i))
upper i = ≼-trans {b = Rt (B.row-h (suc i))}
  (mono<ⁿ (B.nf-collapsed (suc i) 2) (B.nf-row (suc i)) (c∷ c[]) (B.tower-h (suc i) 2) (B.row-h (suc i))
    (hd< (ar< (B.small (B.tower-indices (suc i) 2)))))
  (proj₁ (P.scale (suc i)))

cofinal : C.omega-cut ≈ᵛ L.lim sample
cofinal = l≼ cover , l≼ (λ i → ≼l {f = C.finite} (suc (suc i)) (≼-trans (≼-suc (≼-refl _)) (upper i)))
  where
  positive : ∀ i → C.finite (suc i) ≼ L.lim sample
  positive i = ≼l {f = sample} i (≼-trans (≼-suc (≼-refl _)) (lower i))
  cover : ∀ k → C.finite k ≼ L.lim sample
  cover zero = ≼-trans {b = C.finite 1} (⊑→≼ (C.finite 0) (L.Ψ⁰0 (L.natᴵ 1))) (positive 0)
  cover (suc i) = positive i

Hits : Set
Hits = ∀ i → Σ ℕ (λ m → L.suc (sample i) ≼ A.c m)

necessary : C.omega-cut ≼ A.Y → Hits
necessary h i = A.cross (sample i) (≼-trans {b = C.omega-cut}
  (≼l {f = C.finite} (suc (suc i)) (upper i)) h)

sufficient : Hits → C.omega-cut ≼ A.Y
sufficient h = ≼-trans {b = L.lim sample} (proj₁ cofinal) (l≼ λ i →
  ≼-trans {b = L.suc (sample i)} (≼-suc (≼-refl _))
    (≼-trans {b = A.c (proj₁ (h i))} (proj₂ (h i)) (Feedback.actual (proj₁ (h i)) 0)))

second : L.suc (sample 1) ≼ A.c 1
second = ≼-trans {b = First.f 2} G.first-unit
  (≼-trans {b = First.S} (≼l {f = First.f} 2 (≼-refl _))
    (≼-trans {b = L.suc First.S} (≼-suc (≼-refl _)) A.at-one))

module Fourth = Live.First W.sS _ (T.finiteRun 4) (Slots.all-finite 4)

fourth-return : L.suc (read (T.value Fourth.sub)) ≼ Live.Live.leaf 4 1
fourth-return = Fourth.strict
```
