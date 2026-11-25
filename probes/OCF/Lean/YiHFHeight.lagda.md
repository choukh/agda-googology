# 带高度族：由高度值传递下界
非验收文件；`height-chain` 是对所有起点与链点的充分条件，`feedback-instance` 实填该条件。
复用 `CrossNextSum.ofL-lvl`、`CrossMInst.val≼T`、`TLOneThm.below-chain`；不改树与证书。
没有给出目标参照树到链高度的界，故不声称新增强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHFHeight where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level using (Ordᴵ; Ordᶜ; zero; HS; toLevel; ≅-sym)
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos using (Code; Pos; cs; end; val)
open import OCF.Align.LadderOrdCert using (Gᵖ)
import OCF.Align.LadderOrdCode as L
import OCF.Align.ValueJudgeBase as V
open import OCF.Align.CrossNextSum using (ofL; ofL-lvl)
open import OCF.Align.CrossMNode using (C; νT; ly; val-next)
open import OCF.Align.CrossMInst using (𝒯; val≼T)
open import OCF.Align.TLOneThm using (below-chain)

ofL-mono : ∀ {a b} → L._≼_ a b → V._≼_ (ofL a) (ofL b)
ofL-mono L.z≼ = V.z≼
ofL-mono (L.s≼ p) = V.s≼s (ofL-mono p)
ofL-mono (L.s≼ʳ p) = V.≼-suc (ofL-mono p)
ofL-mono (L.l≼ h) = V.l≼ (λ n → ofL-mono (h n))
ofL-mono (L.l≼ʳ n p) = V.≼l n (ofL-mono p)

reflect : ∀ (a b : Ordᶜ zero) (ha : HS a) (hb : HS b) →
  L._≼_ (toLevel a ha) (toLevel b hb) → V._≼_ a b
reflect a b ha hb p = V.≼-trans (V.≅→≼ (≅-sym (ofL-lvl a ha)))
  (V.≼-trans (ofL-mono p) (V.≅→≼ (ofL-lvl b hb)))

height-row : ∀ M (a : Ordᶜ zero) (ha : HS a) →
  L._≼_ (toLevel a ha) (val M) → V._≼_ a (forceᴺ _ (Gᵖ M end zero))
height-row M a ha p = reflect a (forceᴺ _ (Gᵖ M end zero)) ha
  (forceᴺ-HS _ (Gᵖ M end zero)) (L.≼-trans p (val≼T M))

height-chain : ∀ M₀ n (a : Ordᶜ zero) (ha : HS a) →
  L._≼_ (toLevel a ha) (val (C 𝒯 M₀ n)) → V._≼_ a (νT 𝒯 M₀)
height-chain M₀ n a ha p = V.≼-trans (height-row (C 𝒯 M₀ n) a ha p)
  (V.≺→≼ (V.≺→s≼ (below-chain M₀ n end)))

feedback-premise : ∀ M₀ n →
  L._≼_ (lvG (Gᵖ (C 𝒯 M₀ n) end zero)) (val (C 𝒯 M₀ (suc n)))
feedback-premise M₀ n = val-next (C 𝒯 M₀ n) (ly 𝒯 (C 𝒯 M₀ n))

feedback-instance : ∀ M₀ n →
  V._≼_ (forceᴺ _ (Gᵖ (C 𝒯 M₀ n) end zero)) (νT 𝒯 M₀)
feedback-instance M₀ n = height-chain M₀ (suc n)
  (forceᴺ _ (Gᵖ (C 𝒯 M₀ n) end zero))
  (forceᴺ-HS _ (Gᵖ (C 𝒯 M₀ n) end zero)) (feedback-premise M₀ n)
```
