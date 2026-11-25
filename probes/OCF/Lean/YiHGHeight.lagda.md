# 带高度族：严格值界与链高度覆盖
非验收文件；编译定理：`height-iff-strict` 对任意带 `HS` 的树给出严格下界的充要条件。
`branch-cover` 实填链分支实例；复用 `YiHFHeight.height-chain`、`feedback-premise` 与 `TLOneThm.below-chain`。
不经过 `NF₁`；没有目标参照到链高度的新界，不声称新增序数站。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHGHeight where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Free.Level using (Ordᶜ; zero; suc; lim; HS; hs; hs⁻; hl₁; toLevel)
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos using (Code; end; val)
open import OCF.Align.LadderOrdCert using (Gᵖ)
open import OCF.Align.CrossMNode using (C; νT)
open import OCF.Align.CrossMInst using (𝒯)
import OCF.Align.LadderOrdCode as L
import OCF.Align.ValueJudgeBase as V
open import OCF.Align.TLOneThm using (below-chain)
open import OCF.Lean.YiHFHeight using (height-chain; feedback-premise)

level-mono : ∀ {a b : Ordᶜ zero} (ha : HS a) (hb : HS b) →
  V._≼_ a b → L._≼_ (toLevel a ha) (toLevel b hb)
level-mono ha hb V.z≼ = L.z≼
level-mono ha hb (V.s≼s p) = L.s≼ (level-mono (hs⁻ ha) (hs⁻ hb) p)
level-mono ha hb (V.≼l n p) = L.l≼ʳ n (level-mono ha (hl₁ hb n) p)
level-mono ha hb (V.l≼ h) = L.l≼ (λ n → level-mono (hl₁ ha n) hb (h n))
level-mono ha hb (V.≼i {p = ()} x ex p)
level-mono ha hb (V.i≼ {p = ()} h)
level-mono ha hb (V.≼u {r = ()} p)
level-mono ha hb (V.u≼ {r = ()} p)

strict-cover : ∀ M (a : Ordᶜ zero) (ha : HS a) →
  V._≼_ (suc a) (νT 𝒯 M) →
  Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))
strict-cover M a ha p = from (V.≼lim⁻ p)
  where
  from : (Σ ℕ λ n → V._≼_ (suc a) (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))) →
    Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))
  from (n , q) = suc n , L.≼-trans
    (level-mono (hs ha) (forceᴺ-HS _ (Gᵖ (C 𝒯 M n) end zero)) q)
    (feedback-premise M n)

cover-strict : ∀ M (a : Ordᶜ zero) (ha : HS a) →
  (Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))) →
  V._≼_ (suc a) (νT 𝒯 M)
cover-strict M a ha (n , p) = height-chain M n (suc a) (hs ha) p

branch-cover : ∀ M n →
  Σ ℕ λ k → L._≼_
    (suc (lvG (Gᵖ (C 𝒯 M n) end zero))) (val (C 𝒯 M k))
branch-cover M n = strict-cover M
  (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))
  (forceᴺ-HS _ (Gᵖ (C 𝒯 M n) end zero))
  (V.≺→s≼ (below-chain M n end))

height-iff-strict : ∀ M (a : Ordᶜ zero) (ha : HS a) →
  ((V._≼_ (suc a) (νT 𝒯 M)) →
    Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))) ×
  ((Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))) →
    V._≼_ (suc a) (νT 𝒯 M))
height-iff-strict M a ha = strict-cover M a ha , cover-strict M a ha

omega-cover : Σ ℕ λ k → L._≼_
  (suc (lvG (Gᵖ L.ωᶜ end zero))) (val (C 𝒯 L.ωᶜ k))
omega-cover = branch-cover L.ωᶜ 0
```
