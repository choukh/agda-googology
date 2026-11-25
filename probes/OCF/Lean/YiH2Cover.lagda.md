# 带高度族：后继截面的精确覆盖
非验收文件；编译定理：`covers-iff` 对任意第 0 层参照树给出原累加链下界的充要条件，不要求参照树带 `HS`。
每个后继截面须被某个实际链高度读回覆盖；`covered-branch` 由旧 `branch-cover` 实填，`height-on-HS` 接旧严格值界充要条件。
证明复用 `YiHFHeight.ofL-mono/feedback-premise` 与 `YiHGHeight`；不改原树、折叠、合法性，不声称新增序数站。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiH2Cover where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import OCF.Free.Level using (Ordᶜ; zero; suc; lim; HS; toLevel; _≅_; ≅-sym)
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Align.LadderOrdPos using (Code; end; val)
open import OCF.Align.LadderOrdCert using (Gᵖ)
open import OCF.Align.CrossMNode using (C; νT)
open import OCF.Align.CrossMInst using (𝒯; val≼T)
open import OCF.Align.CrossNextSum using (ofL; ofL-lvl)
open import OCF.Lean.YiHFHeight using (ofL-mono; feedback-premise)
open import OCF.Lean.YiHGHeight using (branch-cover; height-iff-strict)
import OCF.Align.LadderOrdCode as L
import OCF.Align.ValueJudgeBase as V

height≤branch : ∀ M → V._≼_ (ofL (val M)) (forceᴺ _ (Gᵖ M end zero))
height≤branch M = V.≼-trans (ofL-mono (val≼T M))
  (V.≅→≼ (ofL-lvl (forceᴺ _ (Gᵖ M end zero)) (forceᴺ-HS _ (Gᵖ M end zero))))

branch≤height : ∀ M n → V._≼_ (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))
  (ofL (val (C 𝒯 M (Data.Nat.suc n))))
branch≤height M n = V.≼-trans
  (V.≅→≼ (≅-sym (ofL-lvl (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))
    (forceᴺ-HS _ (Gᵖ (C 𝒯 M n) end zero)))))
  (ofL-mono (feedback-premise M n))

Height : Code → Ordᶜ zero → Set
Height M a = Σ ℕ λ n → V._≼_ (suc a) (ofL (val (C 𝒯 M n)))

height-from-strict : ∀ M a → V._≼_ (suc a) (νT 𝒯 M) → Height M a
height-from-strict M a p = go (V.≼lim⁻ p)
  where
  go : (Σ ℕ λ n → V._≼_ (suc a) (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))) → Height M a
  go (n , q) = Data.Nat.suc n , V.≼-trans q (branch≤height M n)

height-to-strict : ∀ M a → Height M a → V._≼_ (suc a) (νT 𝒯 M)
height-to-strict M a (n , p) = V.≼l n (V.≼-trans p (height≤branch (C 𝒯 M n)))

Covers : Code → Ordᶜ zero → Set
Covers M zero = ⊤
Covers M (suc a) = Height M a
Covers M (lim f) = ∀ n → Covers M (f n)
Covers M (OCF.Free.Level.limᵢ () f)
Covers M (OCF.Free.Level.up () x)

covers-from : ∀ M a → V._≼_ a (νT 𝒯 M) → Covers M a
covers-from M zero p = tt
covers-from M (suc a) p = height-from-strict M a p
covers-from M (lim f) p = λ n → covers-from M (f n)
  (V.≼-trans (V.≼l n (V.≼-refl (f n))) p)
covers-from M (OCF.Free.Level.limᵢ () f) p
covers-from M (OCF.Free.Level.up () x) p

covers-to : ∀ M a → Covers M a → V._≼_ a (νT 𝒯 M)
covers-to M zero p = V.z≼
covers-to M (suc a) p = height-to-strict M a p
covers-to M (lim f) p = V.l≼ (λ n → covers-to M (f n) (p n))
covers-to M (OCF.Free.Level.limᵢ () f) p
covers-to M (OCF.Free.Level.up () x) p

covers-iff : ∀ M a → (V._≼_ a (νT 𝒯 M) → Covers M a) ×
  (Covers M a → V._≼_ a (νT 𝒯 M))
covers-iff M a = covers-from M a , covers-to M a

covered-branch : ∀ M n → Covers M (suc (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero)))
covered-branch M n = proj₁ (branch-cover M n) ,
  V.≼-trans
    (V.≅→≼ (OCF.Free.Level.s≅ (≅-sym (ofL-lvl
       (forceᴺ _ (Gᵖ (C 𝒯 M n) end zero))
       (forceᴺ-HS _ (Gᵖ (C 𝒯 M n) end zero))))))
    (ofL-mono (proj₂ (branch-cover M n)))

height-on-HS : ∀ M a (ha : HS a) →
  (Height M a → Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))) ×
  ((Σ ℕ λ n → L._≼_ (suc (toLevel a ha)) (val (C 𝒯 M n))) → Height M a)
height-on-HS M a ha =
  (λ p → proj₁ (height-iff-strict M a ha) (height-to-strict M a p)) ,
  (λ p → height-from-strict M a (proj₂ (height-iff-strict M a ha) p))
```
