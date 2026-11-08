# 消费实际via层同构的读回运输

规范运输已实填，实际旧派发的via证明不必等于规范proof-shape。
只在旧Ordᶜ上用已有≅闭包替换搬运结果；native坐标保持原对象。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofVia where
open import OCF.Lean.CRwBase
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (self; coord-self; coord-cong)
open import OCF.Align.GeneralOmegaCountableTypedProofIf
open import OCF.Align.GeneralOmegaCountableTypedProofRestrict
open import OCF.Align.GeneralOmegaCountableTypedProofRun

transport-via : ∀ B l₁ l₂ (e : height B l₁ L.≅ᴵ height B l₂) {x c} →
  Read B l₂ (canonical B l₂) x c →
  Read B l₁ (canonical B l₁) (L.tr⁻ e x) c
transport-via B l₁ l₂ e r = rc
  (L.≅-trans (L.tr⁻-≅ e (self r))
    (L.≅-sym (L.tr⁻-≅ (proof-shape B l₁ l₂) (self r))))
  (transport B l₁ l₂ r)

coordinate-via : ∀ B l₁ l₂ κ (e : rank B l₁ κ L.≅ᴵ rank B l₂ κ) {x c} →
  Coord B l₂ κ x c → Coord B l₁ κ (L.tr⁻ e x) c
coordinate-via B l₁ l₂ κ e r = coord-cong B l₁ κ
  (L.≅-trans (L.tr⁻-≅ e (coord-self B l₂ κ r))
    (L.≅-sym (L.tr⁻-≅ (rank-shape B l₁ l₂ κ) (coord-self B l₂ κ r))))
  (coordinate B l₁ l₂ κ r)
```

这允许真实via同构保持不变，不要求其证明相等。它仍要求同一个
native B或同一native种类；跨不同raw秩的识别须由同界分类另证。
