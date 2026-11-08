# 原全高度地板的合法证运输实例

这不是完整CanonicalProofTransport的实例；它实填该接口在原全部
pointFloor上的字段，包含非有限高度。搬运后旧Ω与目标旧Ω的等价
用原tr⁻-≅和Ω-≅证明，原树与其地板未改。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofActual where
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read)
open import OCF.Align.GeneralOmegaCountableTypedProofIf

floor-transport : ∀ B l₁ l₂ →
  Read B l₁ (canonical B l₁)
    (L.tr⁻ (proof-shape B l₁ l₂) (L.Ω (height B l₂))) (pointFloor B)
floor-transport B l₁ l₂ = rc
  (L.tr⁻-≅ (proof-shape B l₁ l₂)
    (L.Ω-≅ (L.≅ᴵ-sym (proof-shape B l₁ l₂))))
  (floor-read B l₁)

omega-transport : Read omega omega-legal (canonical omega omega-legal)
  (L.tr⁻ (proof-shape omega omega-legal omega-legal)
    (L.Ω (height omega omega-legal))) (pointFloor omega)
omega-transport = floor-transport omega omega-legal omega-legal
```
