# YiNext 基线：固定对角的闭项

**判决：编译定理，无前提；没有值定理。** 把 `T₃` 当第 0 层的坐标，`Tᵈ = F (suc T₃)`：第 `⌜ T₃ ⌝ + 1` 层的 `top` 折到第 0 层，合法 (`Tᵈ-legal`)。
它的读法按便宜增长算 (只把层号抬到 ψ₀(Ω_Ω) + 1)，不算这一站。闭项 `T₃` 在 [YiNextTop](YiNextTop.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextBaseline where

open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
open import OCF.Lean.YiNextTop using (F; lv; T₃; T₃-legal)

Tᵈ : R
Tᵈ = F (G.suc T₃) T₃-legal

Tᵈ-legal : Lgl zero Tᵈ
Tᵈ-legal = Ψ-lgl zero (lv (G.suc T₃) T₃-legal) (λ _ → fold) G.top tt

Tᵈ-form : Tᵈ ≡ G.lim (λ n → Ψ zero (lv T₃ T₃-legal) (λ _ → fold)
  (chain ⌜ T₃ ⌝ (Ψ ⌜ T₃ ⌝ (lv T₃ T₃-legal) (self ⌜ T₃ ⌝)) n))
Tᵈ-form = refl
```
