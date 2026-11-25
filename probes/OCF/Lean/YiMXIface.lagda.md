# 无标准形前提的项序出口陈述
> 验收文件（读记号）。`Mono` 是构造与否定共用的陈述；不要求标准形或可数性。
> `YiMXNote.¬Mono` 的反例两端都可数，因而只补可数性不能恢复这条陈述。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXIface where
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)

Mono : Set
Mono = ∀ {s t} → s ≤ᵀ t → (h : HC s) (h′ : HC t) → Rt h ≼ Rt h′
```
