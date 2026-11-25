# `T⁺ʷ` 与 `TΛ` 不低于 ψ₀(Ω_Ω+Ω₂) 的参照 (无前提) (搬到收缩见证的折叠)

验收文件. [YiSyncTwo](YiSyncTwo.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitSyncTwo where

open import Data.Nat.Base using (ℕ; zero; suc)
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (Ω⊴top)
open import OCF.Lean.YiWitShpTwo using (e₂; γ₂; Sync₂; X₂′; X₂≅; X₂′≼ᶜ)
open import OCF.Lean.YiWitIntoTw3 using (T⁺ʷ≼TΛ)
open import OCF.Align.YiLvVal2 using (ℓ₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiWitSyncRel using (_⊴⁺_; ⊴→⊴⁺; ⊴⁺-+ˡ)
open import OCF.Lean.YiWitSyncFold using (fold1⁺; Fold₁ᴾ; ψ₁ᴿ-≅)
```

## 1 链上逐点

```agda
e₂-self : ∀ n → e₂ n L.≅ e₂ n
e₂-self zero = L.Ω-refl ℓ₁
e₂-self (suc n) = ψ₁ᴿ-≅ (e₂-self n)

e₂⊴γ₂ : ∀ n → e₂ n ⊴⁺ γ₂ n
e₂⊴γ₂ zero = ⊴→⊴⁺ Ω⊴top
e₂⊴γ₂ (suc n) = ⊴⁺-+ˡ (γ₂ n) (Fold₁ᴾ (e₂⊴γ₂ n) (e₂-self n))

sync₂ : Sync₂
sync₂ n = fold1⁺ (e₂⊴γ₂ n) (e₂-self n)
```

## 2 ψ₀(Ω_Ω+Ω₂)

```agda
X₂≼ʷ : S2.X₂ ≼ NA.read WF.T⁺ʷ
X₂≼ʷ = ≼-trans (≅→≼ X₂≅) (X₂′≼ᶜ sync₂)

X₂≼TΛ : S2.X₂ ≼ NA.read WF.TΛ
X₂≼TΛ = ≼-trans X₂≼ʷ T⁺ʷ≼TΛ
```
