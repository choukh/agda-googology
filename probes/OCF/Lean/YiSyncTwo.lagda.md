# `T⁺ʷ` 与 `TΛ` 不低于 ψ₀(Ω_Ω+Ω₂) 的参照 (无前提)

验收文件. 编译定理, 无前提: `e₂⊴γ₂ : ∀ n → e₂ n ⊴⁺ γ₂ n` (参照第 n 项在树的层号 1 的链的第 n 点之下), `sync₂ : Sync₂` (即 [YiShpTwo](YiShpTwo.lagda.md) 条件定理的前提), `X₂≼ʷ : S2.X₂ ≼ NA.read W.T⁺ʷ`, `X₂≼TΛ : S2.X₂ ≼ NA.read W.TΛ`. 参照 `S2.X₂` 读作 ψ₀(Ω_Ω+Ω₂), 读法是判断 (没有逐项一致证明, 见 `Stage2` 的 `X₂-unlabel`). 只是下界.
办法: [YiSyncRel](YiSyncRel.lagda.md) 的关系 `⊴⁺` 与 [YiSyncFold](YiSyncFold.lagda.md) 的 `Fold₁ᴾ`, `fold1⁺`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSyncTwo where

open import Data.Nat.Base using (ℕ; zero; suc)
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open NA using (Ω⊴top)
open import OCF.Lean.YiShpTwo using (e₂; γ₂; Sync₂; X₂′; X₂≅; X₂′≼ᶜ)
open import OCF.Lean.YiIntoTw3 using (T⁺ʷ≼TΛ)
open import OCF.Align.YiLvVal2 using (ℓ₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiSyncRel using (_⊴⁺_; ⊴→⊴⁺; ⊴⁺-+ˡ)
open import OCF.Lean.YiSyncFold using (fold1⁺; Fold₁ᴾ; ψ₁ᴿ-≅)
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
X₂≼ʷ : S2.X₂ ≼ NA.read W.T⁺ʷ
X₂≼ʷ = ≼-trans (≅→≼ X₂≅) (X₂′≼ᶜ sync₂)

X₂≼TΛ : S2.X₂ ≼ NA.read W.TΛ
X₂≼TΛ = ≼-trans X₂≼ʷ T⁺ʷ≼TΛ
```
