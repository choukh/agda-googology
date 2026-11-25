# YiPE 陈述：主线链点层号的前驱嵌入推出 BTBO 下界

**验收文件，档位：编译定理与条件定理。** `EmbTⁿ`：参照对角链第 n 项的层号 `D.L n` 的前驱保序嵌进主线某个链点的层号 `κ m`。`btbo-embⁿ : EmbTⁿ → D.BTBOᴵ ≼ read T₃` (由 `Ψ-emb` 与 `T₃-own`，只用下界)，`btbo-emb⁺` 接到下一站的 `T⁺`。
n = 0, 1 的实例是无条件定理 (`emb₀ⁿ`；`emb₁ⁿ` 由 `YiChainOne.chainP₁` 经 `embᵖ`)。一般的 n 在 [YiPEStep](YiPEStep.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPEBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanTw3 using (T₃; pts; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (κ; T₃-own; HS-read)
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiLeanTw3 as MT
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValFin using (T₃≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; l≼; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-⊑)
open import OCF.Align.YiVmConExact using (embᵖ)
open import OCF.Lean.YiChainOne using (chainP₁)
```

## 1 约化

```agda
EmbTⁿ : Set
EmbTⁿ = ∀ n → Σ ℕ λ m → PEmb (D.L n) (κ m)

btbo-embⁿ : EmbTⁿ → D.BTBOᴵ ≼ read T₃
btbo-embⁿ e = l≼ (λ n → ≼-trans (Ψ-emb (proj₂ (e n))) (T₃-own (proj₁ (e n))))

btbo-emb⁺ : EmbTⁿ → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo-emb⁺ e = ≼-trans (≼-trans (btbo-embⁿ e) (≅→≼ T₃≅)) NA.T₃≼T⁺
```

## 2 前两项

```agda
emb₀ⁿ : Σ ℕ λ m → PEmb (D.L 0) (κ m)
emb₀ⁿ = 0 , PEmb-⊑ L.⊑ᴵ-refl

emb₁ⁿ : Σ ℕ λ m → PEmb (D.L 1) (κ m)
emb₁ⁿ = proj₁ chainP₁ ,
  embᵖ (D.γ 1) (D.cert 1) (read (co (pts (proj₁ chainP₁)))) (HS-read _ (lw (pts (proj₁ chainP₁)))) (proj₂ chainP₁)
```
