> **机械克隆, 验收用.** 由 `LadderNFWBase` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

# 标签世界的名字表 (Base)

> 验收用. 把 `OCF.Free.Base` 的名字指向标签阶梯世界的原定义. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZNFWBase where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Align.Level
open import OCF.Align.LadderLabZUniform3Base using (∅ᴿ)
open import OCF.Align.LadderLabZNFWEq using (_≈ᴿ_; Ωˢ-≅)

clash : ∀ {i j} → j ≺ᴵ i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ⊥
clash s (inj₁ t) = ≺ᴵ-irrefl (≺ᴵ-trans s t)
clash s (inj₂ c) = ≺ᴵ-irrefl (≺ᴵ-respʳ s c)

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei
```
