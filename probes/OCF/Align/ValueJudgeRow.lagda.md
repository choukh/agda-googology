# 值判据 (六): 塔的行, 判据的陈述

> **判决: HOLDS (只有定义).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 对高度结构 `HtS` 参数化, 不含记号.
>
> `Rows W`: 函数 $W:\mathrm{Ht}\times\mathrm{Ord}^I\to$ 树, 满足严格递增, 极限连续, 同余, 链行, 闭包行的下界. **这是判据的定义, 里面没有折叠, 没有证书, 没有记号**, 只有结构 `HtS`. `V-rows`: 证书的计值满足它, 对一切结构. 它是相对的: 第 0 行和后继行的具体数值由别的东西给 (`rows-blind`, [ValueJudgeRowNeg](ValueJudgeRowNeg.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.ValueJudgeRow (𝕊 : HtS) where

open HtS 𝕊
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import OCF.Free.Level
open import OCF.Align.ValueJudgeBase
open import OCF.Align.ValueJudgeFix

record Rows (W : Ht → Ordᴵ → Ordᶜ zero) : Set where
  field
    r-cong   : ∀ m {a b} → a ≅ᴵ b → W m a ≈ᵛ W m b
    r-strict : ∀ m a → W m a ≺ᵛ W m (suc a)
    r-limit  : ∀ m f s → W m (lim f s) ≈ᵛ lim (λ n → W m (f n))
    r-chain  : ∀ m F (qq : ∀ i → F i <ᴸ m) → view m ≡ chain F qq → W m zero ≈ᵛ lim (λ i → W (F i) zero)
    r-clos   : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → W n zero ≺ᵛ W m zero
open Rows public
```
