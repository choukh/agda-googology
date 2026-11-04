# 折叠要的定义域接口

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). 与 [LevelFixX](LevelFixX.lagda.md) 的差别: `bound` 读同一个纤维里的证据树 (`Fᵉ`), 不读 `D` 上的地板; 没有 `bot` (空表没有项); `⊑-tr` 被 `Tp.gr` 取代; `self<G` 进了 `Dom` (`self<ᵉ`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoKX where

open import Data.Nat using (ℕ)
open import OCF.Align.LevelNoKLv

record XU : Set₁ where
  field
    𝔻 : Dom
  open Dom 𝔻
  open Lv 𝔻 using (LG; Fᵉ; Tp)
  field
    bound  : ∀ {c X K₀} (F : c ⊑ᴰ X) (ψ : Fᵉ F) {e₀ : c ⊑ᴰ K₀} → e₀ <ᵉ F → Tp F ψ
    ix     : D → ℕ
    nodeC  : ℕ → D
    nodeF  : ℕ → LG
    emᵈ    : D → LG
```
