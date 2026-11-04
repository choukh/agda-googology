# 折叠要的定义域接口

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). 与 [DomFoldDom](DomFoldDom.lagda.md) 的 `DomX` 差两处: 去掉折叠不读的 `ht`, `base`; `self<` 带守卫证据 (`self<G`). 守卫里有 "$\eta$ 合法", 而 $\eta$ 本身不带证据, 所以 $\eta<\eta+1$ 只在过了守卫时才成立.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixX where

open import Data.Nat using (ℕ)
open import OCF.Align.GuardTightLv
open import OCF.Align.DomFoldDom using (module FlrOf)

record XU : Set₁ where
  field
    𝔻 : Dom
  open Dom 𝔻
  open FlrOf 𝔻
  open Lv 𝔻 using (LG)
  field
    ⊑-tr   : ∀ {a b c} → a ⊑ᴰ b → b ⊑ᴰ c → a ⊑ᴰ c
    self<G : ∀ {c η} → c ⊑ᴰ η → η <ᴰ sD η
    bound  : ∀ {ℓ K₀} (φ : Flr) → Ev ℓ φ → K₀ <ᴰ ℓ → Tp ℓ φ
    ix     : D → ℕ
    nodeC  : ℕ → D
    nodeF  : ℕ → LG
    emᵈ    : D → LG
    bot    : D
```
