# 序数高度: 跨世界的第 0 行对齐

> **判决: HOLDS (只有声明).** 结论写在 [LadderOrd](LadderOrd.lagda.md). `RowEq` 说右边第 0 行的写法与左边一致. 由 `Survey/scripts/ladderord/mk_cross.py` 写出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdCrossEq (𝕊 : HtS) (𝔹 : HtB) (e : HtS.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtS._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m)) where

open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.LadderInfTree
import OCF.Align.LadderOrdTree
module N = OCF.Align.LadderInfTree 𝕊
module I = OCF.Align.LadderOrdTree 𝔹

RowEq : ∀ m → View N._<ᴸ_ N.h₀ m → Set
RowEq m base = I.rowV (e m) (I.ΩI (e m)) (I.view (e m)) ≡ I.rowB {e m}
RowEq m (clos q) = I.view (e m) ≡ clos (ε q)
RowEq m (chain F qs) = I.view (e m) ≡ chain (λ i → e (F i)) (λ i → ε (qs i))
```
