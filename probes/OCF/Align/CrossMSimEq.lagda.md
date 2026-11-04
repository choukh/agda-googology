# 跨段: 第 0 行对齐

> **判决: HOLDS (只有声明).** 入口 [CrossM](CrossM.lagda.md). `RowEq` 说右边第 0 行的写法与左边一致. 仿 [LadderOrdCrossEq](LadderOrdCrossEq.lagda.md); 链行的证明项不要求字面相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.CrossMSimEq (𝕊 : HtB) (𝔹 : HtB) (e : HtB.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtB._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m)) where

open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.LadderOrdTree
module N = OCF.Align.LadderOrdTree 𝕊
module I = OCF.Align.LadderOrdTree 𝔹

RowEq : ∀ m → View N._<ᴸ_ N.h₀ m → Set
RowEq m base = I.rowV (e m) (I.ΩI (e m)) (I.view (e m)) ≡ I.rowB {e m}
RowEq m (clos q) = I.view (e m) ≡ clos (ε q)
RowEq m (chain F qs) = Σ (∀ i → e (F i) I.<ᴸ e m) λ r → I.view (e m) ≡ chain (λ i → e (F i)) r
```
