# 值验收: 链行第 0 项的三种处理

> 入口 [EmbVV](EmbVV.lagda.md). 不读记号. `keep`: 主线的写法. `drop`: 去掉第 0 项, 错开一位. `repl n q`: 第 0 项换成高度 $n$ 的行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.EmbVVMode (𝕊 : HtB) where

data HdM (m : HtB.Ht 𝕊) : Set where
  keep : HdM m
  drop : HdM m
  repl : ∀ n → HtB._<ᴸ_ 𝕊 n m → HdM m
```
