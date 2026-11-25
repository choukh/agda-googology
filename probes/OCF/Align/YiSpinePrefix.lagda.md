# 字面前缀 Ω：只检查本轮指定反例的修补

不改既有 Ω，在新文件定义 x ⊞ Ω_x。合法性随加法与原 Ω 给出；
字面前缀的定位对所有输入成立。本轮只将其用于指定的一个比较对，
不据此宣称全部实际比较、ψ 或 S3 已经闭合。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpinePrefix where

import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open import OCF.Align.LevelFixVal using (CP)
open import OCF.Align.YiLevelBase using (Level; level; tree; legal; Ω)

add : Level → Level → Level
add x y = level (V._+ᴸ_ (tree x) (tree y))
  (V.Legal-add (tree x) (tree y) (legal x) (legal y))

first : ∀ x y → CP x (V._+ᴸ_ x y)
first x F.zero = V.self
first x (F.suc y) = V.suc (first x y)
first x (F.lim f) = V.lim 0 (first x (f 0))
first x (F.lc k c t g) = V.fst (first x t)

Ωprefix : Level → Level
Ωprefix x = add x (Ω x)

prefix-position : ∀ x → CP (tree x) (tree (Ωprefix x))
prefix-position x = first (tree x) (tree (Ω x))
```

这里没有给加法新增全域单调律，没有改变原层号合法性或分支域。
一般的 Ω 位置保持、极限相邻位置及值对应均不由这条前缀定位定理自动推出。
