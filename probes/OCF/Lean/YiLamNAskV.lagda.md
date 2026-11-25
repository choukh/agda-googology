# `Tw 3` 问到极限目标: 值的形式

验收文件. 编译定理 `asked : NA.read NJ ≼ NA.read (Tw 3)`: [YiLamNAsk](YiLamNAsk.lagda.md) 的结点 `NJ` (链用极限目标 `J` 上的 `dfin`) 的值不高于 `Tw 3`. 由 `◁→≼` (第一位置与右加数不增值) 得到.
不陈述丢掉的值有多少.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNAskV where

open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R)
open import OCF.Lean.YiLamFold using (Tw)
open import OCF.Lean.YiLamNAsk using (_◁_; here; inLim; inPlus; NJ; asked◁)
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)

◁→≼ : ∀ {a b} → a ◁ b → NA.read a ≼ NA.read b
◁→≼ {a} here = ≼-refl (NA.read a)
◁→≼ (inLim n q) = ≼l n (◁→≼ q)
◁→≼ (inPlus p b q) = NA.plus≽ p b (◁→≼ q)

asked : NA.read NJ ≼ NA.read (Tw 3)
asked = ◁→≼ asked◁
```
