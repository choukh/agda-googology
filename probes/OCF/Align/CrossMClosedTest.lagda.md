# 跨段: 闭项的有限测试

> 入口 [CrossM](CrossM.lagda.md). **有限测试, 不是证明.** 只在几个输入上算值. 比较器是 `refl`; 盲区: 这些小值不区分强度.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMClosedTest where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up)
open import OCF.Align.CrossMClosed

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl
sh _       = sz

_ : sh T⊤ ≡ sl
_ = refl

_ : fgh⊤ 0 ≡ 1
_ = refl
```
