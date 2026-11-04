# 跨段, 下一步: 有限测试

> 入口 [CrossNext](CrossNext.lagda.md). **有限测试, 不是证明.** 比较器 `refl`; 盲区: 小值不区分强度. `FS` 只为读形状. 能算出来的列在这里; 没算出来的写在入口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNextTest where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up)
open import OCF.Align.CrossNextInst

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl
sh _       = sz

FS : Ordᶜ zero → ℕ → Ordᶜ zero
FS (lim f) n = f n
FS (suc x) n = x
FS x       n = x

_ : sh T̂ᵀ ≡ sl
_ = refl

_ : sh T̃ᵀ ≡ sl
_ = refl

_ : sh T̄ᵀ ≡ sl
_ = refl

_ : fgĥ 0 ≡ 1
_ = refl

_ : fgh̃ 0 ≡ 1
_ = refl

_ : fgh̄ 0 ≡ 1
_ = refl

-- 第 0 项都是 ω
_ : sh (FS T̄ᵀ 0) ≡ sl
_ = refl

_ : sh (FS T̃ᵀ 0) ≡ sl
_ = refl

-- 修法二的第 1 项头部是极限, 修法三的第 1 项也是: 同一棵树的第 0 行, 前者顶着前缀
_ : sh (FS T̃ᵀ 1) ≡ sl
_ = refl

_ : sh (FS T̄ᵀ 1) ≡ sl
_ = refl

_ : fgh̄ 1 ≡ 2
_ = refl

_ : fgh̃ 1 ≡ 2
_ = refl

-- 毛刺: 第 1 项的第 0 项是 ω, 它的第 0 项不带前缀是 0, 带前缀是 ω+1
_ : sh (FS (FS (FS T̄ᵀ 1) 0) 0) ≡ sz
_ = refl

_ : sh (FS (FS (FS T̃ᵀ 1) 0) 0) ≡ ss
_ = refl
```
