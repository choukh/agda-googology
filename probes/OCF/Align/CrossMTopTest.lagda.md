# 跨段: 数据树闭项的有限测试

> 入口 [CrossM](CrossM.lagda.md). **有限测试, 不是证明.** 比较器是 `refl` 看头部形状; 盲区: 不看界, 不看值 (`noCert₂` 的教训: 种类全过也不算证据). 这里只说明 `Tᵀ` 算得动, 头部的形状与 [CrossMAccept](CrossMAccept.lagda.md) 里记号的 `cof` 同类: $\alpha=0$ 是闭包节点, $\alpha=1$ 是 ℕ-极限, 它的前两项是闭包节点.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMTopTest where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (Ordᴵ; zero; suc)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdPos using (cz)
open import OCF.Align.CrossMTop

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

data Sh : Set where
  sz ss sl sc : Sh

sh : Z → Sh
sh Z.zero = sz
sh (Z.suc _) = ss
sh (Z.lim _) = sl
sh (Z.ĉᴸ _ _ _ _ _) = sc

fs : Z → ℕ → Z
fs (Z.lim f) n = f n
fs x n = x

Z₀ Z₁ : Z
Z₀ = toZ (Tᵀ cz zero ev₀ zero)
Z₁ = toZ (Tᵀ cz (suc zero) ev₀ zero)

_ : sh Z₀ ≡ sc
_ = refl

_ : sh Z₁ ≡ sl
_ = refl

_ : sh (fs Z₁ 0) ≡ sc
_ = refl

_ : sh (fs Z₁ 1) ≡ sc
_ = refl
```
