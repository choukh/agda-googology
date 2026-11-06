# 高度由回灌生成: 有限测试

> 入口 [HtGen](HtGen.lagda.md). **有限测试, 不是证明.** 比较器 `same d w` (`CumUpAcceptF`): 深度 $d$, 宽度 $w$, 只读形状. 盲区: 不读第 $w$ 项以后, 不读深度 $d$ 以下, 不读值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtGenTest where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumUpAcceptF using (same)
import OCF.Align.SumOneClosed as O
import OCF.Align.SumHtClosed as H
open import OCF.Align.HtGenGen

-- 同一个 ψ₀(Ω_Ω), 两种写法: SumOne 的 T₀ 对 SumHt 的 T 1 0. 深度 3 就分开
a2 : same 2 2 (O.ord s₀) (H.ord (H.T 1 0)) ≡ true
a2 = refl
a3 : same 3 2 (O.ord s₀) (H.ord (H.T 1 0)) ≡ false
a3 = refl

-- 回灌的站对 ψ₀(Ω_Ω): 深度 3 分开
b3 : same 3 2 (O.ord s₁) (O.ord s₀) ≡ false
b3 = refl
c3 : same 3 2 (O.ord s₂) (O.ord s₀) ≡ false
c3 = refl

-- 回灌的站对 SumHt 的 Ω+1, Ω·2: 深度 3 相同. 比较器在这里没有分辨力:
-- s₁ (读 ψ₀(Ω_{ψ₀(Ω_Ω)})) 对 T 1 1 也相同
d3 : same 3 2 (O.ord s₂) (H.ord (H.T 1 1)) ≡ true
d3 = refl
e3 : same 3 2 (O.ord s₃) (H.ord (H.T 2 0)) ≡ true
e3 = refl
f3 : same 3 2 (O.ord s₁) (H.ord (H.T 1 1)) ≡ true
f3 = refl
```
