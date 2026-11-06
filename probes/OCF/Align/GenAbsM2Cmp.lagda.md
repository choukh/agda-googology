# 规范形论证对树类型抽象 (八): 与 `MonoPort2Zero` 对照

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). 同样的参数下, [GenAbsM2](GenAbsM2.lagda.md) 的下标与关系与 [MonoPort2Zero](MonoPort2Zero.lagda.md) 的定义性相等 (`I≡`, `Rl≡`, `refl`); 两边的 `cong0₂` 互为对方类型的居民, 新的 `chain₂` 有原来的类型.
>
> 本文件是对照, 导入 `MonoPort2Zero` (从而导入 `MonoPortBridge`, `DValCanon`); `GenAbsM2` 本身不导入后者.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; Lg)
module OCF.Align.GenAbsM2Cmp {W : A} (lW : Lg W) where

open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (D; hz; nl; sum)
open import OCF.Align.MonoPort2Rel lW using (module P; Good; SRel)
import OCF.Align.MonoPort2Zero lW as O
import OCF.Align.GenAbsM2 lW as N
open import OCF.Align.GenAbsHtInst using (valᴴ)

I≡ : O.I ≡ N.I
I≡ = refl

Rl≡ : ∀ {i j : O.I} {V₁ V₂} (z : D hz V₁) (z′ : D hz V₂) → O.Rl i j z z′ ≡ N.Rl i j z z′
Rl≡ z z′ = refl

cong0₂ᴺ : ∀ (i j : O.I) → O.Hy i j → ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → valᴴ z ≤ valᴴ z′ → O.Rl i j z z′
cong0₂ᴺ = N.cong0₂

cong0₂ᴼ : ∀ (i j : N.I) → N.Hy i j → ∀ {W₀ W₀′} (z : D hz W₀) (z′ : D hz W₀′) → valᴴ z ≤ valᴴ z′ → N.Rl i j z z′
cong0₂ᴼ = O.cong0₂

chain₂ᴺ : ∀ (i j : O.I) (hx : O.Hy i j) (Y Y′ : P.St W) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ →
          sum b (nl (O.segs i j hx (proj₁ i) Y)) ≤ sum b′ (nl (O.segs i j hx (proj₁ j) Y′))
chain₂ᴺ = N.chain₂
```
