# 种类结构的对应 (四): 有限测试

> 不含记号. 入口 [HtTowerN](HtTowerN.lagda.md). **有限测试, 不是证明.** 比较器是 [HtTowerFTest](HtTowerFTest.lagda.md) 的 `same d 2`.
>
> | 比较 | 结果 |
> |---|---|
> | `T-fb₂ 1` 对 `T-Ω₂²` | 深度 9 同, 10 不同 |
> | `T-Ω₂` 对 `T-fb₂ 1` | 深度 9 同, 10 不同 |
> | `T-fb₂ 2` 对 `T-fb₂ω` | 深度 4 同, 5 不同 |
> | `T-fb₂ 1` 对 `T-fb₂ 2` | 深度 12 同 (比较器在这里没有分辨力, 同 `HtOutTest` 对 `T-fb 1`, `T-fb 2` 的那一行) |
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerNTest where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerFTest using (same)
open import OCF.Align.HtTowerFClosed using (T-Ω₂; T-Ω₂²)
open import OCF.Align.HtTowerNFb using (T-fb₂; T-fb₂ω)

a9 : same 9 2 (T-fb₂ 1) T-Ω₂² ≡ true
a9 = refl

a10 : same 10 2 (T-fb₂ 1) T-Ω₂² ≡ false
a10 = refl

b9 : same 9 2 T-Ω₂ (T-fb₂ 1) ≡ true
b9 = refl

b10 : same 10 2 T-Ω₂ (T-fb₂ 1) ≡ false
b10 = refl

c4 : same 4 2 (T-fb₂ 2) T-fb₂ω ≡ true
c4 = refl

c5 : same 5 2 (T-fb₂ 2) T-fb₂ω ≡ false
c5 = refl

d12 : same 12 2 (T-fb₂ 1) (T-fb₂ 2) ≡ true
d12 = refl
```
