# LamIso 测试: `TI` 与 `TVs`, 全有损 `TL` (有限测试)

> 测试文件, 不进成品. 全文 `--safe --without-K --lossy-unification`. `TL`, `sz′` 取自 [LeanFbTest](LeanFbTest.lagda.md) (有界展开的结点数).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIsoTest where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanFbTest using (TL; sz′)
open import OCF.Lean.LamIsoTm using (TI)
```

**有限测试 (不是证明).** 有界展开 $k=7$ 的结点数与 `TVs`, `TL` 相同 (7238): 这一深度看不见回灌与新的最高层的差 (`Ωd Λ′` 的前几步与 `Ωd ΛF` 同形). $k=9$ 的 `sz′ 9 TI ≡ sz′ 9 TVs` 在 300 秒内没有算完 (被 `timeout` 杀掉, 不是结论).

```agda
sz-7I : sz′ 7 TI ≡ 7238
sz-7I = refl
```
