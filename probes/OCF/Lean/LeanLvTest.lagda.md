# LeanLv 测试: `TVs` 与同一折叠全有损的 `TL` (有限测试)

> 测试文件, 不进成品. 全文 `--safe --without-K --lossy-unification`. `TL`, `sz′` 取自 [LeanFbTest](LeanFbTest.lagda.md) (同一个 `T = SLs`, 同一个最高层 `ΛF`, 同一个底种类, 级回灌参数一切有损).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLvTest where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanFbTest using (TL; sz′)
open import OCF.Lean.LeanLvTmS using (TVs)
```

**有限测试 (不是证明).** 有界展开的结点数 ($k\le7$) 在 `TVs` 与 `TL` 上相同 (都是 `LeanFbTest` 的 7238): 在这一深度上看不见回灌 (回灌行在 `exec-TVs2` 的路径上, 离根 11 步).

```agda
sz-7V : sz′ 7 TVs ≡ 7238
sz-7V = refl
```
