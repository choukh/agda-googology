# 最高层含与站层号同形的层, 否定一路 (五): 有限测试

> 测试文件, 不进成品. 全文 `--safe --without-K --lossy-unification`. 只读导入构造一路的 [LamIsoTm](LamIsoTm.lagda.md) (`TI`) 与 [LeanFbTest](LeanFbTest.lagda.md) 的有界展开 `sz′`.
>
> **有限测试 (不是证明).** 有界展开 ($k=7$) 的结点数: `TI` 是 7238, 与 `TVs`, `TF`, `TL` 相同 (`LeanLvTest.sz-7V`, `LeanFbTest`). 这一深度上看不见回灌, 测试分不出 `TI` 与全有损的 `TL`. 比较器: `sz′` (只数结点, 深度预算 7); 盲区: 回灌行离根比预算深.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoTest where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.LeanFbTest using (TL; sz′)
open import OCF.Lean.LamIsoTm using (TI)

sz-7I : sz′ 7 TI ≡ 7238
sz-7I = refl
```
