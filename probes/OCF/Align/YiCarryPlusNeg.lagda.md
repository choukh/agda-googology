# Carry⁺：排除冻结 K2′ 的旧反例源

YiCarryNeg.no-K2′ 使用的同一个源仍保留原 Carry、Legal、Reg
及原守卫起点；本篇只编译证明它不能带 Carry⁺。失败字段精确为
根下界的 Nested，不否定 Carry⁺ 的规范全塔或 Λ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryPlusNeg where

open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₂)
open import OCF.Align.YiCarryPlus
import OCF.Align.YiCarryNeg as N

no-old-source-carry⁺ : Carry⁺ N.bad-source → ⊥
no-old-source-carry⁺ r = N.no-bad-coordinate-nested (proj₂ (lower⁺ r))
```

编译否定的目标就是新增证书本身，无其它背景假设。旧源的各项原
前提均由 N.source-carry、N.source-legal、N.original-start 实填。
本结论只说明旧反例被增补域排除，不推出 PsiRows⁺ 或 K2′⁺ 可满足。
有限测试无；没有比较器、值界、折叠或新树字段。
