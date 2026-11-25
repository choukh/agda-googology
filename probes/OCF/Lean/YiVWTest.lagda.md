# 新主线 FGH 的有限求值
> 验收文件。有限测试，来源：`YiLPFGH.test₀`，闭项换成新主线 `EBOᶻ`。
> 仅检查参数 0 的求值；不作序数强度或增长率结论。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVWTest where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiVWFGH using (fghᶻ)

test₀ : fghᶻ 0 ≡ 0
test₀ = refl
```
